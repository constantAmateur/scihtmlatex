"""
    htmlatex.py

    htmlatex does on-the-fly rendering of latex source in HTML documents.  It is based on mt-math
    by A.M. Kuchling (http://www.amk.ca/python/code/mt-math) which is based on eqhtml.py by 
    Kjell Magne Fauske (http://fauskes.net/nb/htmleqII/eqhtml.py).

    htmlatex is a mod_python application that, after initially rendering equations, stores them
    on the filesystem rerendering them only if they change.

    htmlatex has two main goals:  first, I wanted to avoid preprocessing; I wanted to be able to
    type the raw latex into an HTML document and be finished.  Second, I wanted the HTML/Latex
    file to remain untouched.

    There is one option:  DEBUG.  If DEBUG is set, the intermediate files are
    maintained on disk in /tmp/htmlatex -- this is the only method available for helping to
    troubleshoot latex errors.  Oddly enough, performance should theoretically *increase* if
    debug mode is on as it doesn't require repeated filesystem access to delete files.

    There used to be another option:  SANITIZE, which checked the latex source for dangerous code
    and replaces it with a 'sanitized' graphic.  I decidd that giving people the option to 
    auto-render latex code over the web that could do arbitrary things to their PC was a bad idea.
    All latex code is sanitized now.  If you want to turn it off, just comment out all of the 
    self._sanitize() calls in Equation._translateToTex().

    htmlatex used to use memcached and store the png data inline as a base64 encoded url, however
    Internet Explorer is unable to display inline urls of this type so I switched the storeage
    backend to the filesystem.

    Version: $Id: htmlatex.py 152 2006-04-16 16:05:42Z jayed $
    Copyright (C) 2006 Jay Edwards

    This program is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public License
    as published by the Free Software Foundation; either version 2
    of the License, or (at your option) any later version.
    
    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.
    
    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
"""

__author__ = "Matthew Young"
__copyright__ = "Copyright (C) 2011, Matthew Young"
__license__ = "GPLv2"
__version__ = "Alpha_2011.12.24"

from BeautifulSoup import BeautifulSoup
import os, os.path 
import tempfile, binascii
from cStringIO import StringIO
import md5

DEBUG = 0
TEMPDIR = '/tmp/htmlatex'
#IMGDIR and IMGURL must exist on the webserver
IMGDIR = '/home/sciteit/sciteit/r2/r2/public/static/htmlatex/'
IMGURL = '/static/htmlatex/'
LATEX = '/usr/bin/latex'
DVIPNG = '/usr/bin/dvipng'
# Trading size for time-to-generate is a only a good idea when using memcache
DVIPNG_FLAGS = '-T tight -D 120 -z 9 -bg Transparent -o '
TYPES = {'div':'eq', 'div':'numeq', 'div':'alignedeq', 'div':'numalignedeq', 'span':'eq', 'div':'matrix', 'div':'det'}

bad_tags = ["include", "def", "command", "loop", "repeat", "open", "toks", "output",
"input", "catcode", "name", "\\^\\^", "\\every", "\\errhelp", "\\errorstopmode",
"\\scrollmode","\\nonstopmode", "\\batchmode", "\\read", "\\write", "csname",
"\\newhelp", "\\uppercase", "\\lowercase", "\\relax", "\\aftergroup", "\\afterassignment",
"\\expandafter", "\\noexpand", "\\special"]


# Include your favourite LaTeX packages and commands here
# ------ NOTE: please leave \usepackage{preview} as the last package
# ------       it plays a role with dvipng in generating to correct
# ------       offset for inline equations
PREAMBLE = r'''
\documentclass[12pt]{article} 
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{amssymb}
\usepackage{mathrsfs}
\usepackage{gensymb}
\usepackage{preview}
\pagestyle{empty} 
\batchmode
\begin{document} 
'''

def main(data):
    """
    Get the latex source; return a raw string for the webserver to send to the client

    Take the outgoing HTML and turn it into a python object.  Search the object for the
    <div> and <span> tags that indicate latex source -- the tags we can handle are given
    in the global variable TYPES.  If there isn't anything to handle, return.  If there is, 
    process it and return a pretty string of HTML for the webserver to send to the client.
 
    Notes:  A working directory must be set via os.chdir so latex knows where to put its output
    """

    if not os.path.isdir(TEMPDIR):
        os.mkdir(TEMPDIR, 0755)
    os.chdir(TEMPDIR)
    
    if not os.path.isdir(IMGDIR):
        os.mkdir(IMGDIR, 0755)
        for i in ['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']:
            os.mkdir(IMGDIR + i, 0755)

    soup = BeautifulSoup(data)

    equations = soup.findAll(TYPES)
    if not equations:
        return data

    for equation in equations:
        key = md5.new()
        key.update(str(equation).strip())                   # Strip to minimize gratuitous differences in keys
        eq = Equation(key.hexdigest(), equation)
        equation.replaceWith(eq.contents[0])
        del(eq)

    return StringIO(soup.prettify()).getvalue()


class Equation:

    def __init__(self, key, equation):
        """
        Parameters:  key --  an md5 sum of the parsed equation node
                     equation -- the parsed equation node
        Methods:     contents -- base64 encoded PNG

        When an Equation object is initialized, it checks the filesystem
	indiciated by IMGDIR to see if a file with the same name as its
        key is stored; if the key-named file exists, an <img src> tag
        referring to the filesystem is inserted into Equation.contents.

        If it isn't found, the equation's latex source is sanitized, compiled
        to a DVI, turned into a PNG, saved to IMGDIR, and stored in 
	Equation.contents
        """
        self.key, self.contents = key, equation
        self.eqstring, self.fd = None, None
        self.texfilename, self.texfile, self.dvifile = None, None, None
        self.pngfile = IMGDIR + self.key[0] + '/' + self.key + '.png'
        self.pngurl = IMGURL + self.key[0] + '/' + self.key + '.png'
        #self.comment = "\n<!-- %s -->\n" % (self.contents.string.strip())
        self.cached = os.path.isfile(self.pngfile)
        if self.cached:
            self.contents = ['<img src="%s" />' % (self.pngurl)]
        else:
            self._addToTex()
            self._compileDVI()
            self._createPNG()
            self.contents = ['<img src="%s" />' % (self.pngurl)]
        
        
    def _addToTex(self):
        """
        Creates a Tex file, writes the preamble and the equation, closed the Tex file.
        
        Calls _translateToTex
        """
        self.fd, self.texfilename = tempfile.mkstemp(suffix='.tex', prefix='eq', dir=TEMPDIR)
        self.texfile = os.fdopen(self.fd, 'w+')
        self.texfile.write(PREAMBLE)
        self._translateToTex()
        self.texfile.write('\n' + self.eqstring + '\n')
        self.texfile.write("\n \\end{document}")
        self.texfile.close()
        return


    def _translateToTex(self):
        """
        Translates the HTML into equivalent latex.
        FIXME: This is getting a little unwieldly
        
        Calls _sanitize
        """
        if self.contents.name == 'span':
            if self.contents.attrs[0][1] == 'eq':
                self.eqstring = "$ %s $ \\newpage" % self.contents.string.strip()
                self._sanitize()
                return
            elif self.contents.attrs[0][1] == 'det':
                self.eqstring = "\\begin{equation*} \\left| \\begin{matrix} %s \\end{matrix} \\right| \\end{equation*}" % \
                self.contents.string.strip()
                return
            elif self.contents.attrs[0][1] == 'matrix':
                self.eqstring = "\\begin{equation*} \\left[ \\begin{matrix} %s \\end{matrix} \\right] \\end{equation*}" % \
                self.contents.string.strip()
                return
            if DEBUG:
                assert False, 'Unhandled span:  %s at %s' % (self.eqstring)
            return
        elif self.contents.name == 'div':
            if self.contents.attrs[0][1] == 'matrix':
                self.eqstring = "\\begin{equation*} \\left[ \\begin{matrix} %s \\end{matrix} \\right] \\end{equation*}" % \
                self.contents.string.strip()
                self._sanitize()
                return
            elif self.contents.attrs[0][1] == 'det':
                self.eqstring = "\\begin{equation*} \\left| \\begin{matrix} %s \\end{matrix} \\right| \\end{equation*}" % \
                self.contents.string.strip()
                self._sanitize()
                return
            elif self.contents.attrs[0][1] == 'alignedeq':
                self.eqstring = "\\begin{align*} %s \\end{align*}" % \
                self.contents.string.strip()
                self._sanitize()
                return
            elif self.contents.attrs[0][1] == 'numalignedeq':
                self.eqstring = "\\begin{align} %s \\end{align}" % \
                self.contents.string.strip()
                self._sanitize()
                return
            elif self.contents.attrs[0][1] == 'numeq':
                self.eqstring = "\\begin{equation} %s \\end{equation}" % \
                self.contents.string.strip()
                self._sanitize()
                return
            else:
                self.eqstring = "\\begin{equation*} %s \\end{equation*}" % \
                self.contents.string.strip()
                self._sanitize()
                return
            if DEBUG:
                assert False, 'Unhandled div:  %s at %s' % (self.eqstring)
            return


    def _sanitize(self):
        """
        Removes potentially dangerous latex code, replacing it with
        a 'LaTeX sanitized' message
        """
        for tag in bad_tags:
            if tag in self.eqstring.lower():
                self.eqstring = "$ \\mbox{\\LaTeX sanitized} $ \\newpage"
        return 


    def _compileDVI(self):
        """
        Compiles the Tex file into a DVI.  If there's an error, raise it.
        """
        os.spawnl(os.P_WAIT, LATEX, 'latex', self.texfilename)
	#Open the log file and see if anything went wrong
	f=open(self.texfilename[:-3]+'log')
	for line in f:
		if line[0]=="!":
			raise SyntaxError(line)
	f.close()
        if not DEBUG:
                os.remove(self.texfilename)
                os.remove(self.texfilename[:-3] + 'aux')
                os.remove(self.texfilename[:-3] + 'log')
        return 

    def _createPNG(self):
        """
        Runs dvipng on the DVI file.
        Encodes the original latex as an HTML comment.
        """
        self.dvifile = self.texfilename[:-3] + 'dvi'
        #os.spawnl(os.P_WAIT, DVIPNG, 'dvipng', '%s %s %s' % (DVIPNG_FLAGS, self.pngfile, self.dvifile))
        os.system('%s %s "%s" %s 2>/dev/null 1>/dev/null' % (DVIPNG, DVIPNG_FLAGS, self.pngfile, self.dvifile))
	if not DEBUG:
            os.remove(self.dvifile)
        return



