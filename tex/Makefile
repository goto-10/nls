TEXFLAGS=-interaction=nonstopmode

nls.dvi:	nls.tex
	latex $(TEXFLAGS) $<

nls.pdf:	nls.tex
	pdflatex $(TEXFLAGS) $<

clean:
	rm -f *.aux *.log *.dvi *.pdf
