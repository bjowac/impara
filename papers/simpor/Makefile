MAIN = main.tex

SRC = main.tex appendix.tex db.bib

all: $(SRC)
	pdflatex $(MAIN)
	bibtex main.aux
	pdflatex $(MAIN)
	pdflatex $(MAIN)


clean: 
	rm *.fls *.make *.bbl *.blg *.d *.log *.pdf *~

