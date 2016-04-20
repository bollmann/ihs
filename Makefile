all: report.tex refs.bib
	pdflatex -shell-escape $^
	bibtex report
	pdflatex -shell-escape $^
	pdflatex -shell-escape $^

report.tex: report.lhs
	lhs2TeX --verb $^ -o $@

clean:
	rm -rf report.tex report.pdf *.aux *~ *.log *.ptb *.blg *.bbl
