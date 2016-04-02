all: report.tex
	pdflatex -shell-escape $^
	bibtex report.tex
	pdflatex -shell-escape $^
	pdflatex -shell-escape $^

report.tex: report.lhs
	lhs2TeX $^ -o $@

clean:
	rm -rf report.tex report.pdf *.aux *~ *.log *.ptb
