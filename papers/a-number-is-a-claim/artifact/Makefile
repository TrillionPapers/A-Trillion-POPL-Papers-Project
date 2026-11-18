# Audits the recorded versions of the first nine papers of the repository and this paper, and
# regenerates the numbers that the paper quotes.  `make check` needs python3, git with the full
# history of the repository, and pdftotext (poppler) for the check of the committed PDFs.
# `make seeds` runs the scripts of six earlier papers with other random seeds; it takes a few
# minutes and is not part of `make check`, which reads the recorded result.
.PHONY: all check seeds clean

all: check

check:
	mkdir -p out
	python3 evidence.py out > /dev/null
	diff -u expected/check.txt out/check.txt
	diff -u expected/numbers.tex out/numbers.tex
	diff -u expected/unsupported.txt out/unsupported.txt
	diff -u expected/excerpt.tex out/excerpt.tex

seeds:
	mkdir -p out
	python3 seeds.py out > /dev/null
	diff -u expected/seeds.txt out/seeds.txt
	diff -u expected/seeds.tex out/seeds.tex

clean:
	rm -rf out __pycache__
