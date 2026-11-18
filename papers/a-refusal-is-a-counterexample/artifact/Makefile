# Runs the learning agent of the paper on random policies and on policies of several shapes,
# compares it with three agents that do not learn, and regenerates the numbers and the table
# rows that the paper quotes.  `make check` fails if any of them differs from the files in
# expected/, which the paper reads.  Needs python3 and nothing else.
.PHONY: all check clean

FILES = check.txt numbers.tex dialogue.tex cells.tex shapes.tex growth.tex refused.tex \
        lengths.tex alphabet.tex blocks.tex

all: check

check:
	mkdir -p out
	python3 learn.py out > /dev/null
	for f in $(FILES); do diff -u expected/$$f out/$$f || exit 1; done

clean:
	rm -rf out __pycache__
