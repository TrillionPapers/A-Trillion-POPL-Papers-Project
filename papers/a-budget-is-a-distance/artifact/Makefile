# Runs the decoder of the paper on a small example and on random automata, pushdown schemas and
# vocabularies, compares its distances and its outputs with what trying every sequence of
# tokens gives, and regenerates the numbers and the table rows that the paper quotes.
# `make check` fails if any of them differs from the files in expected/, which the paper reads.
# Needs python3 and nothing else.
.PHONY: all check clean

FILES = check.txt numbers.tex trace.tex runs.tex lists.tex

all: check

check:
	mkdir -p out
	python3 budget.py out > /dev/null
	for f in $(FILES); do diff -u expected/$$f out/$$f || exit 1; done

clean:
	rm -rf out __pycache__
