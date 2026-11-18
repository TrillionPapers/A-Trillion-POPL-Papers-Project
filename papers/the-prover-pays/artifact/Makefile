# Runs the checker of the paper on random terms, compares it with a separate evaluator, builds
# the equations of Theorem 5.1, and regenerates the numbers and the table rows that the paper
# quotes.  Needs python3 and nothing else.
.PHONY: all check clean

all: check

check:
	mkdir -p out
	python3 pays.py out > /dev/null
	for f in check.txt numbers.tex adversary.tex theorems.tex equations.tex users.tex walk.tex; do diff -u expected/$$f out/$$f || exit 1; done

clean:
	rm -rf out __pycache__
