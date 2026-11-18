# Runs ten layers of an agent harness in every order, compares what the paper predicts with
# what happens, and regenerates the numbers and the table rows that the paper quotes.
# Needs python3 and nothing else.
.PHONY: all check clean

all: check

check:
	mkdir -p out
	python3 layers.py out > /dev/null
	for f in check.txt numbers.tex layers.tex survive.tex retries.tex witnesses.tex variants.tex frontier.tex; do diff -u expected/$$f out/$$f || exit 1; done

clean:
	rm -rf out __pycache__
