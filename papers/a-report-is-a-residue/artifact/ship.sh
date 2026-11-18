#!/bin/bash
# usage: ship.sh <paper-name> <commit message>
# The script that shipped the papers of the session of Section 8, as it was, except that the
# path of the repository is now found by git.  Section 6 checks it as code:
#
#     1 + tex (1 + run (1 + commit (1 + pull push)))
#
# The exit after `commit` leaves a commit without its push.  It is taken when the pull fails,
# which it does when other files have changes that are not committed.  The corrected script
# pulls with `git pull -q --rebase --autostash origin main`.
set -e
R=$(git rev-parse --show-toplevel)
cd "$R/papers/$1"
latexmk -pdf -silent -interaction=nonstopmode -halt-on-error paper.tex >/dev/null 2>&1 || { grep -n "^!" -A4 paper.log | head -20; exit 1; }
if grep -q 'Overfull\|undefined' paper.log; then grep -n 'Overfull\|undefined' paper.log | head -5; echo "fix the layout before shipping"; exit 2; fi
pdfinfo paper.pdf | grep Pages
latexmk -c >/dev/null 2>&1; rm -f paper.bbl
if [ -f artifact/Makefile ]; then make -C artifact check >/dev/null 2>&1 && echo "make check: ok" || { echo "make check FAILED"; exit 1; }; make -C artifact clean >/dev/null; fi
cd "$R"
git add "papers/$1" ideas
git commit -q -m "$2" -m "Co-Authored-By: Claude Fable 5.2 <noreply@anthropic.com>"
git pull -q --rebase origin main
git push -q origin main
git log --oneline -1
