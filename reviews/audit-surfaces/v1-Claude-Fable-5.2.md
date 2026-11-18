# Review of version 1

Reviewer: Claude-Fable-5.2, a second instance that the author asked for an adversarial review. It read the paper, the Lean files, and the recorded outputs of version 1, ran the proofs, and wrote its own scripts to recount the measurement. Line numbers refer to `paper.tex` and `Audit.lean` of version 1.

## Errors

1. **The "source lines" of Section 5 are mostly documentation comments.** `Measure.lean` counts whole declaration ranges, doc comments included, and neither the Method paragraph nor the threats say so. I classified every counted line for the 2,000 sampled theorems: the median audit surface drops from 1,436 lines to 378 lines that are not comments (71% comments), the signature surface from 462 to 88, and the closure from 6,241 to 3,687 (41% comments). So "three orders of magnitude" is about 2.5, and "about a third" is about a sixth (the median of closure over audit is 6.0). "At most 500 lines for 432" becomes 1,118. Fix: count lines that are not comments, or report both, and regenerate the tables, the abstract, and the conclusion.

2. **The sample is not "every 23rd theorem".** A stride of 23 gives 2,044 candidates and the cap keeps the first 2,000, so the last 1,014 names can never be drawn: all 780 theorems of the root namespace (`and_comm`, `true_and`), 195 of `Vector.*`, and 29 of `WellFounded.*`. Their median audit surface is 201 lines. "Spread over the namespaces" is false, and the medians are biased upward. Fix: take the sample at index `i*N/2000` and regenerate.

3. **`meta.yaml` claims more under `verified` than the commands check.** `make measure` compares the output of the program with `expected/measure.txt`, and nothing reads `paper.tex`. Some statements are never printed: "a line or two", "about 16 lines", "three orders", "a third". The factors 4.9, 3.3, and 2.8 are truncated, and so are the means. "The audit surfaces of the library in Figure 3" covers two of the five theorems. Fix: narrow both entries, or let the paper take its numbers from the output.

## Weaknesses

4. "Theorems about data structures show the difference most" is false for the ratio that the paragraph uses. It holds only for absolute lines.
5. The distribution has two modes. The theorems of `Std` have a median of 3,108 lines and the others 805, so the overall median reflects the mix. Report the two groups.
6. "16 lines per theorem" depends on the size of the sample. Drop it.
7. "Three consequences follow": `merge` and `replace` use only `Chk.weaken` and `mono_refs`, never audit soundness. Say "two further results".
8. "One pass computes the surface": `close` needs the axioms of the proof, which `unfoldLems` computes by inlining proofs. A chain of 17 theorems `h(i+1) := trans (lem hi) (lem hi)` gives 131,071 nodes, and the proof `p'` of Theorem 3.4 grows the same way. State this, and collect the axioms per theorem instead.
9. The prose after Corollary 4.1 exceeds `portable`. The library `L'` is unconstrained and may define a parameter of the surface. The proof still checks, but the audit surface of the theorem in `L'` gains that definition. Likewise after Theorem 4.3: clients stay checked, yet a client whose audit set contains `c` has a new surface to read.
10. Section 3.4 calls skipping bodies "sound by Theorem 3.4", including a surface where no body is read. Section 3.3 shows that skipping `flip` under an axiom is unsafe. Restrict subjects to definitions that are not under axioms and drop "sound".
11. The "audit surface" of Section 5 is not the notion of the calculus. Lean definitions embed proofs, and the measured surface keeps theorems by type only, so it is not self-contained. The analogue of Theorem 3.4 needs restating, not only proving.
12. The introduction says the advice to read the statement leaves out the definitions and attributes the advice to Pollack. Pollack and Adams already ask for the definitions under the statement. Confidence 70%.

## Minor points

- "Decides" and "decision procedure": only soundness is proved.
- "Signature surface" is used before Section 5 defines it, "transparent and sealed" is never defined, the concatenation `L_0, L_1` is undefined, and "uses" is direct in Lemma 2.1 and transitive in Section 3.1.
- "Needed in the following sense" never states the sense. The examples are existential, and the surface is not minimal for derivability.
- Lean4Lean is not yet a verified kernel (confidence 75%).
- The citation of Church and Rosser covers beta. Say that delta reduces to it by definition elimination.
- The Method paragraph omits that a projection brings its structure, a literal its type, and an inductive type its mutual block. The surfaces exclude the theorem itself, and the closure includes it.
- The Lean comment at the last example says that normal forms differ. The example shows that one proof is rejected.

## No problem found

- Correspondence: Lemma 2.1 through Theorem 4.3 match their Lean declarations in hypotheses and conclusions, the proof outline matches `lemma_elim` and `def_elim`, and there is no `sorry`.
- The model: `Chk`, `WF`, and `Fresh` are adequate, and the hypotheses of `merge` and `replace` are satisfiable.
- Figure 3 agrees with `Audit.Example` in terms, indices, proofs, and both audit surfaces.
- Section 3.3: the normal forms and the claims of underivability hold.
- Every number in the tables, the abstract, and the Results paragraph equals the recorded output, and an independent recount of all 2,000 line totals agrees.
- Section 6 and the related work are otherwise accurate as far as I know (85%).
- All references resolve to the cited works.
