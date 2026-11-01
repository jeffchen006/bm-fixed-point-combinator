# No fixed-point combinator from B and M, even up to βη-conversion

**Author:** Zhiyang Chen

**DOI:** [10.5281/zenodo.23854830](https://doi.org/10.5281/zenodo.23854830)

> **Status: preprint, assisted by AI, not peer reviewed.**
> This work was directed by the author and assisted by AI systems, which were used for proof development, the Lean formalization, drafting and review.
> The Lean proof is checked by the Lean kernel. The written proof has not been independently checked by a human.
> The reviews by AI systems are not independent confirmation. Do not cite this result as an established theorem.

## Result

No applicative combination of `B`, `M` and `I` is a fixed-point combinator. This holds at weak equality, at `=β` and at `=βη`. The result is stronger: for each `q ≥ 1`, `Yx ≠βη x^q(Yx)`. This gives a negative answer to Problem 4 of the [TLCA List of Open Problems](https://tlca.di.unito.it/opltlca/), on these readings of that question.

The main Lean theorem:

```lean
theorem TBeta.no_fix_xr (e : Bool) (t : Tree) (ht : t.over [.B, .M, .I] = true)
    {r : Nat} (hr : 1 ≤ r) : ¬ Conv e (.app (Y t) .x) (xp r (.app (Y t) .x))
```

`e = false` is `=β` and `e = true` is `=βη`. The kernel reports only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Credit

Imamura's preprints gave the negative answer at weak equality first, and they contain the trace, the growth lemma and the final arithmetic for the term `T`. Statman has the polynomial form, the first letter `M`, the balance condition and the list rule for the first `x`. Section "Related work" of the paper gives the details and the limits of our literature check.

## Files

| Path | Content |
|---|---|
| `paper/paper.pdf` | The paper, 18 pages |
| `paper/paper.tex` | Its source. To compile it, you need the `lipics-v2021` class from CTAN |
| `lean/min2/` | The Lean 4 proof, unpacked. Read its `README.md` first |
| `lean/min2_final5.tar.gz` | The same release as the archive that the paper names |

SHA-256 of the archive: `70d869915b1294807708ba0835bc73cc8ffa9dc35ed74276a53dcadf2443acab`

## Check the proof

You need [elan](https://github.com/leanprover/elan) and `python3`. The Lean version is 4.33.1, and there is no external library.

```bash
cd lean/min2 && bash scripts/check.sh
```

The last line must be `CHECK PASSED`. The script builds from empty, runs `leanchecker` on all modules, and prints the axioms.

To read the theorem, read the definitions in `LeanJudge/Defs.lean`. You do not need to read the proofs. `lean/min2/TABLE.md` maps each statement of the paper to its Lean name.

## Known limits

- All checks ran on one machine with one toolchain. There is no independent replay yet.
- Open `Y`, with free variables other than `x`, has only a hand proof. The problem does not need this case, because combinations of `B`, `M` and `I` are closed.
- The clock argument in the paper's "Related work" section is also by hand.
- The printed text has had errors that the Lean proof did not have, and such errors can still exist.

Please report errors in an issue.

## License

[CC-BY 4.0](https://creativecommons.org/licenses/by/4.0/), for the paper and the Lean proof.
