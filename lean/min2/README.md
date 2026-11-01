# Lean proof: no fixed-point combinator over B, M, I

## What it proves

Let `Y t` be a closed applicative combination of `B`, `M`, `I`, and let `x` be a constant that no binder binds and that substitution does not touch. Then for each `r ≥ 1`, `Y t x` is not convertible to `xʳ (Y t x)`, at `=β` (`e = false`) and at `=βη` (`e = true`).

```lean
theorem TBeta.no_fix_xr (e : Bool) (t : Tree) (ht : t.over [.B, .M, .I] = true) {r : Nat} (hr : 1 ≤ r) :
    ¬ Conv e (.app (Y t) .x) (xp r (.app (Y t) .x))
```

These follow from it:

| Name | File | Statement |
|---|---|---|
| `TBeta.no_fix_x` | `TBeta/Main.lean` | the case `r = 1` |
| `TBeta.no_fixed_point_combinator` | `TBeta/Main.lean` | `¬ IsFixedPointCombinator e t`, for `t` over `B`, `M`, `I` |
| `TBeta.no_fix_var` | `TBeta/Corollaries.lean` | the same with a free variable, at each de Bruijn index, in place of `x` |
| `TBeta.no_weak_xr` | `TBeta/Corollaries.lean` | the same at combinatory weak equality |
| `TBeta.Restate.theorem_1` | `TBeta/Restate.lean` | `no_fix_xr`, with its own power of `x` |
| `TBeta.Restate.theorem_1_BM` | `TBeta/Restate.lean` | over `B`, `M` only, at `=β`, `r = 1` |

Open `Y`, with free variables other than `x`, is not in Lean. The paper proves that step by hand.

## Run it

You need [elan](https://github.com/leanprover/elan), which reads the toolchain from `lean-toolchain` (`leanprover/lean4:v4.33.1`), and `python3` for the line counts. There is no external library: `lake-manifest.json` has no packages.

From this folder:

```
bash scripts/check.sh
```

The script removes `.lake`, then does these steps, and writes the log to `logs/check.log`:

1. `lake build` from empty.
2. `lake env lean Audit.lean`: `Audit.lean` restates the main types in `example`s and prints the axioms of each main theorem.
3. `lake env leanchecker` on all modules: a replay in the kernel.
4. It checks the SHA-256 of `LeanJudge/Defs.lean` and `LeanJudge/Final.lean`, and searches for `sorry`.
5. `scripts/table_names.lean` checks that each Lean name in `TABLE.md` exists. It does not compare types.
6. It prints the used lines and the physical lines.

The last line is `CHECK PASSED` or `CHECK FAILED`, and the exit status is 0 only for `CHECK PASSED`. The expected axioms are `propext`, `Classical.choice`, `Quot.sound`. `sigma_zero_control` uses a subset of them.

One known event: in four runs by a reader on a loaded host, one failed with a read error on the toolchain file `Iterators.ir`, while it built `TBeta.Corollaries`. It did not recur in six further runs, and the cause was not found. The script reports such a failure as `CHECK FAILED`. If you see it, look in `logs/build.log`, and run the script again.

## What a reader must trust

- The Lean kernel, and `leanchecker`.
- The definitions in the statements. To read a theorem, read these and no proof:

| Theorem | Definitions |
|---|---|
| all | `LeanJudge/Defs.lean`: `Term`, `shift`, `subst`, `Root`, `Step`, `Conv`, `Atom`, `Tree`, `Y`, `Tree.over` |
| `no_fixed_point_combinator` | also `IsFixedPointCombinator`, `LeanJudge/Final.lean` |
| `no_fix_xr` | also `xp`, `TBeta/CR.lean` |
| `no_fix_var` | also `iterApp`, `TBeta/Corollaries.lean` |
| `no_weak_xr` | also `CL`, `WConv`, `Tree.cl` in `Defs.lean`, and `xc`, `TBeta/Corollaries.lean` |
| `Restate.theorem_1` | also `iterx`, `TBeta/Restate.lean` |

`Defs.lean` also defines the atoms `W`, `C`, `K`, `S`. `Tree.over` excludes them from the theorems.

## Files

| File | Content |
|---|---|
| `LeanJudge/Defs.lean`, `LeanJudge/Final.lean` | The statement |
| `LeanJudge/Basic.lean`, `TBeta/CR.lean` | Shift and substitution facts, Church-Rosser |
| `TBeta/PartA.lean` | Reduction |
| `TBeta/N.lean`, `TBeta/Alive.lean` | Shape |
| `TBeta/Core2.lean` | Separation |
| `TBeta/Main.lean` | The main theorem |
| `TBeta/Corollaries.lean`, `TBeta/Restate.lean`, `TBeta/Control.lean` | Not used by the main theorem |
| `TABLE.md` | Each statement of the paper, its Lean name, and how the two differ |
