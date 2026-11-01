# Text to Lean

Statements of the text are named as in the paper. See `README.md` for how to run the check.

**Conventions of the formalization.** Terms have de Bruijn indices (`LeanJudge/Defs.lean`). The symbol `x` of the text is the constant `Term.x`. No binder can bind it, and substitution never replaces it. Letters are pairs `(n, C)`, with `C` one of `Ch.M`, `Ch.B`, `Ch.x`. A word is a list of letters. To read the statements, a reader needs `LeanJudge/Defs.lean` and these definitions: `IsFixedPointCombinator` (`LeanJudge/Final.lean`) for `no_fixed_point_combinator`; `xp` (`TBeta/CR.lean`) for `no_fix_xr`; `iterApp` (`TBeta/Corollaries.lean`) for `no_fix_var`; `xc` (`TBeta/Corollaries.lean`) for `no_weak_xr`. `TBeta/Restate.lean` restates the theorem with its own `iterx`, so `theorem_1` needs only `Defs.lean` and that one definition. The step from the constant to a free variable is `no_fix_var`. The step from closed `Y` to open `Y` is not in Lean. `Defs.lean` also defines the atoms `W`, `C`, `K`, `S`, which the theorems exclude by `Tree.over`. `CL` and `WConv` in it are used only by `TBeta/Corollaries.lean`.

**Namespaces.** `TBeta` for `Alive.lean`, `Main.lean`, `Corollaries.lean` and `CR.lean`; `TBeta.N` for `N.lean`; `TBeta.G2` for `Core2.lean` and `Control.lean`; `TBeta.Restate` for `Restate.lean`; `PartA` for `PartA.lean`.

**Words of the text and of the source.** The source is frozen, so its comments and names keep some earlier words. The text's words are in the first column below.
| Text | In Lean names and comments |
|---|---|
| Reduction, Shape, Separation | Part A, Part B, Part C; `PartA`, `TBeta.N`, `TBeta.G2` |
| Core term `Q` | `W` in comments, `coreW`. (`PartA.W` is a different thing: the type of combinations) |
| State `(S, R)` | `St X S V`: the Lean variable `V` is `R` |
| List `d` of the core term | `us`, `u` |
| Fold `h·R` | `pop`, "Pop" |
| Slack, its bound | "height − level", `Bd` |
| The search | `start`, `run`, "the run" |
| Tidy | `J`, `bodyOK` |
| Acts as a word | `Rep` |
| `F_k`, `B_k(u)`, `H(i,j)` | `G σ .F k`, `G σ (.C (.B u)) k`, `G σ (.C (.H j)) i` |

**Status column.** This compares the type of the Lean declaration with the statement in the text. The types are in the source. `Audit.lean` restates the types of the main ones in `example`s, which the kernel checks.
- **exact**: the Lean type says the same thing as the text, up to the conventions above.
- **stronger**: the Lean type implies the text, by an instance that the note gives.
- **restricted**: the Lean type is narrower than the text, as the note says.
- **local**: the fact is a step inside the proof of the declaration named. It has no type of its own.
- **definition**: a definition, not a claim.

`scripts/table_names.lean` checks only that each name exists. It does not compare types.

**Line counts.** "Used lines" are source lines in the declaration ranges of the constants that the walk of proof terms from `no_fixed_point_combinator` reaches (`scripts/DepGraph.lean`, `scripts/dep_sum.py`). Auxiliary constants are charged to their owner. Comments and blank lines between declarations do not count. The route has 2712 used lines. Physical lines by `wc -l` (`scripts/check.sh` prints them): 3127 for the nine route modules, and 3343 for all twelve modules. The other three are outside the route: `TBeta/Control.lean` (25), `TBeta/Corollaries.lean` (152), `TBeta/Restate.lean` (39).

## Main theorems (`TBeta/Main.lean`)
| Text | Lean name | Status | Note |
|---|---|---|---|
| Main theorem: `Yx ≠ x^q(Yx)`, `q ≥ 1`, `Y` closed over B, M, I, at `=β` and `=βη` | `no_fix_xr` | exact | `x` is the constant; `no_fix_var` gives a variable. Open `Y` is not in Lean |
| The case `q = 1` | `no_fix_x` | exact | `x` is the constant. Instance of `no_fix_xr` |
| No fixed-point combinator, for each test term | `no_fixed_point_combinator` | exact | `x` is the constant. From `no_fix_x` at the term `.x`. Uses `LeanJudge.IsFixedPointCombinator` |
| `S` of a list is `P[z]`, for its letters | `S_plug`, `mono_lt`, `toL` | definition | Join of the letters of Reduction and Shape |

## Reduction (`TBeta/PartA.lean`)
| Text | Lean name | Status | Note |
|---|---|---|---|
| Proposition (Reduction): `tx =βη x^q(tx)` gives a word `P` over `m_n`, `b_n` with `P[x] =β x^q P[x]` | `partA` | exact | No "non-empty": the empty word is excluded in Shape, by `not_alive_x` |
| Letter, `S_w(z)` | `mono`, `S` | definition | |
| Head step, run, headed | `NS`, `Run`, `VH` | definition | |
| Determinism; a run passes through | `ns_det`, `run_step`, `run_prefix`, `lam_stuck` | exact | |
| Reach a head: `s =βη` headed gives `s l̄ →h*` headed | `HR`, `HR.of_reds`, `VH.reds` | restricted | `HR.of_reds` has `s ↠βη u` with `u` reaching a head. The step from `=βη` by Church-Rosser is local in `partA` |
| β step of that lemma | `Int`, `Int.vh`, `int_subst`, `par_factor`, `int_ns`, `par_run_vh`, `ns_subst`, `run_subst` | exact | |
| η step of that lemma | `E`, `step_split`, `EL`, `eta_run`, `appsT` | exact | |
| Combination | `W`, `W.term`, `toW`, `toW_term` | definition | |
| Rules for B, M, I; too few arguments | `run_B`, `run_M`, `run_I`, `B_run`, `M_run`, `I_run` | exact | |
| Head step, or B, M, I, BU, BUV | `Stuck`, `W.cases'` | exact | |
| Acts as a word; closure rules | `Rep`, `Rep.BU`, `Rep.BUV`, `S_lift`, `lift`, `S_append`, `run_conv` | exact | `Rep` is at `=βη` |
| First argument: `X t̄ →h^n` headed gives `t̄ = t_1 ..`, the run passes through `t_1 s̄`, `X` acts as a word | `first_arg` | exact | The prefix is `Run j`, with `j + m = n` |
| Tidy | `bodyOK`, `J` | definition | |
| A β-reduct of an applicative term over B, M, x has no η-redex | `J_subst`, `J_step`, `step_no_eta`, `reds_no_eta`, `bodyOK_shift`, `J_shift`, `bodyOK_subst`, `step_not_var` | stronger | For all tidy terms (`J`) |
| An applicative term over B, M, x is tidy | `J_mono`, `J_S`, `J_xp` | restricted | Only for the terms used: `mono n a`, `S l x` (a word applied to `x`), and `x^q t` for tidy `t`. Lean has no statement for all applicative terms |
| No η: tidy `s =βη s'` gives `s =β s'` | `J_conv` | stronger | For all tidy `s`, `s'`. The text states it for applicative terms |

## Shape (`TBeta/N.lean`, `TBeta/Alive.lean`)
| Text | Lean name | Status | Note |
|---|---|---|---|
| Letter, word, `w[t]`, `ŵ` | `Ch`, `Ch.t`, `Lt`, `bp`, `lt`, `plug`, `hat` | definition | `Ch`, `Lt`, `bp`, `lt`, `plug` are in `TBeta/Core2.lean` |
| Degree, `b(w)`, walk, slack bound | `Ch.d`, `dg`, `bz`, `legal`, `Walk`, `Bd` | definition | Height = list length at the letter |
| Alive; `t =β x^q t` gives alive | `Alive`, `alive_of_fix` | exact | |
| Alive is kept by `=β`, and by removing `x^n` | `Alive.conv`, `Alive.peel`, `Alive.peelN` | exact | |
| Not alive: abstraction; `x`; `x` with two arguments; `ŵ` | `not_alive_lam`, `not_alive_x`, `not_alive_two`, `not_alive_hat` | exact | |
| `ŵ t =β w[t]` | `hat_app` | exact | |
| List rule | `list_rule`, `letter` | exact | |
| At most one start for a word with an `x` letter | `two_walk`, `HasX` | exact | |
| A walk from `≥ 1` has no `x_0` | `walk_pos` | exact | |
| A walk from `0` with no `m_0` has degree `0` | `walk_zero` | exact | |
| Fold `h·R`, `↑R`, condition on `h` | `pop`, `pop1`, `up`, `OK` | definition | |
| Fold (a): `h[R̂] =β (h·R)^` | `pop_conv`, `hat_up`, `fact_dist` | exact | |
| Fold (b): degree and last letter | `dg_pop`, `dg_up`, `LastX.pop` | exact | |
| Fold (c): bound on the slack | `Bd_pop`, `Bd_up`, `Bd_append`, `exists_Bd` | exact | |
| State | `St`, `LastX` | definition | |
| At a state `(S, R)`: walks, `dg(S) ≥ 0`, `dg(R) = 1` | `St.facts` | exact | |
| Start: `P` has `m_0` | `start` | local | Inside `start`, with `rsplit` |
| Start: `P = S m_0 h` gives the state `(S, h·x_0)` | `St.init` | restricted | Takes `OK` on `h` as a premise. `start` proves it |
| Next: `S R` has `m_0` | `run` | local | Inside `run`, by `walk_zero` |
| Next: `S R = S' m_0 h` gives the state `(S', h·R)` | `St.next`, `split_where`, `rsplit`, `ok_of`, `level_of_bz` | restricted | `St.next` takes `OK` on `h` as a premise. `run` proves it |
| The search stops | `start`, `run` | exact | `run` is the induction on (`ρ − E`, length of `S`). It stops only when the `m_0` is in `R` and `b(h) = 0` |
| Last state gives `X =β Q`, `Q = L[a a]` | `St.shape`, `plug_up_app`, `exists_down`, `conv_eta_exp`, `hasX_of_up`, `two_letters` | exact | `conv_eta_exp`: `T =β λq` gives `T =β λ. T↑ 0`. No η |
| Theorem (Shape): `P` over `m_n`, `b_n`, `P[x]` alive, gives `L`, `c`, `d` with an `x` letter in `d`, `P[x] =β Q`, the core term | `shape_of_alive` | exact | No "non-empty": `plug [] .x` is `.x`, not alive |

## Separation (`TBeta/Core2.lean`)
| Text | Lean name | Status | Note |
|---|---|---|---|
| Definition of the family: `F_k`, `B_k(u)`, `H(i,j)`, and `D`-bodies | `G`, `Kd`, `Hk` | definition | `x` is the constant, so no context binds it. A kind records the head variable as an index |
| `Ψ(i,j) = 2σi − j(j−σ)` | `val` | definition | |
| Stable under substitution | `G.sub`, `Mv`, `MK` | restricted | Substitutes for an index, never for `x`. `MK` is a premise: the head variables move to variables by `Mv` |
| Stable under shift | `G.shift`, `up1`, `upK` | exact | The named text has no shift |
| Stable under `→β`, for `F_k` and `B_k(u)` | `G.step` | stronger | It also covers the `D`-bodies (kind `D`). Premise `nonH`: not an `H` kind. `ctx_root` is the redex of a context |
| `→β` keeps `Ψ` on `H(i,j)` | `G.stepH`, `G.redsH`, `G.transD`, `G.transB` | exact | |
| `x t ∈ H(i+1,j)` | `G.cx` | exact | A rule of `G`. `G.xp` iterates it |
| `Ψ(i+q,j) = Ψ(i,j) + 2σq` | `state_not_fix` | local | Arithmetic inside the proof |
| Count on the head path, reading | `hx`, `rd`, `G.hx`, `G.rd` | exact | `G.rd` has its statement by kind (`rdP`) |
| `σ ≥ 1`, `t ∈ H(i,j)` gives `t ≠β x^q t` | `state_not_fix` | exact | |
| Letter: `l t ↠ C[t]`, with the count of `C` that of `l`; `w[t] ↠ C[t]` | `lt_red`, `plug_red`, `nx` | restricted | Only for `t` in the family, with the result in the family. A context is not an object in Lean |
| Core term `Q = L[a a]`, `a = λy.c[D_y D_y]`, `D_y = λw.d[y w]` | `coreW`, `aT`, `Dy` | definition | |
| `Q` reduces to a member of `H` | `coreW_state` | exact | |
| Theorem (Separation): `Q ≠β x^q Q` | `coreW_not_fix` | exact | |

## Base
| Text | Lean name | File | Status |
|---|---|---|---|
| Church-Rosser | `church_rosser` | `TBeta/CR.lean` | exact |
| `x^n t` | `xp`, `xp_add`, `conv_xp` | `TBeta/CR.lean` | definition |
| Rules of B, M, I | `LeanJudge.conv_B`, `LeanJudge.conv_M`, `LeanJudge.conv_I` | `LeanJudge/Basic.lean` | exact |

## Not used by the main theorem
| Text | Lean name | File | Status |
|---|---|---|---|
| Weak form: `Yx =w x^q(Yx)` is false | `no_weak_xr`, `xc`, `wconv_conv`, `cl_term` | `TBeta/Corollaries.lean` | exact |
| Free variable `v` in place of `x`: `Yv ≠ v^r(Yv)` | `no_fix_var`, `iterApp`, `abstract_at`, `Y_subst` | `TBeta/Corollaries.lean` | exact |
| `σ ≥ 1` is needed | `a0`, `a0_F`, `sigma_zero_control` | `TBeta/Control.lean` | exact |
| Theorem 1 with its own power of `x`; a type check against `no_fix_xr` | `theorem_1`, `iterx`, `iterx_eq` | `TBeta/Restate.lean` | exact |
| Over B, M only, at `=β`, `r = 1` | `theorem_1_BM`, `over_BM` | `TBeta/Restate.lean` | exact |
