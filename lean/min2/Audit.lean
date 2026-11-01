import TBeta.Main
import TBeta.Control
import TBeta.Corollaries
import TBeta.Restate

/-! Run with `lake env lean Audit.lean`. Each `example` states the exact type of a theorem. -/

open LeanJudge TBeta TBeta.N

/-- `xp` is what it says. -/
example (t : Term) : xp 0 t = t ∧ xp 2 t = .app .x (.app .x t) := ⟨rfl, rfl⟩

/-- The main theorem. -/
example : ∀ (e : Bool) (t : Tree), t.over [.B, .M, .I] = true → ∀ {r : Nat}, 1 ≤ r →
    ¬ Conv e (.app (Y t) .x) (xp r (.app (Y t) .x)) :=
  TBeta.no_fix_xr

/-- The case `r = 1`. -/
example : ∀ (e : Bool) (t : Tree), t.over [.B, .M, .I] = true →
    ¬ Conv e (.app (Y t) .x) (.app .x (.app (Y t) .x)) :=
  TBeta.no_fix_x

/-- In the form of `LeanJudge/Final.lean`. -/
example : ∀ (e : Bool) (t : Tree), t.over [.B, .M, .I] = true → ¬ IsFixedPointCombinator e t :=
  TBeta.no_fixed_point_combinator

/-- Part A. -/
example : ∀ {e : Bool} {t : Tree} {q : Nat}, t.over [.B, .M, .I] = true → 1 ≤ q →
    Conv e (.app (Y t) .x) (xp q (.app (Y t) .x)) →
    ∃ l : List (Nat × Atom), (∀ m ∈ l, m.2 = .B ∨ m.2 = .M) ∧ Conv false (PartA.S l .x) (xp q (PartA.S l .x)) :=
  PartA.partA

/-- Part A, the first-argument lemma, with the run through `a s`. -/
example : ∀ (n : Nat) (X : PartA.W) (l : List Term) (K : Term), PartA.Run n (PartA.appsT X.term l) K → PartA.VH K →
    ∃ a l' s j m, l = a :: l' ∧ j + m = n ∧ PartA.Run j (PartA.appsT X.term l) (PartA.appsT a s) ∧
      PartA.Run m (PartA.appsT a s) K ∧ ∃ w, PartA.Rep X w :=
  PartA.first_arg

/-- Part B, the initial state. -/
example : ∀ {S h : List Lt}, (∀ l ∈ h, OK l) → St (plug (S ++ (0, Ch.M) :: h) .x) S (pop h [(0, Ch.x)]) :=
  St.init

/-- Part B, the shape theorem. -/
example : ∀ {P : List Lt}, (∀ l ∈ P, l.2 ≠ .x) → Alive (plug P .x) →
    ∃ L c u, HasX u ∧ Conv false (plug P .x) (G2.coreW L c u) :=
  shape_of_alive

/-- Part C. -/
example : ∀ (ls cs us : List Lt), 1 ≤ G2.nx us → ∀ {q : Nat}, 1 ≤ q →
    ¬ Conv false (G2.coreW ls cs us) (xp q (G2.coreW ls cs us)) :=
  G2.coreW_not_fix

/-- The weak form. -/
example : ∀ (t : Tree), t.over [.B, .M, .I] = true → ∀ {r : Nat}, 1 ≤ r →
    ¬ CL.WConv (.app t.cl .x) (xc r (.app t.cl .x)) :=
  no_weak_xr

/-- A free variable in place of `x`. -/
example : ∀ (e : Bool) (t : Tree), t.over [.B, .M, .I] = true → ∀ {r : Nat}, 1 ≤ r → ∀ (k : Nat),
    ¬ Conv e (.app (Y t) (.var k)) (iterApp (.var k) r (.app (Y t) (.var k))) :=
  no_fix_var

/-- `iterApp` is what it says. -/
example (h t : Term) : iterApp h 0 t = t ∧ iterApp h 2 t = .app h (.app h t) := ⟨rfl, rfl⟩

/-- The theorem with its own power of `x`. -/
example : ∀ (e : Bool) (t : Tree), t.over [.B, .M, .I] = true → ∀ (r : Nat), 1 ≤ r →
    ¬ Conv e (.app (Y t) .x) (Restate.iterx r (.app (Y t) .x)) :=
  Restate.theorem_1

/-- Over `B`, `M` only, at `=β`. -/
example : ∀ (t : Tree), t.over [.B, .M] = true → ¬ Conv false (.app (Y t) .x) (.app .x (.app (Y t) .x)) :=
  Restate.theorem_1_BM

#print axioms TBeta.no_fix_xr
#print axioms TBeta.no_fix_x
#print axioms TBeta.no_fixed_point_combinator
#print axioms TBeta.N.shape_of_alive
#print axioms TBeta.G2.coreW_not_fix
#print axioms TBeta.no_weak_xr
#print axioms TBeta.no_fix_var
#print axioms TBeta.Restate.theorem_1
#print axioms TBeta.Restate.theorem_1_BM
#print axioms TBeta.G2.sigma_zero_control
