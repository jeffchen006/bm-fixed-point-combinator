import TBeta.N
import TBeta.PartA

/-! # The final theorem: part A gives an alive word, part B its shape, part C the contradiction. -/

namespace TBeta

open LeanJudge N

/-- A monomial as a letter. -/
def toL : Nat × Atom → Lt
  | (n, .M) => (n, Ch.M)
  | (n, _) => (n, Ch.B)

theorem mono_lt {n : Nat} {a : Atom} (h : a = .B ∨ a = .M) : PartA.mono n a = lt (toL (n, a)) := by
  have e : ∀ m, PartA.mono m a = bp m a.term := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => simp only [PartA.mono, bp, ih]
  rcases h with rfl | rfl
  · exact e n
  · exact e n

theorem S_plug (l : List (Nat × Atom)) (h : ∀ m ∈ l, m.2 = .B ∨ m.2 = .M) (z : Term) :
    PartA.S l z = plug (l.map toL) z := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    simp only [PartA.S, List.map_cons, plug]
    rw [ih fun c hc => h c (List.mem_cons_of_mem _ hc), mono_lt (h m (List.mem_cons_self ..))]

/-- **Main theorem.** For `Y` over `B`, `M`, `I`, a fresh constant `x` and `r ≥ 1`, `Y x ≠ xʳ (Y x)`, at `=β` and `=βη`. -/
theorem no_fix_xr (e : Bool) (t : Tree) (ht : t.over [.B, .M, .I] = true) {r : Nat} (hr : 1 ≤ r) :
    ¬ Conv e (.app (Y t) .x) (xp r (.app (Y t) .x)) := by
  intro h
  obtain ⟨l, hl, hc⟩ := PartA.partA ht hr h
  rw [S_plug l hl] at hc
  obtain ⟨L, c, u, hu, hW⟩ := shape_of_alive (P := l.map toL) (by
    intro c hc'
    obtain ⟨⟨n, a⟩, _, rfl⟩ := List.mem_map.1 hc'
    cases a <;> simp [toL]) (alive_of_fix hr hc)
  exact G2.coreW_not_fix L c u (nx_pos hu) hr (.trans (.symm hW) (.trans hc (conv_xp r hW)))

/-- The case `r = 1`. -/
theorem no_fix_x (e : Bool) (t : Tree) (ht : t.over [.B, .M, .I] = true) :
    ¬ Conv e (.app (Y t) .x) (.app .x (.app (Y t) .x)) :=
  no_fix_xr e t ht (r := 1) (Nat.le_refl 1)

/-- **No combination of `B`, `M`, `I` is a fixed-point combinator, at `=β` or `=βη`.** -/
theorem no_fixed_point_combinator (e : Bool) (t : Tree) (ht : t.over [.B, .M, .I] = true) :
    ¬ IsFixedPointCombinator e t :=
  fun h => no_fix_x e t ht (h .x)

end TBeta
