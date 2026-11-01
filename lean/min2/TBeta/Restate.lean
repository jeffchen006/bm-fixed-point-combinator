import TBeta.Main

/-! # The theorem, with its power of `x` written here. Only `LeanJudge/Defs.lean` occurs in the statements below,
and `iterx`. -/

namespace TBeta.Restate

open LeanJudge

/-- `xʳ t`. -/
def iterx : Nat → Term → Term
  | 0, t => t
  | n + 1, t => .app .x (iterx n t)

/-- `iterx` is the `xp` of the main theorem. -/
theorem iterx_eq (r : Nat) (t : Term) : iterx r t = xp r t := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [iterx, xp, ih]

/-- **Theorem 1.** For `Y` over `B`, `M`, `I` and `r ≥ 1`, `Y x ≠ xʳ (Y x)`, at `=β` and `=βη`. -/
theorem theorem_1 (e : Bool) (t : Tree) (ht : t.over [.B, .M, .I] = true) (r : Nat) (hr : 1 ≤ r) :
    ¬ Conv e (.app (Y t) .x) (iterx r (.app (Y t) .x)) := by
  rw [iterx_eq]
  exact no_fix_xr e t ht hr

theorem over_BM {t : Tree} (h : t.over [.B, .M] = true) : t.over [.B, .M, .I] = true := by
  induction t with
  | atom a => cases a <;> simp_all [Tree.over]
  | app s t ihs iht =>
    simp only [Tree.over, Bool.and_eq_true] at h ⊢
    exact ⟨ihs h.1, iht h.2⟩

/-- **Over `B`, `M` only, at `=β`, and `r = 1`.** The problem as first posed. -/
theorem theorem_1_BM (t : Tree) (ht : t.over [.B, .M] = true) :
    ¬ Conv false (.app (Y t) .x) (.app .x (.app (Y t) .x)) :=
  theorem_1 false t (over_BM ht) 1 (Nat.le_refl 1)

end TBeta.Restate
