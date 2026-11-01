import LeanJudge.Defs
/-! # Shift, substitution, conversion, and what the combinators do. -/

namespace LeanJudge
open Term

namespace Term

@[simp] theorem shift_zero (t : Term) (c : Nat) : shift t 0 c = t := by
  induction t generalizing c with
  | var n => simp [shift]
  | lam b ih => simp [shift, ih]
  | app f a ihf iha => simp [shift, ihf, iha]
  | x => rfl

/-- Two shifts at compatible cutoffs add up. -/
theorem shift_add (t : Term) (d e c k : Nat) (h1 : c ≤ k) (h2 : k ≤ c + d) :
    shift (shift t d c) e k = shift t (d + e) c := by
  induction t generalizing c k with
  | var n =>
    simp only [shift]; congr 1
    by_cases h : c ≤ n <;> simp only [h, if_true, if_false] <;> (repeat' split) <;> omega
  | lam b ih => simp only [shift]; rw [ih _ _ (by omega) (by omega)]
  | app f a ihf iha => simp only [shift]; rw [ihf _ _ h1 h2, iha _ _ h1 h2]
  | x => rfl

/-- Two shifts at far cutoffs commute. -/
theorem shift_comm (t : Term) (d e c k : Nat) (h : k ≤ c) :
    shift (shift t d c) e k = shift (shift t e k) d (c + e) := by
  induction t generalizing c k with
  | var n =>
    simp only [shift]; congr 1
    by_cases h1 : c ≤ n <;> by_cases h2 : k ≤ n <;> simp only [h1, h2, if_true, if_false] <;> (repeat' split) <;> omega
  | lam b ih =>
    simp only [shift]; rw [ih _ _ (by omega)]
    congr 2; omega
  | app f a ihf iha => simp only [shift]; rw [ihf _ _ h, iha _ _ h]
  | x => rfl

/-- Substitution cancels a shift at the same index. -/
theorem subst_shift (t s : Term) (c : Nat) : subst (shift t 1 c) s c = t := by
  induction t generalizing c with
  | var n =>
    simp only [shift]
    by_cases h : c ≤ n
    · simp only [h, if_true, subst]
      rw [if_neg (by omega), if_pos (by omega)]; congr 1
    · simp only [h, if_false, subst]
      rw [if_neg (by omega), if_neg (by omega)]
  | lam b ih => simp [shift, subst, ih]
  | app f a ihf iha => simp [shift, subst, ihf, iha]
  | x => rfl

theorem subst_shift_succ (t s : Term) (k : Nat) : subst (shift t (k + 1) 0) s k = shift t k 0 := by
  have : shift t (k + 1) 0 = shift (shift t k 0) 1 k := by
    rw [shift_add t k 1 0 k (by omega) (by omega)]
  rw [this, subst_shift]

end Term

/-! ## Conversion -/

namespace Conv
variable {e : Bool}

theorem appL {f g : Term} (a : Term) (h : Conv e f g) : Conv e (.app f a) (.app g a) := by
  induction h with
  | refl => exact .refl _
  | step s => exact .step (.appL a s)
  | symm _ ih => exact .symm ih
  | trans _ _ i1 i2 => exact .trans i1 i2

theorem appR (f : Term) {a b : Term} (h : Conv e a b) : Conv e (.app f a) (.app f b) := by
  induction h with
  | refl => exact .refl _
  | step s => exact .step (.appR f s)
  | symm _ ih => exact .symm ih
  | trans _ _ i1 i2 => exact .trans i1 i2

theorem lam {a b : Term} (h : Conv e a b) : Conv e (.lam a) (.lam b) := by
  induction h with
  | refl => exact .refl _
  | step s => exact .step (.lam s)
  | symm _ ih => exact .symm ih
  | trans _ _ i1 i2 => exact .trans i1 i2

theorem beta (b a : Term) : Conv e (.app (.lam b) a) (subst b a 0) :=
  .step (.root (.beta e b a))

end Conv

theorem Root.mono {e : Bool} {t u : Term} (h : Root e t u) : Root true t u := by
  cases h with
  | beta => exact .beta _ _ _
  | eta => exact .eta _

theorem Step.mono {e : Bool} {t u : Term} (h : Step e t u) : Step true t u := by
  induction h with
  | root r => exact .root r.mono
  | lam _ ih => exact .lam ih
  | appL a _ ih => exact .appL a ih
  | appR f _ ih => exact .appR f ih

/-- `=β` implies `=βη`. -/
theorem Conv.mono {e : Bool} {t u : Term} (h : Conv e t u) : Conv true t u := by
  induction h with
  | refl => exact .refl _
  | step s => exact .step s.mono
  | symm _ ih => exact .symm ih
  | trans _ _ i1 i2 => exact .trans i1 i2

/-! ## The lambda terms do what the combinators do. -/

section Combinators
variable (e : Bool) (a b c : Term)
open Term

private theorem subst1 (t s : Term) : subst (shift t 1 0) s 0 = t := subst_shift t s 0

theorem conv_B : Conv e (.app (.app (.app Atom.B.term a) b) c) (.app a (.app b c)) := by
  refine .trans (.appL c (.appL b (Conv.beta _ _))) ?_
  simp only [subst]; simp
  refine .trans (.appL c (Conv.beta _ _)) ?_
  simp only [subst]; simp [subst_shift_succ]
  refine .trans (Conv.beta _ _) ?_
  simp only [subst, subst1]; simp
  exact .refl _

theorem conv_M : Conv e (.app Atom.M.term a) (.app a a) := by
  refine .trans (Conv.beta _ _) ?_
  simp [subst]; exact .refl _

theorem conv_I : Conv e (.app Atom.I.term a) a := by
  refine .trans (Conv.beta _ _) ?_
  simp [subst]; exact .refl _

end Combinators

end LeanJudge
