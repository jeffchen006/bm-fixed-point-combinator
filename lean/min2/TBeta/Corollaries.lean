import TBeta.Main

/-! # Corollaries, not used by the main theorem: a free variable in place of `x`, and combinatory weak equality. -/

namespace TBeta

open LeanJudge LeanJudge.Term

section Rules
variable (a b c : Term)

theorem conv_W : Conv false (.app (.app Atom.W.term a) b) (.app (.app a b) b) := by
  refine .trans (.appL b (Conv.beta _ _)) ?_
  simp only [subst]; simp
  refine .trans (Conv.beta _ _) ?_
  simp [subst, subst_shift]
  exact .refl _

theorem conv_C : Conv false (.app (.app (.app Atom.C.term a) b) c) (.app (.app a c) b) := by
  refine .trans (.appL c (.appL b (Conv.beta _ _))) ?_
  simp only [subst]; simp
  refine .trans (.appL c (Conv.beta _ _)) ?_
  simp only [subst]; simp [subst_shift_succ]
  refine .trans (Conv.beta _ _) ?_
  simp [subst, subst_shift]
  exact .refl _

theorem conv_K : Conv false (.app (.app Atom.K.term a) b) a := by
  refine .trans (.appL b (Conv.beta _ _)) ?_
  simp only [subst]; simp
  refine .trans (Conv.beta _ _) ?_
  simp [subst, subst_shift]
  exact .refl _

theorem conv_S : Conv false (.app (.app (.app Atom.S.term a) b) c) (.app (.app a c) (.app b c)) := by
  refine .trans (.appL c (.appL b (Conv.beta _ _))) ?_
  simp only [subst]; simp
  refine .trans (.appL c (Conv.beta _ _)) ?_
  simp only [subst]; simp [subst_shift_succ]
  refine .trans (Conv.beta _ _) ?_
  simp [subst, subst_shift]
  exact .refl _

end Rules

theorem wroot_conv {t u : CL} (h : CL.WRoot t u) : Conv false t.term u.term := by
  cases h with
  | B => exact conv_B ..
  | M => exact conv_M ..
  | I => exact conv_I ..
  | W => exact conv_W ..
  | C => exact conv_C ..
  | K => exact conv_K ..
  | S => exact conv_S ..

theorem wstep_conv {t u : CL} (h : CL.WStep t u) : Conv false t.term u.term := by
  induction h with
  | root r => exact wroot_conv r
  | appL a _ ih => exact .appL _ ih
  | appR f _ ih => exact .appR _ ih

/-- `=w` implies `=β`, on the lambda interpretation. -/
theorem wconv_conv {t u : CL} (h : CL.WConv t u) : Conv false t.term u.term := by
  induction h with
  | refl => exact .refl _
  | step s => exact wstep_conv s
  | symm _ ih => exact .symm ih
  | trans _ _ i1 i2 => exact .trans i1 i2

theorem cl_term (t : Tree) : t.cl.term = Y t := by
  induction t with
  | atom a => rfl
  | app s t ihs iht => simp [Tree.cl, CL.term, Y, ihs, iht]

/-- `xⁿ t`, in `CL`. -/
def xc : Nat → CL → CL
  | 0, t => t
  | n + 1, t => .app .x (xc n t)

theorem xc_term (n : Nat) (t : CL) : (xc n t).term = xp n t.term := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Term.app .x (xc n t).term = _
    rw [ih]
    rfl

/-- **The weak form.** For `Y` over `B`, `M`, `I` and `r ≥ 1`, `Y x =w xʳ (Y x)` is false. -/
theorem no_weak_xr (t : Tree) (ht : t.over [.B, .M, .I] = true) {r : Nat} (hr : 1 ≤ r) :
    ¬ CL.WConv (.app t.cl .x) (xc r (.app t.cl .x)) := by
  intro h
  have := wconv_conv h
  rw [xc_term] at this
  show False
  apply no_fix_xr false t ht hr
  have e : (CL.app t.cl .x).term = .app (Y t) .x := by
    show Term.app t.cl.term .x = _
    rw [cl_term]
  rwa [e] at this

/-! ### A free variable in place of the constant `x` -/

/-- `h (h (.. (h t)))`, with `r` copies of `h`. -/
def iterApp (h : Term) : Nat → Term → Term
  | 0, t => t
  | n + 1, t => .app h (iterApp h n t)

theorem iterApp_x (r : Nat) (t : Term) : iterApp .x r t = xp r t := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [iterApp, xp, ih]

theorem subst_iterApp (h : Term) (r : Nat) (t s : Term) (i : Nat) :
    Term.subst (iterApp h r t) s i = iterApp (Term.subst h s i) r (Term.subst t s i) := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [iterApp, Term.subst, ih]

theorem Y_subst (t : Tree) (s : Term) (i : Nat) : Term.subst (Y t) s i = Y t := by
  induction t with
  | atom a => cases a <;> rfl
  | app p q ip iq => simp only [Y, Term.subst, ip, iq]

/-- The equation at the index `k` gives the equation at its image under `[s/0]`, by abstraction and `β`. -/
theorem abstract_at {e : Bool} {t : Tree} {r k : Nat} {u : Term} (hu : Term.subst (.var k) .x 0 = u)
    (h : Conv e (.app (Y t) (.var k)) (iterApp (.var k) r (.app (Y t) (.var k)))) :
    Conv e (.app (Y t) u) (iterApp u r (.app (Y t) u)) := by
  have e1 : Term.subst (.app (Y t) (.var k)) .x 0 = .app (Y t) u := by
    show Term.app (Term.subst (Y t) .x 0) (Term.subst (.var k) .x 0) = _
    rw [Y_subst, hu]
  have e2 : Term.subst (iterApp (.var k) r (.app (Y t) (.var k))) .x 0 = iterApp u r (.app (Y t) u) := by
    rw [subst_iterApp, hu, e1]
  have b1 := Conv.beta (e := e) (.app (Y t) (.var k)) .x
  have b2 := Conv.beta (e := e) (iterApp (.var k) r (.app (Y t) (.var k))) .x
  rw [e1] at b1
  rw [e2] at b2
  exact .trans (.symm b1) (.trans (Conv.appL _ (Conv.lam h)) b2)

/-- **A free variable.** For `Y` over `B`, `M`, `I`, `r ≥ 1` and each index `k`, `Y v ≠ vʳ (Y v)`, at `=β` and `=βη`. -/
theorem no_fix_var (e : Bool) (t : Tree) (ht : t.over [.B, .M, .I] = true) {r : Nat} (hr : 1 ≤ r) (k : Nat) :
    ¬ Conv e (.app (Y t) (.var k)) (iterApp (.var k) r (.app (Y t) (.var k))) := by
  induction k with
  | zero =>
    intro h
    have := abstract_at (u := .x) (by simp [Term.subst, shift_zero]) h
    rw [iterApp_x] at this
    exact no_fix_xr e t ht hr this
  | succ k ih =>
    intro h
    exact ih (abstract_at (by simp [Term.subst]) h)

end TBeta
