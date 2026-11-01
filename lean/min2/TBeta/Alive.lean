import TBeta.Core2

/-! # `Alive`: `x` with one argument, at each depth. Eta expansion. `B` terms. -/

namespace TBeta

open LeanJudge LeanJudge.Term G2

/-- `t a₁ .. aₙ`. -/
def sp (t : Term) : List Term → Term
  | [] => t
  | a :: l => sp (.app t a) l

/-- `T =β xᴺ z`, for each `N`. -/
def Alive (T : Term) : Prop := ∀ N, ∃ z, Conv false T (xp N z)

theorem Alive.conv {T T' : Term} (h : Alive T) (c : Conv false T T') : Alive T' := by
  intro N
  obtain ⟨z, hz⟩ := h N
  exact ⟨z, .trans (.symm c) hz⟩

theorem reds_app_x {r z : Term} (h : Reds false (.app .x r) z) : ∃ r', z = .app .x r' ∧ Reds false r r' := by
  have gen : ∀ a b, Reds false a b → ∀ r, a = .app .x r → ∃ r', b = .app .x r' ∧ Reds false r r' := by
    intro a b rr
    induction rr with
    | refl => intro r e; exact ⟨r, e, .refl _⟩
    | step s _ ih =>
      intro r e
      subst e
      rcases step_app s with ⟨b0, hb, _⟩ | ⟨f', _, q⟩ | ⟨a', rfl, q⟩
      · cases hb
      · exact absurd q step_x'
      · obtain ⟨r', e, r3⟩ := ih a' rfl
        exact ⟨r', e, .step q r3⟩
  exact gen _ _ h r rfl

theorem Alive.peel {r : Term} (h : Alive (.app .x r)) : Alive r := by
  intro N
  obtain ⟨z, hz⟩ := h (N + 1)
  obtain ⟨w, r1, r2⟩ := church_rosser hz
  obtain ⟨r', rfl, r3⟩ := reds_app_x r1
  obtain ⟨r'', e, r4⟩ := reds_app_x (r := xp N z) r2
  cases e
  exact ⟨z, .trans (reds_conv r3) (.symm (reds_conv r4))⟩

theorem Alive.peelN {t : Term} : ∀ (n : Nat), Alive (xp n t) → Alive t := by
  intro n
  induction n with
  | zero => exact fun h => h
  | succ n ih => exact fun h => ih (Alive.peel h)

/-- `x` with at least two arguments. -/
inductive TwoX : Term → Prop
  | base (p q) : TwoX (.app (.app .x p) q)
  | ext {t} (a) : TwoX t → TwoX (.app t a)

theorem TwoX.step {t t' : Term} (h : TwoX t) (s : Step false t t') : TwoX t' := by
  induction h generalizing t' with
  | base p q =>
    rcases step_app s with ⟨b0, hb, _⟩ | ⟨f', rfl, st2⟩ | ⟨a', rfl, _⟩
    · cases hb
    · rcases step_app st2 with ⟨b0, hb, _⟩ | ⟨f', _, q2⟩ | ⟨a', rfl, _⟩
      · cases hb
      · exact absurd q2 step_x'
      · exact .base _ _
    · exact .base _ _
  | @ext t a h0 ih =>
    rcases step_app s with ⟨b0, hb, _⟩ | ⟨f', rfl, st2⟩ | ⟨a', rfl, _⟩
    · subst hb
      cases h0
    · exact .ext a (ih st2)
    · exact .ext _ h0

theorem TwoX.sp' {t : Term} (h : TwoX t) (l : List Term) : TwoX (sp t l) := by
  induction l generalizing t with
  | nil => exact h
  | cons a l ih => exact ih (.ext a h)

theorem TwoX.reds {a b : Term} (r : Reds false a b) (h : TwoX a) : TwoX b := by
  induction r with
  | refl => exact h
  | step s _ ih => exact ih (h.step s)

theorem not_alive_two {r s : Term} {l : List Term} : ¬ Alive (sp (.app (.app .x r) s) l) := by
  intro h
  obtain ⟨z, hz⟩ := h 1
  obtain ⟨w, r1, r2⟩ := church_rosser hz
  obtain ⟨r', rfl, _⟩ := reds_app_x (r := xp 0 z) r2
  have := TwoX.reds r1 ((TwoX.base r s).sp' l)
  cases this with
  | ext _ h0 => cases h0

theorem not_alive_lam {T q : Term} (c : Conv false T (.lam q)) : ¬ Alive T := by
  intro h
  obtain ⟨z, hz⟩ := h 1
  have c2 : Conv false (.lam q) (.app .x (xp 0 z)) := .trans (.symm c) hz
  obtain ⟨w, r1, r2⟩ := church_rosser c2
  obtain ⟨r', rfl, _⟩ := reds_app_x r2
  have gen : ∀ a b, Reds false a b → (∃ q, a = .lam q) → ∃ q', b = .lam q' := by
    intro a b rr
    induction rr with
    | refl => exact id
    | step s _ ih =>
      rintro ⟨q0, rfl⟩
      cases s with
      | root ro => cases ro
      | lam _ => exact ih ⟨_, rfl⟩
  obtain ⟨q', e⟩ := gen _ _ r1 ⟨q, rfl⟩
  cases e

theorem not_alive_x : ¬ Alive .x := by
  intro h
  obtain ⟨z, hz⟩ := h 1
  obtain ⟨w, r1, r2⟩ := church_rosser hz
  obtain ⟨r', rfl, _⟩ := reds_app_x r2
  cases r1 with
  | step s _ => exact step_x' s

/-- `X =β xʳ X`, with `r ≥ 1`, gives `Alive X`. -/
theorem alive_of_fix {X : Term} {r : Nat} (hr : 1 ≤ r) (H : Conv false X (xp r X)) : Alive X := by
  have k : ∀ n, Conv false X (xp (r * n) X) := by
    intro n
    induction n with
    | zero => exact .refl _
    | succ n ih =>
      rw [Nat.mul_succ, Nat.add_comm, ← xp_add]
      exact .trans H (conv_xp _ ih)
  intro N
  have e : r * N = N + (r * N - N) := by
    have : N ≤ r * N := Nat.le_mul_of_pos_left _ hr
    omega
  refine ⟨xp (r * N - N) X, ?_⟩
  rw [xp_add, ← e]
  exact k N

/-! ### Eta expansion -/

theorem step_shift {t t' : Term} (h : Step false t t') (d c : Nat) :
    Step false (shift t d c) (shift t' d c) := by
  induction h generalizing c with
  | root r =>
    cases r with
    | beta _ b a =>
      have := shift_subst_le b a 0 d c (by omega)
      rw [this]
      exact .root (.beta _ _ _)
  | lam _ ih => exact .lam (ih _)
  | appL a _ ih => exact .appL _ (ih _)
  | appR f _ ih => exact .appR _ (ih _)

theorem conv_shift {t t' : Term} (h : Conv false t t') (d c : Nat) :
    Conv false (shift t d c) (shift t' d c) := by
  induction h with
  | refl => exact .refl _
  | step s => exact .step (step_shift s d c)
  | symm _ ih => exact .symm ih
  | trans _ _ i1 i2 => exact .trans i1 i2

theorem conv_eta_exp {T q : Term} (h : Conv false T (.lam q)) :
    Conv false T (.lam (.app (shift T 1 0) (.var 0))) := by
  have h1 : Conv false (.app (shift T 1 0) (.var 0)) (.app (shift (.lam q) 1 0) (.var 0)) :=
    Conv.appL _ (conv_shift h 1 0)
  have h2 : Conv false (.app (shift (.lam q) 1 0) (.var 0)) q := by
    have := Conv.beta (e := false) (shift q 1 1) (.var 0)
    rw [subst_shift_rename] at this
    exact this
  exact .trans h (Conv.lam (.symm (.trans h1 h2)))

theorem sp_conv {t t' : Term} (h : Conv false t t') (l : List Term) : Conv false (sp t l) (sp t' l) := by
  induction l generalizing t t' with
  | nil => exact h
  | cons a l ih => exact ih (Conv.appL _ h)

theorem sp_append (t : Term) (l l' : List Term) : sp t (l ++ l') = sp (sp t l) l' := by
  induction l generalizing t with
  | nil => rfl
  | cons a l ih => exact ih _

/-! ### `B` terms -/

theorem B1_lam (t : Term) : ∃ q, Conv false (.app Atom.B.term t) (.lam q) := ⟨_, Conv.beta _ _⟩

theorem B2_lam (t a : Term) : ∃ q, Conv false (.app (.app Atom.B.term t) a) (.lam q) :=
  ⟨_, .trans (Conv.appL _ (Conv.beta _ _)) (Conv.beta _ _)⟩

theorem B1 (e : Bool) (u : Term) : Conv e (.app Atom.B.term u)
    (.lam (.lam (.app (shift u 2 0) (.app (.var 1) (.var 0))))) := by
  have : Conv e (.app Atom.B.term u)
      (Term.subst (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) u 0) := Conv.beta _ _
  simpa [Term.subst] using this

theorem B2 (e : Bool) (u w : Term) : Conv e (.app (.app Atom.B.term u) w)
    (.lam (.app (shift u 1 0) (.app (shift w 1 0) (.var 0)))) := by
  refine .trans (.appL w (B1 e u)) ?_
  have := Conv.beta (e := e) (.lam (.app (shift u 2 0) (.app (.var 1) (.var 0)))) w
  simpa [Term.subst, subst_shift_succ] using this

/-- `B (B a b) =β B (B a) (B b)`. -/
theorem fact_dist (e : Bool) (a b : Term) :
    Conv e (.app Atom.B.term (.app (.app Atom.B.term a) b))
      (.app (.app Atom.B.term (.app Atom.B.term a)) (.app Atom.B.term b)) := by
  have l := B1 e (.app (.app Atom.B.term a) b)
  have r := B2 e (.app Atom.B.term a) (.app Atom.B.term b)
  have sB : ∀ d c, shift Atom.B.term d c = Atom.B.term := fun _ _ => rfl
  simp only [shift, sB] at l r
  have l2 := conv_B e (shift a 2 0) (shift b 2 0) (.app (.var 1) (.var 0))
  have r2 := B2 e (shift a 1 0) (.app (.app Atom.B.term (shift b 1 0)) (.var 0))
  simp only [shift, sB] at r2
  have r3 := conv_B e (shift (shift b 1 0) 1 0) (.var 1) (.var 0)
  have s1 : shift (shift a 1 0) 1 0 = shift a 2 0 := shift_add a 1 1 0 0 (by omega) (by omega)
  have s2 : shift (shift b 1 0) 1 0 = shift b 2 0 := shift_add b 1 1 0 0 (by omega) (by omega)
  simp only [Nat.zero_le, if_true] at r2
  rw [s1, s2] at r2
  rw [s2] at r3
  refine .trans l (.trans (Conv.lam (Conv.lam l2)) (.symm ?_))
  refine .trans r (Conv.lam ?_)
  exact .trans r2 (Conv.lam (Conv.appR _ r3))

end TBeta
