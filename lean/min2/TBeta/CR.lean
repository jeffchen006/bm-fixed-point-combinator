import LeanJudge.Defs
import LeanJudge.Basic

/-!
# Church-Rosser for `=β` and `=βη`

The definitions of terms, `Step`, `Conv` are in `LeanJudge.Defs`.
One parallel relation `Par β e` covers both systems: the `eta` rule needs `e = true`.
The diamond property is proved directly, by induction on the size of the term.
-/

namespace TBeta

open LeanJudge LeanJudge.Term

/-! ### Shift and substitution -/

theorem sv_lt {n i : Nat} (s : Term) (h : n < i) : Term.subst (var n) s i = var n := by
  simp only [Term.subst]
  rw [if_neg (by omega), if_neg (by omega)]

theorem sv_eq (i : Nat) (s : Term) : Term.subst (var i) s i = shift s i 0 := by
  simp only [Term.subst, if_true]

theorem sv_gt {n i : Nat} (s : Term) (h : i < n) : Term.subst (var n) s i = var (n - 1) := by
  simp only [Term.subst]
  rw [if_neg (by omega), if_pos h]

theorem sh_ge {n c : Nat} (d : Nat) (h : c ≤ n) : shift (var n) d c = var (n + d) := by
  simp only [shift, if_pos h]

theorem sh_lt {n c : Nat} (d : Nat) (h : n < c) : shift (var n) d c = var n := by
  simp only [shift]
  rw [if_neg (by omega)]

/-- Substitution at or above a shift cutoff. -/
theorem shift_subst_ge (t s : Term) (i d c : Nat) (h : c ≤ i) :
    shift (Term.subst t s i) d c = Term.subst (shift t d c) s (i + d) := by
  induction t generalizing i c with
  | var n =>
    rcases Nat.lt_trichotomy n i with h1 | h1 | h1
    · rw [sv_lt s h1]
      by_cases h3 : c ≤ n
      · rw [sh_ge d h3, sv_lt s (by omega)]
      · rw [sh_lt d (by omega), sv_lt s (by omega)]
    · cases h1
      rw [sv_eq, sh_ge d h, sv_eq]
      exact shift_add s n d 0 c (by omega) (by omega)
    · rw [sv_gt s h1, sh_ge d (by omega), sh_ge d (by omega), sv_gt s (by omega)]
      congr 1; omega
  | lam b ih =>
    simp only [Term.subst, shift]
    rw [ih (i + 1) (c + 1) (by omega)]
    congr 2; omega
  | app f a ihf iha => simp only [Term.subst, shift]; rw [ihf i c h, iha i c h]
  | x => rfl

/-- Substitution below a shift cutoff. -/
theorem shift_subst_le (t s : Term) (i d c : Nat) (h : i ≤ c) :
    shift (Term.subst t s i) d c = Term.subst (shift t d (c + 1)) (shift s d (c - i)) i := by
  induction t generalizing i c with
  | var n =>
    rcases Nat.lt_trichotomy n i with h1 | h1 | h1
    · rw [sv_lt s h1, sh_lt d (by omega), sh_lt d (by omega), sv_lt _ h1]
    · cases h1
      rw [sv_eq, sh_lt d (by omega), sv_eq, shift_comm s d n (c - n) 0 (by omega)]
      congr 1; omega
    · by_cases h3 : c + 1 ≤ n
      · rw [sv_gt s h1, sh_ge d (by omega), sh_ge d h3, sv_gt _ (by omega)]
        congr 1; omega
      · rw [sv_gt s h1, sh_lt d (by omega), sh_lt d (by omega), sv_gt _ h1]
  | lam b ih =>
    simp only [Term.subst, shift]
    rw [ih (i + 1) (c + 1) (by omega)]
    congr 3; omega
  | app f a ihf iha => simp only [Term.subst, shift]; rw [ihf i c h, iha i c h]
  | x => rfl

theorem subst_shift_gen (t s : Term) (m k : Nat) (h : k ≤ m) :
    Term.subst (shift t (m + 1) 0) s k = shift t m 0 := by
  have : shift t (m + 1) 0 = shift (shift t m 0) 1 k := by
    rw [shift_add t m 1 0 k (by omega) (by omega)]
  rw [this, subst_shift]

/-- The substitution lemma. -/
theorem subst_subst (t a s : Term) (k i : Nat) :
    Term.subst (Term.subst t a k) s (k + i)
      = Term.subst (Term.subst t s (k + i + 1)) (Term.subst a s i) k := by
  induction t generalizing k with
  | var n =>
    rcases Nat.lt_trichotomy n k with h1 | h1 | h1
    · rw [sv_lt a h1, sv_lt s (by omega), sv_lt s (by omega), sv_lt _ h1]
    · cases h1
      rw [sv_eq, sv_lt s (by omega), sv_eq, shift_subst_ge a s i n 0 (by omega)]
      congr 1; omega
    · rcases Nat.lt_trichotomy n (k + i + 1) with h2 | h2 | h2
      · rw [sv_gt a h1, sv_lt s (by omega), sv_lt s h2, sv_gt _ h1]
      · cases h2
        rw [sv_gt a h1, sv_eq]
        simp only [Nat.add_sub_cancel]
        rw [sv_eq, subst_shift_gen _ _ (k + i) k (by omega)]
      · rw [sv_gt a h1, sv_gt s (by omega), sv_gt s h2, sv_gt _ (by omega)]
  | lam b ih =>
    simp only [Term.subst]
    have := ih (k + 1)
    rw [show k + 1 + i = k + i + 1 by omega] at this
    exact congrArg Term.lam this
  | app f a ihf iha => simp only [Term.subst]; rw [ihf k, iha k]
  | x => rfl

/-- Renaming the top binder to itself. -/
theorem subst_shift_rename (t : Term) (k : Nat) :
    Term.subst (shift t 1 (k + 1)) (var 0) k = t := by
  induction t generalizing k with
  | var n =>
    rcases Nat.lt_trichotomy n k with h1 | h1 | h1
    · rw [sh_lt 1 (by omega), sv_lt _ h1]
    · cases h1
      rw [sh_lt 1 (by omega), sv_eq, sh_ge n (by omega)]
      congr 1; omega
    · rw [sh_ge 1 (by omega), sv_gt _ (by omega)]
      rfl
  | lam b ih => simp only [shift, Term.subst]; rw [ih (k + 1)]
  | app f a ihf iha => simp only [shift, Term.subst]; rw [ihf k, iha k]
  | x => rfl

/-! ### Parallel reduction -/

/-- `Par β e`: the `beta` rule needs `β = true`, the `eta` rule needs `e = true`. -/
inductive Par (β e : Bool) : Term → Term → Prop
  | var (n) : Par β e (var n) (var n)
  | x : Par β e .x .x
  | lam {b b'} : Par β e b b' → Par β e (lam b) (lam b')
  | app {f f' a a'} : Par β e f f' → Par β e a a' → Par β e (app f a) (app f' a')
  | beta {b b' a a'} : β = true → Par β e b b' → Par β e a a' → Par β e (app (lam b) a) (Term.subst b' a' 0)
  | eta {f f'} : e = true → Par β e f f' → Par β e (lam (app (shift f 1 0) (var 0))) f'

theorem par_refl {β e : Bool} (t : Term) : Par β e t t := by
  induction t with
  | var n => exact .var n
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha
  | x => exact .x

theorem par_shift {β e : Bool} {t t' : Term} (h : Par β e t t') (d c : Nat) :
    Par β e (shift t d c) (shift t' d c) := by
  induction h generalizing c with
  | var n => exact par_refl _
  | x => exact .x
  | lam _ ih => exact .lam (ih _)
  | app _ _ ihf iha => exact .app (ihf _) (iha _)
  | @beta b b' a a' hβ _ _ ihb iha =>
    have := shift_subst_le b' a' 0 d c (by omega)
    rw [this]
    exact .beta hβ (ihb _) (iha _)
  | @eta f f' he _ ih =>
    show Par β e (lam (app (shift (shift f 1 0) d (c + 1)) (shift (var 0) d (c + 1)))) _
    rw [sh_lt d (by omega), ← shift_comm f d 1 c 0 (by omega)]
    exact .eta he (ih _)

theorem par_subst {β e : Bool} {b b' a a' : Term} (hb : Par β e b b') (ha : Par β e a a') (i : Nat) :
    Par β e (Term.subst b a i) (Term.subst b' a' i) := by
  induction hb generalizing i with
  | var n =>
    rcases Nat.lt_trichotomy n i with h1 | h1 | h1
    · rw [sv_lt _ h1, sv_lt _ h1]; exact par_refl _
    · cases h1
      rw [sv_eq, sv_eq]
      exact par_shift ha _ _
    · rw [sv_gt _ h1, sv_gt _ h1]; exact par_refl _
  | x => exact .x
  | lam _ ih => exact .lam (ih _)
  | app _ _ ihf iha => exact .app (ihf _) (iha _)
  | @beta c c' d d' hβ _ _ ihc ihd =>
    have := subst_subst c' d' a' 0 i
    rw [Nat.zero_add] at this
    rw [this]
    exact .beta hβ (ihc _) (ihd _)
  | @eta f f' he _ ih =>
    show Par β e (lam (app (Term.subst (shift f 1 0) a (i + 1)) (Term.subst (var 0) a (i + 1)))) _
    rw [sv_lt _ (by omega), ← shift_subst_ge f a i 1 0 (by omega)]
    exact .eta he (ih _)

theorem shift_one_inj {g h : Term} (k : shift g 1 0 = shift h 1 0) : g = h := by
  have := congrArg (fun t => Term.subst t Term.x 0) k
  simpa only [subst_shift] using this

/-- "Index `c` is not free in `s`", in the form `shift (s[c := x]) 1 c = s`, is kept by `Par`. -/
theorem par_noFree {e : Bool} {s s' : Term} (h : Par true e s s') (c : Nat)
    (hs : shift (Term.subst s .x c) 1 c = s) : shift (Term.subst s' .x c) 1 c = s' := by
  induction h generalizing c with
  | var n => exact hs
  | x => exact hs
  | lam _ ih =>
    simp only [Term.subst, shift, Term.lam.injEq] at hs ⊢
    exact ih _ hs
  | app _ _ ihf iha =>
    simp only [Term.subst, shift, Term.app.injEq] at hs ⊢
    exact ⟨ihf _ hs.1, iha _ hs.2⟩
  | @beta b b' a a' _ _ _ ihb iha =>
    simp only [Term.subst, shift, Term.app.injEq, Term.lam.injEq] at hs
    have k := shift_subst_le (Term.subst b' .x (c + 1)) (Term.subst a' .x c) 0 1 c (by omega)
    rw [Nat.sub_zero, ihb _ hs.1, iha _ hs.2] at k
    rw [← k, subst_shift]
  | @eta f f' _ _ ih =>
    refine ih c (shift_one_inj ?_)
    simp only [Term.subst, shift, Term.app.injEq, Term.lam.injEq] at hs
    rw [shift_comm _ 1 1 c 0 (by omega), shift_subst_ge f .x c 1 0 (by omega)]
    exact hs.1

/-- A parallel reduct of a shifted term is a shifted term. -/
theorem par_unshift {e : Bool} {t s' : Term} {c : Nat} (h : Par true e (shift t 1 c) s') :
    ∃ t', s' = shift t' 1 c ∧ Par true e t t' := by
  refine ⟨_, (par_noFree h c (by rw [subst_shift])).symm, ?_⟩
  simpa only [subst_shift] using par_subst h (par_refl .x) c

theorem par_app_inv {e : Bool} {f a s : Term} (h : Par true e (app f a) s) :
    (∃ f' a', s = app f' a' ∧ Par true e f f' ∧ Par true e a a') ∨
    (∃ b b' a', f = lam b ∧ s = subst b' a' 0 ∧ Par true e b b' ∧ Par true e a a') := by
  cases h with
  | app p q => exact .inl ⟨_, _, rfl, p, q⟩
  | beta _ p q => exact .inr ⟨_, _, _, rfl, rfl, p, q⟩

theorem par_var_inv {e : Bool} {n : Nat} {s : Term} (h : Par true e (var n) s) : s = var n := by
  cases h; rfl

/-- What `app (shift g 1 0) (var 0)` can reduce to. -/
theorem par_etaBody_inv {e : Bool} {g s : Term} (h : Par true e (app (shift g 1 0) (var 0)) s) :
    (∃ g', s = app (shift g' 1 0) (var 0) ∧ Par true e g g') ∨
    (∃ c c', g = lam c ∧ s = c' ∧ Par true e c c') := by
  rcases par_app_inv h with ⟨f', a', rfl, p, q⟩ | ⟨b, b', a', hb, rfl, p, q⟩
  · obtain ⟨g', rfl, h2⟩ := par_unshift p
    rw [par_var_inv q]
    exact .inl ⟨g', rfl, h2⟩
  · cases g with
    | lam c =>
      simp only [shift, Term.lam.injEq] at hb
      subst hb
      obtain ⟨c', rfl, h2⟩ := par_unshift p
      rw [par_var_inv q]
      exact .inr ⟨c, c', rfl, subst_shift_rename c' 0, h2⟩
    | var _ => simp [shift] at hb
    | app _ _ => simp [shift] at hb
    | x => simp [shift] at hb

theorem par_lam_inv {e : Bool} {b s : Term} (h : Par true e (lam b) s) :
    (∃ b', s = lam b' ∧ Par true e b b') ∨
    (∃ g, e = true ∧ b = app (shift g 1 0) (var 0) ∧ Par true e g s) := by
  cases h with
  | lam p => exact .inl ⟨_, rfl, p⟩
  | eta he p => exact .inr ⟨_, he, rfl, p⟩

def size : Term → Nat
  | .var _ => 1
  | .x => 1
  | .lam b => size b + 1
  | .app f a => size f + size a + 1

theorem size_shift (t : Term) (d c : Nat) : size (shift t d c) = size t := by
  induction t generalizing c with
  | var _ => rfl
  | x => rfl
  | lam _ ih => simp [shift, size, ih]
  | app _ _ ihf iha => simp [shift, size, ihf, iha]

/-- The diamond property of `Par e`. -/
theorem par_diamond {e : Bool} (n : Nat) : ∀ t, size t ≤ n → ∀ a b, Par true e t a → Par true e t b →
    ∃ w, Par true e a w ∧ Par true e b w := by
  induction n with
  | zero =>
    intro t hs
    cases t <;> simp [size] at hs
  | succ n IH =>
    -- a `lam` rule against an `eta` rule
    have lamEta : ∀ {g b' f1 : Term}, size g ≤ n → Par true e (app (shift g 1 0) (var 0)) b' →
        Par true e g f1 → e = true → ∃ w, Par true e (lam b') w ∧ Par true e f1 w := by
      intro g b' f1 hg p q he
      rcases par_etaBody_inv p with ⟨g', rfl, p'⟩ | ⟨c, c', rfl, rfl, p'⟩
      · obtain ⟨w, h1, h2⟩ := IH g hg _ _ p' q
        exact ⟨w, .eta he h1, h2⟩
      · exact IH _ hg _ _ (.lam p') q
    -- an `app` rule against a `beta` rule, with `lam b` the function
    have appBeta : ∀ {b a f' a' b2 a2 : Term}, size (app (lam b) a) ≤ n + 1 →
        Par true e (lam b) f' → Par true e a a' → Par true e b b2 → Par true e a a2 →
        ∃ w, Par true e (app f' a') w ∧ Par true e (subst b2 a2 0) w := by
      intro b a f' a' b2 a2 hs pf pa pb2 pa2
      cases pf with
      | lam p1 =>
        simp only [size] at hs
        obtain ⟨bw, h1, h2⟩ := IH _ (by omega) _ _ p1 pb2
        obtain ⟨aw, h3, h4⟩ := IH _ (by omega) _ _ pa pa2
        exact ⟨subst bw aw 0, .beta rfl h1 h3, par_subst h2 h4 0⟩
      | @eta g _ he p1 =>
        simp only [size, size_shift] at hs
        have hs0 : size (app g a) ≤ n := by simp only [size]; omega
        have p2 : Par true e (app g a) (subst b2 a2 0) := by
          rcases par_etaBody_inv pb2 with ⟨g', rfl, p'⟩ | ⟨c, c', rfl, rfl, p'⟩
          · simp only [subst]
            rw [subst_shift]
            simp only [if_true, shift_zero]
            exact .app p' pa2
          · exact .beta rfl p' pa2
        exact IH _ hs0 _ _ (.app p1 pa) p2
    intro t hs a b pa pb
    cases t with
    | var k =>
      rw [par_var_inv pa, par_var_inv pb]
      exact ⟨_, .var k, .var k⟩
    | x =>
      cases pa
      cases pb
      exact ⟨_, .x, .x⟩
    | lam body =>
      simp only [size] at hs
      rcases par_lam_inv pa with ⟨b1, rfl, p⟩ | ⟨g, he, rfl, p⟩
      · rcases par_lam_inv pb with ⟨b2, rfl, q⟩ | ⟨g, he, rfl, q⟩
        · obtain ⟨w, h1, h2⟩ := IH _ (by omega) _ _ p q
          exact ⟨_, .lam h1, .lam h2⟩
        · simp only [size, size_shift] at hs
          exact lamEta (by omega) p q he
      · simp only [size, size_shift] at hs
        rcases par_lam_inv pb with ⟨b2, rfl, q⟩ | ⟨g2, _, hg, q⟩
        · obtain ⟨w, h1, h2⟩ := lamEta (by omega) q p he
          exact ⟨w, h2, h1⟩
        · simp only [Term.app.injEq] at hg
          cases shift_one_inj hg.1
          exact IH _ (by omega) _ _ p q
    | app f y =>
      cases pa with
      | app p q =>
        cases pb with
        | app r s =>
          simp only [size] at hs
          obtain ⟨w1, h1, h2⟩ := IH _ (by omega) _ _ p r
          obtain ⟨w2, h3, h4⟩ := IH _ (by omega) _ _ q s
          exact ⟨_, .app h1 h3, .app h2 h4⟩
        | beta _ r s => exact appBeta hs p q r s
      | beta _ p q =>
        cases pb with
        | app r s =>
          obtain ⟨w, h1, h2⟩ := appBeta hs r s p q
          exact ⟨w, h2, h1⟩
        | beta _ r s =>
          simp only [size] at hs
          obtain ⟨w1, h1, h2⟩ := IH _ (by omega) _ _ p r
          obtain ⟨w2, h3, h4⟩ := IH _ (by omega) _ _ q s
          exact ⟨_, par_subst h1 h3 0, par_subst h2 h4 0⟩

/-! ### Church-Rosser -/

/-- Multi-step reduction. -/
inductive Reds (e : Bool) : Term → Term → Prop
  | refl (t) : Reds e t t
  | step {a b c} : Step e a b → Reds e b c → Reds e a c

theorem Reds.trans {e : Bool} {a b c : Term} (h : Reds e a b) (k : Reds e b c) : Reds e a c := by
  induction h with
  | refl => exact k
  | step s _ ih => exact .step s (ih k)

theorem Reds.lam {e : Bool} {a b : Term} (h : Reds e a b) : Reds e (.lam a) (.lam b) := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.lam s) ih

theorem Reds.app {e : Bool} {f g a b : Term} (h : Reds e f g) (k : Reds e a b) :
    Reds e (.app f a) (.app g b) := by
  induction h with
  | step s _ ih => exact .step (.appL _ s) ih
  | refl =>
    induction k with
    | refl => exact .refl _
    | step s _ ih => exact .step (.appR _ s) ih

theorem step_toPar {e : Bool} {a b : Term} (h : Step e a b) : Par true e a b := by
  induction h with
  | root r =>
    cases r with
    | beta => exact .beta rfl (par_refl _) (par_refl _)
    | eta => exact .eta rfl (par_refl _)
  | lam _ ih => exact .lam ih
  | appL a _ ih => exact .app ih (par_refl a)
  | appR f _ ih => exact .app (par_refl f) ih

theorem Par.toReds {e : Bool} {a b : Term} (h : Par true e a b) : Reds e a b := by
  induction h with
  | var => exact .refl _
  | x => exact .refl _
  | lam _ ih => exact ih.lam
  | app _ _ ihf iha => exact ihf.app iha
  | beta _ _ _ ihb iha =>
    exact (Reds.app ihb.lam iha).trans (.step (.root (.beta _ _ _)) (.refl _))
  | eta he _ ih =>
    subst he
    exact .step (.root (.eta _)) ih

theorem par_strip {e : Bool} {t a b : Term} (h : Par true e t a) (k : Reds e t b) :
    ∃ w, Reds e a w ∧ Par true e b w := by
  induction k generalizing a with
  | refl => exact ⟨a, .refl _, h⟩
  | step s _ ih =>
    obtain ⟨w, h1, h2⟩ := par_diamond _ _ (Nat.le_refl _) _ _ h (step_toPar s)
    obtain ⟨z, h3, h4⟩ := ih h2
    exact ⟨z, h1.toReds.trans h3, h4⟩

/-- Confluence of `→β` and of `→βη`. -/
theorem confluence {e : Bool} {t a b : Term} (h : Reds e t a) (k : Reds e t b) :
    ∃ w, Reds e a w ∧ Reds e b w := by
  induction h generalizing b with
  | refl => exact ⟨b, k, .refl _⟩
  | step s _ ih =>
    obtain ⟨w, h1, h2⟩ := par_strip (step_toPar s) k
    obtain ⟨z, h3, h4⟩ := ih h1
    exact ⟨z, h3, h2.toReds.trans h4⟩

/-- **Church-Rosser** for `Conv e`: `=β` when `e = false`, `=βη` when `e = true`. -/
theorem church_rosser {e : Bool} {a b : Term} (h : Conv e a b) :
    ∃ w, Reds e a w ∧ Reds e b w := by
  induction h with
  | refl t => exact ⟨t, .refl _, .refl _⟩
  | step s => exact ⟨_, .step s (.refl _), .refl _⟩
  | symm _ ih =>
    obtain ⟨w, h1, h2⟩ := ih
    exact ⟨w, h2, h1⟩
  | trans _ _ i1 i2 =>
    obtain ⟨w1, a1, b1⟩ := i1
    obtain ⟨w2, a2, b2⟩ := i2
    obtain ⟨z, c1, c2⟩ := confluence b1 a2
    exact ⟨z, a1.trans c1, b2.trans c2⟩

/-- `xⁿ t`. -/
def xp : Nat → Term → Term
  | 0, t => t
  | n + 1, t => .app .x (xp n t)

theorem xp_add (a b : Nat) (t : Term) : xp a (xp b t) = xp (a + b) t := by
  induction a with
  | zero => simp [xp]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [xp]
    rw [ih]

theorem conv_xp {e : Bool} (r : Nat) {a b : Term} (h : Conv e a b) : Conv e (xp r a) (xp r b) := by
  induction r with
  | zero => exact h
  | succ r ih => exact .appR _ ih

end TBeta
