import TBeta.CR

/-! ### Letters: `Bⁿ C`, `C` is `M`, `B` or `x` -/

namespace TBeta.N

open LeanJudge LeanJudge.Term

inductive Ch | M | B | x
  deriving DecidableEq

def Ch.t : Ch → Term
  | .M => Atom.M.term
  | .B => Atom.B.term
  | .x => .x

/-- The number of `x`. -/
def Ch.c : Ch → Nat
  | .x => 1
  | _ => 0

abbrev Lt := Nat × Ch

def bp : Nat → Term → Term
  | 0, t => t
  | n + 1, t => .app Atom.B.term (bp n t)

def lt (l : Lt) : Term := bp l.1 l.2.t

/-- `w[t]`. -/
def plug : List Lt → Term → Term
  | [], t => t
  | l :: w, t => .app (lt l) (plug w t)

theorem shift_lt (l : Lt) (d c : Nat) : shift (lt l) d c = lt l := by
  obtain ⟨n, C⟩ := l
  show shift (bp n C.t) d c = bp n C.t
  induction n with
  | zero => cases C <;> rfl
  | succ n ih =>
    show Term.app (shift Atom.B.term d c) (shift (bp n C.t) d c) = _
    rw [ih]
    rfl

theorem subst_lt (l : Lt) (a : Term) (i : Nat) : Term.subst (lt l) a i = lt l := by
  obtain ⟨n, C⟩ := l
  show Term.subst (bp n C.t) a i = bp n C.t
  induction n with
  | zero => cases C <;> rfl
  | succ n ih =>
    show Term.app (Term.subst Atom.B.term a i) (Term.subst (bp n C.t) a i) = _
    rw [ih]
    rfl

end TBeta.N

/-!
# Part C: a family of terms, one integer, Church-Rosser

`σ` is fixed. A *context* is built by `[]`, `x C`, `λv. C`, `C E`, with `E` any term.
A context has a count: the number of its `x`. The rules `cx`, `cl`, `ca` below are the contexts.

* `F k`: `λu. b`, with `b ∈ B k u`.
* `B k u`: `C[u D]`, `C` of count `k`, `D = λw. C'[u w]`, `C'` of count `σ` (rules `nf`, `dv`).
           `C[s u]`, `C` of count `m`, `s ∈ F (k - m)` (rule `wr`).
* `H i j`: `C[s R]`, `C` of count `m`, `s ∈ F (i - m)`, `R ∈ F j` (rule `st`).

The value of `H i j` is `2σ i - j (j - σ)`. It stays on `→β`, and `x` adds `2σ` to it.
-/

namespace TBeta.G2

open LeanJudge LeanJudge.Term N

/-- What a context holds: a body with head variable `n`; a `D`-body with filler `n w`; a state. -/
inductive Hk where
  | B (n : Nat)
  | D (n w : Nat)
  | H (j : Nat)

/-- The same kind under one more binder. -/
def Hk.up : Hk → Hk
  | .B n => .B (n + 1)
  | .D n w => .D (n + 1) (w + 1)
  | .H j => .H j

inductive Kd where
  | F
  | C (c : Hk)

inductive G (σ : Nat) : Kd → Nat → Term → Prop
  | mk {k b} : G σ (.C (.B 0)) k b → G σ .F k (.lam b)
  | nf {n d} : G σ (.C (.D (n + 1) 0)) σ d → G σ (.C (.B n)) 0 (.app (.var n) (.lam d))
  | wr {n k s} : G σ .F k s → G σ (.C (.B n)) k (.app s (.var n))
  | dv {n w} : G σ (.C (.D n w)) 0 (.app (.var n) (.var w))
  | st {i j s R} : G σ .F i s → G σ .F j R → G σ (.C (.H j)) i (.app s R)
  | cx {c k t} : G σ (.C c) k t → G σ (.C c) (k + 1) (.app .x t)
  | cl {c k t} : G σ (.C c.up) k t → G σ (.C c) k (.lam t)
  | ca {c k t} (e) : G σ (.C c) k t → G σ (.C c) k (.app t e)

/-! ### Stable under substitution and shift -/

/-- The way a variable moves. -/
inductive Mv (a : Term) (i : Nat) : Nat → Nat → Prop
  | lt {n} : n < i → Mv a i n n
  | gt {n} : i < n → Mv a i n (n - 1)
  | eq {r} : a = .var r → Mv a i i (r + i)

theorem Mv.subst {a : Term} {i n n' : Nat} (h : Mv a i n n') : Term.subst (.var n) a i = .var n' := by
  cases h with
  | lt h => exact sv_lt a h
  | gt h => exact sv_gt a h
  | eq e =>
    rw [sv_eq, e]
    simp [shift]

theorem Mv.up {a : Term} {i n n' : Nat} (h : Mv a i n n') : Mv a (i + 1) (n + 1) (n' + 1) := by
  cases h with
  | @lt n h => exact .lt (by omega)
  | @gt n h =>
    have : n - 1 + 1 = n + 1 - 1 := by omega
    rw [this]
    exact .gt (by omega)
  | @eq r e =>
    rw [show r + i + 1 = r + (i + 1) by omega]
    exact .eq e

/-- The kinds before and after a substitution. -/
inductive MK (a : Term) (i : Nat) : Kd → Kd → Prop
  | F : MK a i .F .F
  | B {n n'} : Mv a i n n' → MK a i (.C (.B n)) (.C (.B n'))
  | D {n n' w w'} : Mv a i n n' → Mv a i w w' → MK a i (.C (.D n w)) (.C (.D n' w'))
  | H {j} : MK a i (.C (.H j)) (.C (.H j))

theorem MK.up {a : Term} {i : Nat} {c c' : Hk} (h : MK a i (.C c) (.C c')) : MK a (i + 1) (.C c.up) (.C c'.up) := by
  cases h with
  | B m => exact .B m.up
  | D m1 m2 => exact .D m1.up m2.up
  | H => exact .H

theorem MK.c {a : Term} {i : Nat} {c : Hk} {K' : Kd} (h : MK a i (.C c) K') : ∃ c', K' = .C c' := by
  cases h <;> exact ⟨_, rfl⟩

theorem G.sub {σ : Nat} {K : Kd} {k : Nat} {t : Term} (h : G σ K k t) :
    ∀ (a : Term) (i : Nat) (K' : Kd), MK a i K K' → G σ K' k (Term.subst t a i) := by
  induction h with
  | mk _ ih =>
    intro a i K' hk
    cases hk
    exact .mk (ih a _ _ (.B (.lt (by omega))))
  | nf _ ih =>
    intro a i K' hk
    cases hk with
    | B m =>
      show G σ _ _ (.app (Term.subst (.var _) a i) (.lam (Term.subst _ a (i + 1))))
      rw [m.subst]
      exact .nf (ih a _ _ (.D m.up (.lt (by omega))))
  | wr _ ih =>
    intro a i K' hk
    cases hk with
    | B m =>
      show G σ _ _ (.app (Term.subst _ a i) (Term.subst (.var _) a i))
      rw [m.subst]
      exact .wr (ih a i _ .F)
  | dv =>
    intro a i K' hk
    cases hk with
    | D m1 m2 =>
      show G σ _ _ (.app (Term.subst (.var _) a i) (Term.subst (.var _) a i))
      rw [m1.subst, m2.subst]
      exact .dv
  | st _ _ ih1 ih2 =>
    intro a i K' hk
    cases hk
    exact .st (ih1 a i _ .F) (ih2 a i _ .F)
  | cx _ ih =>
    intro a i K' hk
    obtain ⟨c', rfl⟩ := hk.c
    exact .cx (ih a i _ hk)
  | cl _ ih =>
    intro a i K' hk
    obtain ⟨c', rfl⟩ := hk.c
    exact .cl (ih a (i + 1) _ hk.up)
  | ca e _ ih =>
    intro a i K' hk
    obtain ⟨c', rfl⟩ := hk.c
    exact .ca _ (ih a i _ hk)

def up1 (d c n : Nat) : Nat := if c ≤ n then n + d else n

theorem up1_succ (d c n : Nat) : up1 d (c + 1) (n + 1) = up1 d c n + 1 := by
  simp only [up1]
  by_cases h : c ≤ n
  · rw [if_pos h, if_pos (by omega)]
    omega
  · rw [if_neg h, if_neg (by omega)]

theorem up1_zero (d c : Nat) : up1 d (c + 1) 0 = 0 := by
  simp [up1]

def upH (d c : Nat) : Hk → Hk
  | .B n => .B (up1 d c n)
  | .D n w => .D (up1 d c n) (up1 d c w)
  | .H j => .H j

def upK (d c : Nat) : Kd → Kd
  | .F => .F
  | .C h => .C (upH d c h)

theorem upH_up (d c : Nat) (h : Hk) : upH d (c + 1) h.up = (upH d c h).up := by
  cases h <;> simp [upH, Hk.up, up1_succ]

theorem G.shift {σ : Nat} {K : Kd} {k : Nat} {t : Term} (h : G σ K k t) :
    ∀ (d c : Nat), G σ (upK d c K) k (LeanJudge.Term.shift t d c) := by
  induction h with
  | mk _ ih =>
    intro d c
    have := ih d (c + 1)
    simp only [upK, upH, up1_zero] at this
    exact .mk this
  | nf _ ih =>
    intro d c
    have := ih d (c + 1)
    simp only [upK, upH, up1_zero, up1_succ] at this
    exact .nf this
  | wr _ ih =>
    intro d c
    exact .wr (ih d c)
  | dv =>
    intro d c
    exact .dv
  | st _ _ ih1 ih2 =>
    intro d c
    exact .st (ih1 d c) (ih2 d c)
  | cx _ ih =>
    intro d c
    exact .cx (ih d c)
  | @cl c0 _ _ _ ih =>
    intro d c
    have := ih d (c + 1)
    simp only [upK, upH_up] at this
    exact .cl this
  | ca e _ ih =>
    intro d c
    exact .ca _ (ih d c)

/-! ### Closed under steps -/

def nonH : Kd → Prop
  | .C (.H _) => False
  | _ => True

theorem step_x' {s : Term} : ¬ Step false .x s := by
  intro h
  cases h with
  | root r => cases r

theorem step_var' {n : Nat} {s : Term} : ¬ Step false (.var n) s := by
  intro h
  cases h with
  | root r => cases r

theorem step_app {f a s : Term} (h : Step false (.app f a) s) :
    (∃ b, f = .lam b ∧ s = Term.subst b a 0) ∨ (∃ f', s = .app f' a ∧ Step false f f') ∨
      (∃ a', s = .app f a' ∧ Step false a a') := by
  cases h with
  | root r =>
    cases r
    exact .inl ⟨_, rfl, rfl⟩
  | appL _ p => exact .inr (.inl ⟨_, rfl, p⟩)
  | appR _ p => exact .inr (.inr ⟨_, rfl, p⟩)

theorem step_lam {b s : Term} (h : Step false (.lam b) s) : ∃ b', s = .lam b' ∧ Step false b b' := by
  cases h with
  | root r => cases r
  | lam p => exact ⟨_, rfl, p⟩

/-- A root step on a context redex. -/
theorem ctx_root {σ : Nat} {c : Hk} {k : Nat} {b a : Term} (h : G σ (.C c) k (.lam b)) :
    G σ (.C c) k (Term.subst b a 0) := by
  cases h with
  | cl h1 =>
    refine h1.sub a 0 _ ?_
    cases c with
    | B n => exact .B (by simpa using Mv.gt (a := a) (i := 0) (n := n + 1) (by omega))
    | D n w =>
      exact .D (by simpa using Mv.gt (a := a) (i := 0) (n := n + 1) (by omega))
        (by simpa using Mv.gt (a := a) (i := 0) (n := w + 1) (by omega))
    | H j => exact .H

theorem G.step {σ : Nat} {K : Kd} {k : Nat} {t : Term} (h : G σ K k t) :
    nonH K → ∀ {u : Term}, Step false t u → G σ K k u := by
  induction h with
  | mk _ ih =>
    intro _ u st
    obtain ⟨b', rfl, q⟩ := step_lam st
    exact .mk (ih trivial q)
  | nf h1 ih =>
    intro _ u st
    rcases step_app st with ⟨b, hb, _⟩ | ⟨f', _, q⟩ | ⟨a', rfl, q⟩
    · cases hb
    · exact absurd q step_var'
    · obtain ⟨b', rfl, q2⟩ := step_lam q
      exact .nf (ih trivial q2)
  | wr h1 ih =>
    intro _ u st
    rcases step_app st with ⟨b, rfl, rfl⟩ | ⟨f', rfl, q⟩ | ⟨a', _, q⟩
    · cases h1 with
      | mk h2 => exact h2.sub _ 0 _ (.B (by simpa using Mv.eq (a := .var _) (i := 0) rfl))
    · exact .wr (ih trivial q)
    · exact absurd q step_var'
  | dv =>
    intro _ u st
    rcases step_app st with ⟨b, hb, _⟩ | ⟨f', _, q⟩ | ⟨a', _, q⟩
    · cases hb
    · exact absurd q step_var'
    · exact absurd q step_var'
  | st _ _ _ _ =>
    intro hn
    exact hn.elim
  | cx _ ih =>
    intro hn u st
    rcases step_app st with ⟨b, hb, _⟩ | ⟨f', _, q⟩ | ⟨a', rfl, q⟩
    · cases hb
    · exact absurd q step_x'
    · exact .cx (ih hn q)
  | @cl c _ _ _ ih =>
    intro hn u st
    obtain ⟨b', rfl, q⟩ := step_lam st
    refine .cl (ih ?_ q)
    cases c <;> first | exact trivial | exact hn
  | ca e h1 ih =>
    intro hn u st
    rcases step_app st with ⟨b, rfl, rfl⟩ | ⟨f', rfl, q⟩ | ⟨a', rfl, q⟩
    · exact ctx_root h1
    · exact .ca _ (ih hn q)
    · exact .ca _ h1

/-! ### The value -/

def val (σ i j : Nat) : Int := 2 * σ * i - j * (j - σ)

/-- A `D`-body with `R` for its head variable is a body of `F (c + j)`. -/
theorem G.transD {σ : Nat} {K : Kd} {c : Nat} {t : Term} (h : G σ K c t) {j : Nat} {R : Term} (hR : G σ .F j R) :
    ∀ n w, K = .C (.D n w) → w < n → G σ (.C (.B w)) (c + j) (Term.subst t R n) := by
  induction h with
  | mk _ _ => intro _ _ e; cases e
  | nf _ _ => intro _ _ e; cases e
  | wr _ _ => intro _ _ e; cases e
  | st _ _ _ _ => intro _ _ e; cases e
  | @dv n w =>
    intro n0 w0 e hw
    cases e
    show G σ _ _ (.app (Term.subst (.var n) R n) (Term.subst (.var w) R n))
    rw [sv_eq, sv_lt R hw, Nat.zero_add]
    exact .wr (hR.shift n 0)
  | @cx _ k0 _ _ ih =>
    intro n w e hw
    cases e
    rw [show k0 + 1 + j = k0 + j + 1 by omega]
    exact .cx (ih n w rfl hw)
  | cl _ ih =>
    intro n w e hw
    cases e
    exact .cl (ih (n + 1) (w + 1) rfl (by omega))
  | ca e' _ ih =>
    intro n w e hw
    cases e
    exact .ca _ (ih n w rfl hw)

/-- **The root step.** A body with `R` for its head variable is a state of the same value. -/
theorem G.transB {σ : Nat} {K : Kd} {k : Nat} {t : Term} (h : G σ K k t) {j : Nat} {R : Term} (hR : G σ .F j R) :
    ∀ n, K = .C (.B n) → ∃ i' j', G σ (.C (.H j')) i' (Term.subst t R n) ∧ val σ i' j' = val σ k j := by
  induction h with
  | mk _ _ => intro _ e; cases e
  | dv => intro _ e; cases e
  | st _ _ _ _ => intro _ e; cases e
  | @nf n d h1 _ =>
    intro n0 e
    cases e
    refine ⟨j, j + σ, ?_, ?_⟩
    · show G σ _ _ (.app (Term.subst (.var n) R n) (.lam (Term.subst d R (n + 1))))
      rw [sv_eq]
      have h2 := h1.transD hR _ _ rfl (show 0 < n + 1 by omega)
      rw [Nat.add_comm] at h2
      exact .st (hR.shift n 0) (.mk h2)
    · simp only [val]
      push_cast
      grind
  | @wr n k s h1 _ =>
    intro n0 e
    cases e
    refine ⟨k, j, ?_, rfl⟩
    show G σ _ _ (.app (Term.subst s R n) (Term.subst (.var n) R n))
    rw [sv_eq]
    exact .st (h1.sub R n _ .F) (hR.shift n 0)
  | cx _ ih =>
    intro n e
    cases e
    obtain ⟨i', j', h2, h3⟩ := ih n rfl
    refine ⟨i' + 1, j', .cx h2, ?_⟩
    simp only [val] at h3 ⊢
    push_cast
    grind
  | cl _ ih =>
    intro n e
    cases e
    obtain ⟨i', j', h2, h3⟩ := ih (n + 1) rfl
    exact ⟨i', j', .cl h2, h3⟩
  | ca e' _ ih =>
    intro n e
    cases e
    obtain ⟨i', j', h2, h3⟩ := ih n rfl
    exact ⟨i', j', .ca _ h2, h3⟩

theorem G.stepH {σ : Nat} {K : Kd} {k : Nat} {t : Term} (h : G σ K k t) :
    ∀ j, K = .C (.H j) → ∀ {u : Term}, Step false t u → ∃ i' j', G σ (.C (.H j')) i' u ∧ val σ i' j' = val σ k j := by
  induction h with
  | mk _ _ => intro _ e; cases e
  | nf _ _ => intro _ e; cases e
  | wr _ _ => intro _ e; cases e
  | dv => intro _ e; cases e
  | @st i j0 s R h1 h2 _ _ =>
    intro j e u st
    cases e
    rcases step_app st with ⟨b, rfl, rfl⟩ | ⟨f', rfl, q⟩ | ⟨a', rfl, q⟩
    · cases h1 with
      | mk h3 =>
        obtain ⟨i', j', h4, h5⟩ := h3.transB h2 0 rfl
        exact ⟨i', j', h4, h5⟩
    · exact ⟨i, j0, .st (h1.step trivial q) h2, rfl⟩
    · exact ⟨i, j0, .st h1 (h2.step trivial q), rfl⟩
  | cx _ ih =>
    intro j e u st
    cases e
    rcases step_app st with ⟨b, hb, _⟩ | ⟨f', _, q⟩ | ⟨a', rfl, q⟩
    · cases hb
    · exact absurd q step_x'
    · obtain ⟨i', j', h2, h3⟩ := ih j rfl q
      refine ⟨i' + 1, j', .cx h2, ?_⟩
      simp only [val] at h3 ⊢
      push_cast
      grind
  | cl _ ih =>
    intro j e u st
    cases e
    obtain ⟨b', rfl, q⟩ := step_lam st
    obtain ⟨i', j', h2, h3⟩ := ih j rfl q
    exact ⟨i', j', .cl h2, h3⟩
  | ca e' h1 ih =>
    intro j e u st
    cases e
    rcases step_app st with ⟨b, rfl, rfl⟩ | ⟨f', rfl, q⟩ | ⟨a', rfl, q⟩
    · exact ⟨_, j, ctx_root h1, rfl⟩
    · obtain ⟨i', j', h2, h3⟩ := ih j rfl q
      exact ⟨i', j', .ca _ h2, h3⟩
    · exact ⟨_, j, .ca _ h1, rfl⟩

theorem G.redsH {σ i j : Nat} {t z : Term} (h : G σ (.C (.H j)) i t) (r : Reds false t z) :
    ∃ i' j', G σ (.C (.H j')) i' z ∧ val σ i' j' = val σ i j := by
  induction r generalizing i j with
  | refl => exact ⟨i, j, h, rfl⟩
  | step a _ ih =>
    obtain ⟨i1, j1, h1, e1⟩ := h.stepH j rfl a
    obtain ⟨i2, j2, h2, e2⟩ := ih h1
    exact ⟨i2, j2, h2, e2.trans e1⟩

/-! ### The plain reading: one value per term -/

/-- The number of `x` on the head path. -/
def hx : Term → Nat
  | .lam b => hx b
  | .app .x a => hx a + 1
  | .app f _ => hx f
  | _ => 0

/-- The result of the reading: a free variable, or the count of the first non-variable on the binder chain. -/
inductive Res where
  | v (n : Nat)
  | t (c : Nat)
  | no
  deriving DecidableEq

def low : Res → Res
  | .v 0 => .no
  | .v (n + 1) => .v n
  | r => r

def readArg : Term → Res
  | .var m => .v m
  | a => .t (hx a)

/-- Walk the head path; at the terminal variable, follow its binder to the argument of that binder. -/
def rd : Term → Res
  | .var n => .v n
  | .x => .no
  | .lam b => low (rd b)
  | .app .x a => rd a
  | .app (.var n) _ => .v n
  | .app (.app f g) _ => rd (.app f g)
  | .app (.lam b) a =>
    match rd b with
    | .v 0 => readArg a
    | r => low r

theorem G.ne_x {σ : Nat} {K : Kd} {k : Nat} {t : Term} (h : G σ K k t) : t ≠ .x := by
  cases h <;> simp

theorem hx_app {t : Term} (e : Term) (h : t ≠ .x) : hx (.app t e) = hx t := by
  cases t with
  | x => exact absurd rfl h
  | var _ => rfl
  | lam _ => rfl
  | app _ _ => rfl

/-- The count of a term is its number of `x` on the head path. -/
theorem G.hx {σ : Nat} {K : Kd} {k : Nat} {t : Term} (h : G σ K k t) : TBeta.G2.hx t = k := by
  induction h with
  | mk _ ih => exact ih
  | nf _ _ => rfl
  | @wr _ _ s h1 ih => rw [hx_app _ h1.ne_x, ih]
  | dv => rfl
  | st h1 _ ih _ => rw [hx_app _ h1.ne_x, ih]
  | cx _ ih => simp only [TBeta.G2.hx, ih]
  | cl _ ih => exact ih
  | ca e h1 ih => rw [hx_app _ h1.ne_x, ih]

theorem rd_ca {t : Term} (e : Term) (h : t ≠ .x) (hn : rd t ≠ .no) : rd (.app t e) = rd t := by
  cases t with
  | x => exact absurd rfl h
  | var _ => rfl
  | app _ _ => rfl
  | lam b =>
    simp only [rd] at hn ⊢
    cases hb : rd b with
    | v n =>
      cases n with
      | zero => simp [hb, low] at hn
      | succ n => rfl
    | t c => rfl
    | no => rfl

/-- What the reading says on a kind. -/
def Hk.res : Hk → Res
  | .B n => .v n
  | .D n _ => .v n
  | .H j => .t j

theorem low_up (c : Hk) : low c.up.res = c.res := by
  cases c <;> rfl

theorem res_ne (c : Hk) : c.res ≠ .no := by
  cases c <;> simp [Hk.res]

def rdP : Kd → Term → Prop
  | .F, t => ∀ b, t = .lam b → rd b = .v 0
  | .C c, t => rd t = c.res

/-- The reading of a body is its head variable; the reading of a state is the count of `R`. -/
theorem G.rd {σ : Nat} {K : Kd} {k : Nat} {t : Term} (h : G σ K k t) : rdP K t := by
  induction h with
  | mk _ ih =>
    intro b e
    cases e
    exact ih
  | nf _ _ => rfl
  | dv => rfl
  | wr h1 ih =>
    cases h1
    simp only [rdP, TBeta.G2.rd, ih _ rfl, readArg, Hk.res]
  | st h1 h2 ih _ =>
    cases h1
    cases h2 with
    | mk h4 => simp only [rdP, TBeta.G2.rd, ih _ rfl, readArg, TBeta.G2.hx, h4.hx, Hk.res]
  | cx _ ih => exact ih
  | @cl c _ _ _ ih =>
    show low (TBeta.G2.rd _) = c.res
    rw [show TBeta.G2.rd _ = c.up.res from ih, low_up]
  | @ca c _ _ e h1 ih =>
    have ih' : TBeta.G2.rd _ = c.res := ih
    show TBeta.G2.rd _ = c.res
    rw [rd_ca _ h1.ne_x (by rw [ih']; exact res_ne c), ih']

/-! ### The core theorem -/

theorem G.xp {σ : Nat} {c : Hk} {k : Nat} {t : Term} (h : G σ (.C c) k t) (n : Nat) :
    G σ (.C c) (k + n) (TBeta.xp n t) := by
  induction n with
  | zero => exact h
  | succ n ih => exact .cx ih

/-- **Core theorem.** A state is not `=β` to `x^q` of itself, if `σ ≥ 1` and `q ≥ 1`. -/
theorem state_not_fix {σ i j : Nat} (hσ : 1 ≤ σ) {t : Term} (h : G σ (.C (.H j)) i t) {q : Nat} (hq : 1 ≤ q) :
    ¬ Conv false t (xp q t) := by
  intro hc
  obtain ⟨z, r1, r2⟩ := church_rosser hc
  obtain ⟨i1, j1, h1, e1⟩ := h.redsH r1
  obtain ⟨i2, j2, h2, e2⟩ := (G.xp h q).redsH r2
  have a1 := h1.hx
  have a2 := h2.hx
  have b1 : rd z = .t j1 := h1.rd
  have b2 : rd z = .t j2 := h2.rd
  have ei : i1 = i2 := by omega
  have ej : j1 = j2 := by
    rw [b1] at b2
    injection b2
  subst ei
  subst ej
  have e3 : val σ i j = val σ (i + q) j := e1.symm.trans e2
  simp only [val] at e3
  push_cast at e3
  have h3 : (2 * (σ : Int)) * q = 0 := by grind
  have h4 : (σ : Int) ≥ 1 := by exact_mod_cast hσ
  have h5 : (q : Int) ≥ 1 := by exact_mod_cast hq
  have h6 : 0 < (2 * (σ : Int)) * q := Int.mul_pos (by omega) (by omega)
  omega

/-! ### The seam: letters give contexts -/

theorem G.shift1 {σ : Nat} {c : Hk} {k : Nat} {t : Term} (h : G σ (.C c) k t) :
    G σ (.C c.up) k (LeanJudge.Term.shift t 1 0) := by
  have := h.shift 1 0
  cases c <;> simpa [upK, upH, up1, Hk.up] using this

theorem G.shift2 {σ : Nat} {c : Hk} {k : Nat} {t : Term} (h : G σ (.C c) k t) :
    G σ (.C c.up.up) k (LeanJudge.Term.shift t 2 0) := by
  have := h.shift 2 0
  cases c <;> simpa [upK, upH, up1, Hk.up] using this

theorem Reds.one {a b : Term} (s : Root false a b) : Reds false a b := .step (.root s) (.refl _)

/-- **Seam lemma.** `Bⁿ C t` reduces to the filler `t` in a context of count `C.c`. -/
theorem lt_red {σ : Nat} (l : Lt) :
    ∀ {c : Hk} {k : Nat} {t : Term}, G σ (.C c) k t →
      ∃ t', Reds false (.app (lt l) t) t' ∧ G σ (.C c) (k + l.2.c) t' := by
  obtain ⟨n, C⟩ := l
  induction n with
  | zero =>
    intro c k t h
    cases C with
    | M =>
      refine ⟨.app t t, ?_, .ca _ h⟩
      have := Reds.one (.beta false (.app (.var 0) (.var 0)) t)
      have e : Reds false (.app (.lam (.app (.var 0) (.var 0))) t) (.app t t) := by simpa [Term.subst] using this
      exact e
    | B =>
      refine ⟨.lam (.lam (.app (LeanJudge.Term.shift t 2 0) (.app (.var 1) (.var 0)))), ?_, .cl (.cl (.ca _ h.shift2))⟩
      have := Reds.one (.beta false (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) t)
      have e : Reds false (.app (.lam (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0)))))) t)
          (.lam (.lam (.app (LeanJudge.Term.shift t 2 0) (.app (.var 1) (.var 0))))) := by simpa [Term.subst] using this
      exact e
    | x => exact ⟨_, .refl _, .cx h⟩
  | succ n ih =>
    intro c k t h
    obtain ⟨t', r, h'⟩ := ih (.ca (.var 0) h.shift1)
    refine ⟨.lam t', ?_, .cl h'⟩
    have hs := shift_lt (n, C)
    have hv := subst_lt (n, C)
    have s1 := Reds.one (.beta false (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) (lt (n, C)))
    have s2 := Reds.one (.beta false (.lam (.app (lt (n, C)) (.app (.var 1) (.var 0)))) t)
    have s0 : Reds false (.app (.app Atom.B.term (lt (n, C))) t)
        (.app (.lam (.lam (.app (lt (n, C)) (.app (.var 1) (.var 0))))) t) :=
      Reds.app (show Reds false (.app (.lam (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0)))))) (lt (n, C))) _ by
        simpa [Term.subst, hs] using s1) (.refl _)
    have s2' : Reds false (.app (.lam (.lam (.app (lt (n, C)) (.app (.var 1) (.var 0))))) t)
        (.lam (.app (lt (n, C)) (.app (LeanJudge.Term.shift t 1 0) (.var 0)))) := by
      simpa [Term.subst, hv] using s2
    exact s0.trans (s2'.trans r.lam)

/-- The number of `x` letters. -/
def nx : List Lt → Nat
  | [] => 0
  | l :: w => l.2.c + nx w

theorem plug_red {σ : Nat} (l : List Lt) {c : Hk} {k : Nat} {t : Term} (h : G σ (.C c) k t) :
    ∃ t', Reds false (plug l t) t' ∧ G σ (.C c) (k + nx l) t' := by
  induction l with
  | nil => exact ⟨t, .refl _, h⟩
  | cons u l ih =>
    obtain ⟨t1, r1, h1⟩ := ih
    obtain ⟨t2, r2, h2⟩ := lt_red u h1
    refine ⟨t2, (Reds.app (.refl _) r1).trans r2, ?_⟩
    have e : k + nx (u :: l) = k + nx l + u.2.c := by
      simp only [nx]
      omega
    rw [e]
    exact h2

theorem plug_reds (l : List Lt) {a b : Term} (r : Reds false a b) : Reds false (plug l a) (plug l b) := by
  induction l with
  | nil => exact r
  | cons u l ih => exact Reds.app (.refl _) ih

theorem plug_subst (l : List Lt) (t a : Term) (i : Nat) : Term.subst (plug l t) a i = plug l (Term.subst t a i) := by
  induction l with
  | nil => rfl
  | cons u l ih => simp only [plug, Term.subst, subst_lt, ih]

/-- `D_y = λw. u[y w]`, with `y` the variable bound just outside. -/
def Dy (us : List Lt) : Term := .lam (plug us (.app (.var 1) (.var 0)))

/-- `a = λy. c[D_y D_y]`. -/
def aT (cs us : List Lt) : Term := .lam (plug cs (.app (Dy us) (Dy us)))

/-- `W = L[a a]`. -/
def coreW (ls cs us : List Lt) : Term := plug ls (.app (aT cs us) (aT cs us))

/-- **The input to part C.** `W` reduces to a state with `σ = nx us`. -/
theorem coreW_state (ls cs us : List Lt) :
    ∃ t i j, Reds false (coreW ls cs us) t ∧ G (nx us) (.C (.H j)) i t := by
  -- `D_y` reduces to a `D`-form.
  obtain ⟨d1, rd1, hd1⟩ := plug_red (σ := nx us) us (c := .D 1 0) (k := 0) .dv
  rw [Nat.zero_add] at hd1
  -- `D_y D_y` reduces to `u[y D']`.
  have hnf : G (nx us) (.C (.B 0)) 0 (.app (.var 0) (.lam d1)) := .nf hd1
  obtain ⟨b1, rb1, hb1⟩ := plug_red (σ := nx us) us hnf
  obtain ⟨b2, rb2, hb2⟩ := plug_red (σ := nx us) cs hb1
  have rD : Reds false (Dy us) (.lam d1) := rd1.lam
  have root1 : Reds false (.app (Dy us) (Dy us)) (plug us (.app (.var 0) (Dy us))) := by
    have := Reds.one (.beta false (plug us (.app (.var 1) (.var 0))) (Dy us))
    rw [plug_subst] at this
    simpa [Term.subst, Dy] using this
  have r2 : Reds false (.app (Dy us) (Dy us)) b1 :=
    root1.trans ((plug_reds us (Reds.app (.refl _) rD)).trans rb1)
  have ra : Reds false (aT cs us) (.lam b2) := ((plug_reds cs r2).trans rb2).lam
  have hF : G (nx us) .F _ (.lam b2) := .mk hb2
  obtain ⟨t, rt, ht⟩ := plug_red (σ := nx us) ls (G.st hF hF)
  exact ⟨t, _, _, (plug_reds ls (Reds.app ra ra)).trans rt, ht⟩

theorem reds_conv {a b : Term} (r : Reds false a b) : Conv false a b := by
  induction r with
  | refl t => exact .refl t
  | step s _ ih => exact .trans (.step s) ih

/-- **Part C.** With an `x` letter in `us`, and `q ≥ 1`, `W ≠β x^q W`. -/
theorem coreW_not_fix (ls cs us : List Lt) (hs : 1 ≤ nx us) {q : Nat} (hq : 1 ≤ q) :
    ¬ Conv false (coreW ls cs us) (xp q (coreW ls cs us)) := by
  intro h
  obtain ⟨t, i, j, r, ht⟩ := coreW_state ls cs us
  exact state_not_fix hs ht hq (.trans (.symm (reds_conv r)) (.trans h (conv_xp q (reds_conv r))))

end TBeta.G2
