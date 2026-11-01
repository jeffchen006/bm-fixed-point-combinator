import LeanJudge.Final
import TBeta.CR
/-! # Part A: `Y x = x^q (Y x)` with `Y` over B, M, I and `q ≥ 1`, at `=β` or `=βη`, gives a list of letters
`m_1, …, m_K`, each `BⁿB` or `BⁿM`, with `X =β x^q X` for `X = m_1(…(m_K x))`.

1. `J`: on terms over B, M, x, `=βη` is `=β`.
2. Head reduction. A term that is `βη`-equal to a term with a variable or `x` at the head reaches such a head
   by head steps, after padding.
3. First-argument lemma `first_arg`: it gives the letters. `I` is the empty list. -/

namespace PartA
open LeanJudge LeanJudge.Term TBeta

/-- `Bⁿ a`. -/
def mono : Nat → Atom → Term
  | 0, a => a.term
  | n + 1, a => .app Atom.B.term (mono n a)

/-- `S l z = m_1(…(m_K z))`. -/
def S : List (Nat × Atom) → Term → Term
  | [], z => z
  | m :: l, z => .app (mono m.1 m.2) (S l z)

/-! ## 1. `J`: no η redex in a β reduct of a term over B, M, x.
A body is not a variable, and a body `p y` with `y` a variable has `p = y`. -/

def bodyOK : Term → Prop
  | var _ => False
  | app p (var k) => p = var k
  | _ => True

def J : Term → Prop
  | app f a => J f ∧ J a
  | lam b => J b ∧ bodyOK b
  | _ => True

theorem bodyOK_shift {t : Term} (d c : Nat) (h : bodyOK t) : bodyOK (shift t d c) := by
  cases t with
  | var n => exact h.elim
  | app p q =>
    cases q with
    | var k => cases (h : p = var k); rfl
    | _ => trivial
  | _ => trivial

theorem J_shift {t : Term} (d c : Nat) (h : J t) : J (shift t d c) := by
  induction t generalizing c with
  | var n => trivial
  | x => trivial
  | lam b ih => exact ⟨ih _ h.1, bodyOK_shift _ _ h.2⟩
  | app f a ihf iha => exact ⟨ihf _ h.1, iha _ h.2⟩

theorem bodyOK_subst {t : Term} (a : Term) (i : Nat) (h : bodyOK t) : bodyOK (subst t a i) := by
  cases t with
  | var n => exact h.elim
  | app p q =>
    cases q with
    | var k =>
      cases (h : p = var k)
      show bodyOK (app (subst (var k) a i) (subst (var k) a i))
      cases subst (var k) a i <;> simp [bodyOK]
    | _ => trivial
  | _ => trivial

theorem J_subst {t a : Term} (i : Nat) (ht : J t) (ha : J a) : J (subst t a i) := by
  induction t generalizing i with
  | var n =>
    simp only [subst]
    split
    · exact J_shift _ _ ha
    · split <;> trivial
  | x => trivial
  | lam b ih => exact ⟨ih _ ht.1, bodyOK_subst _ _ ht.2⟩
  | app f c ihf iha => exact ⟨ihf _ ht.1, iha _ ht.2⟩

/-- A β step from a `J` term never gives a variable. -/
theorem step_not_var {t u : Term} (hs : Step false t u) (hJ : J t) (n : Nat) : u ≠ var n := by
  cases hs with
  | root r =>
    cases r with
    | beta e b a =>
      cases b with
      | var _ => exact hJ.1.2.elim
      | _ => simp [subst]
  | lam _ => simp
  | appL _ _ => simp
  | appR _ _ => simp

theorem J_step {t u : Term} (hs : Step false t u) (hJ : J t) : J u := by
  induction hs with
  | root r =>
    cases r with
    | beta e b a => exact J_subst _ hJ.1.1 hJ.2
  | @lam b b' s ih =>
    refine ⟨ih hJ.1, ?_⟩
    have hb := hJ.2
    cases s with
    | root r => cases r with | beta => exact bodyOK_subst _ _ hJ.1.1.2
    | lam _ => trivial
    | appL a s =>
      cases a with
      | var k =>
        cases (hb : _ = var k)
        cases s with | root r => cases r
      | _ => trivial
    | appR f s =>
      rename_i a c
      cases c with
      | var k => exact (step_not_var s hJ.1.2 k rfl).elim
      | _ => trivial
  | appL a _ ih => exact ⟨ih hJ.1, hJ.2⟩
  | appR f _ ih => exact ⟨hJ.1, ih hJ.2⟩

/-- A `J` term has no η redex: every `βη` step from it is a β step. -/
theorem step_no_eta {t u : Term} (hs : Step true t u) (hJ : J t) : Step false t u := by
  induction hs with
  | root r =>
    cases r with
    | beta e b a => exact .root (.beta _ _ _)
    | eta =>
      rename_i f
      have h3 := hJ.2
      cases f <;> simp [bodyOK, shift] at h3
  | lam _ ih => exact .lam (ih hJ.1)
  | appL a _ ih => exact .appL a (ih hJ.1)
  | appR f _ ih => exact .appR f (ih hJ.2)

/-- Along a `βη` reduction from a `J` term, all steps are β steps. -/
theorem reds_no_eta {t u : Term} (h : Reds true t u) (hJ : J t) : Conv false t u := by
  induction h with
  | refl => exact .refl _
  | step s _ ih =>
    have s' := step_no_eta s hJ
    exact .trans (.step s') (ih (J_step s' hJ))

/-- On `J` terms, `=βη` implies `=β`. -/
theorem J_conv {A C : Term} (hA : J A) (hC : J C) (h : Conv true A C) : Conv false A C := by
  obtain ⟨w, h1, h2⟩ := church_rosser h
  exact .trans (reds_no_eta h1 hA) (.symm (reds_no_eta h2 hC))

theorem J_mono (n : Nat) {a : Atom} (h : a = .B ∨ a = .M) : J (mono n a) := by
  have hB : J Atom.B.term := by simp [J, bodyOK, Atom.term]
  induction n with
  | zero => rcases h with rfl | rfl <;> simp [mono, J, bodyOK, Atom.term]
  | succ n ih => exact ⟨hB, ih⟩

theorem J_S {l : List (Nat × Atom)} (h : ∀ m ∈ l, m.2 = .B ∨ m.2 = .M) : J (S l .x) := by
  induction l with
  | nil => trivial
  | cons m l ih =>
    exact ⟨J_mono _ (h m (by simp)), ih fun c hc => h c (by simp [hc])⟩

/-! ## 2. Head reduction -/

inductive NS : Term → Term → Prop
  | beta (b a) : NS (app (lam b) a) (subst b a 0)
  | app {f f'} (a) : NS f f' → NS (app f a) (app f' a)

inductive Run : Nat → Term → Term → Prop
  | zero (t) : Run 0 t t
  | succ {n a b c} : NS a b → Run n b c → Run (n + 1) a c

theorem Run.trans {m n : Nat} {a b c : Term} (h : Run m a b) (k : Run n b c) : Run (m + n) a c := by
  induction h with
  | zero => simpa using k
  | @succ m' _ _ _ s _ ih => rw [show m' + 1 + n = (m' + n) + 1 by omega]; exact .succ s (ih k)

theorem Run.app {n : Nat} {f f' : Term} (a : Term) (h : Run n f f') :
    Run n (.app f a) (.app f' a) := by
  induction h with
  | zero => exact .zero _
  | succ s _ ih => exact .succ (.app a s) ih

/-- A variable or `x` at the head of the spine. -/
inductive VH : Term → Prop
  | var (n) : VH (var n)
  | x : VH .x
  | app {f} (a) : VH f → VH (app f a)

theorem VH.no_ns {t u : Term} (h : VH t) : ¬ NS t u := by
  induction h generalizing u with
  | var n => intro k; cases k
  | x => intro k; cases k
  | app a hf ih =>
    intro k
    cases k with
    | beta b a => cases hf
    | app a s => exact ih s

theorem VH.reds {e : Bool} {t u : Term} (h : VH t) (k : Reds e t u) : VH u := by
  have one : ∀ {t u : Term}, VH t → Step e t u → VH u := by
    intro t u h k
    induction h generalizing u with
    | var n => cases k with | root r => cases r
    | x => cases k with | root r => cases r
    | app a hf ih =>
      cases k with
      | root r => cases r with | beta => cases hf
      | appL _ s => exact .app _ (ih s)
      | appR _ s => exact .app _ hf
  induction k with
  | refl => exact h
  | step s _ ih => exact ih (one h s)

theorem ns_det {t u u' : Term} (h : NS t u) (k : NS t u') : u = u' := by
  induction h generalizing u' with
  | beta b a =>
    cases k with
    | beta => rfl
    | app _ s => cases s
  | app a s ih =>
    cases k with
    | beta => cases s
    | app _ s' => rw [ih s']

/-- The first step of a run to an `x` head is forced. -/
theorem run_step {n : Nat} {t u K : Term} (s : NS t u) (r : Run n t K) (hv : VH K) :
    ∃ m, n = m + 1 ∧ Run m u K := by
  cases r with
  | zero => exact (hv.no_ns s).elim
  | succ s' r' => cases ns_det s s'; exact ⟨_, rfl, r'⟩

/-- A run to an `x` head passes through every shorter run from the same start. -/
theorem run_prefix {j n : Nat} {t t' K : Term} (h : Run j t t') (k : Run n t K) (hv : VH K) :
    ∃ m, n = j + m ∧ Run m t' K := by
  induction h generalizing n with
  | zero => exact ⟨n, by omega, k⟩
  | succ s _ ih =>
    obtain ⟨m, rfl, r⟩ := run_step s k hv
    obtain ⟨m', rfl, r'⟩ := ih r
    exact ⟨m', by omega, r'⟩

theorem lam_stuck {n : Nat} {b K : Term} (r : Run n (.lam b) K) (hv : VH K) : False := by
  cases r with
  | zero => cases hv
  | succ s _ => cases s

theorem ns_subst {t u : Term} (h : NS t u) (s : Term) : NS (subst t s 0) (subst u s 0) := by
  induction h with
  | beta b a =>
    rw [subst_subst b a s 0 0]
    exact .beta _ _
  | app a _ ih => exact .app _ ih

theorem run_subst {n : Nat} {t u : Term} (h : Run n t u) (s : Term) :
    Run n (subst t s 0) (subst u s 0) := by
  induction h with
  | zero => exact .zero _
  | succ k _ ih => exact .succ (ns_subst k _) ih

/-- Internal parallel reduction. -/
inductive Int : Term → Term → Prop
  | var (n) : Int (var n) (var n)
  | x : Int .x .x
  | lam {b b'} : Par true false b b' → Int (lam b) (lam b')
  | app {f f' a a'} : Int f f' → Par true false a a' → Int (app f a) (app f' a')

theorem Int.vh {t u : Term} (h : Int t u) (k : VH u) : VH t := by
  induction h with
  | var n => exact .var n
  | x => exact .x
  | lam _ => cases k
  | app _ _ ih =>
    cases k with
    | app _ hf => exact .app _ (ih hf)

theorem int_subst {K N P Q : Term} (h : Int K N) (hp : Par true false P Q)
    (hl : ∃ n L, Run n P L ∧ Int L Q) :
    ∃ n K', Run n (subst K P 0) K' ∧ Int K' (subst N Q 0) := by
  induction h with
  | var n =>
    cases n with
    | zero => simpa [subst] using hl
    | succ n => exact ⟨_, _, .zero _, by simpa [subst] using .var n⟩
  | x => exact ⟨_, _, .zero _, .x⟩
  | lam h => exact ⟨_, _, .zero _, .lam (par_subst h hp _)⟩
  | app _ ha ih =>
    obtain ⟨m, K', a, b⟩ := ih
    exact ⟨_, _, a.app _, .app b (par_subst ha hp _)⟩

/-- Takahashi's factorization. -/
theorem par_factor {t u : Term} (h : Par true false t u) : ∃ n K, Run n t K ∧ Int K u := by
  induction h with
  | var n => exact ⟨_, _, .zero _, .var _⟩
  | x => exact ⟨_, _, .zero _, .x⟩
  | lam h _ => exact ⟨_, _, .zero _, .lam h⟩
  | app _ ha ih _ =>
    obtain ⟨m, K, a, b⟩ := ih
    exact ⟨_, _, a.app _, .app b ha⟩
  | beta _ hb ha ihb iha =>
    obtain ⟨m, K, a1, a2⟩ := ihb
    obtain ⟨m', K', b1, b2⟩ := int_subst a2 ha iha
    exact ⟨_, K', .succ (.beta _ _) ((run_subst a1 _).trans b1), b2⟩
  | eta he => cases he

theorem int_ns {L u u1 : Term} (h : Int L u) (k : NS u u1) : ∃ L', NS L L' ∧ Par true false L' u1 := by
  induction k generalizing L with
  | beta b a =>
    cases h with
    | app h1 h2 =>
      cases h1 with
      | lam h3 => exact ⟨_, .beta _ _, par_subst h3 h2 _⟩
  | app a _ ih =>
    cases h with
    | app h1 h2 =>
      obtain ⟨L', a1, a2⟩ := ih h1
      exact ⟨_, .app _ a1, .app a2 h2⟩

/-- A head run to an `x` head lifts backward along a parallel β step. -/
theorem par_run_vh {n : Nat} {t u K : Term} (h : Par true false t u) (k : Run n u K) (hv : VH K) :
    ∃ m K', Run m t K' ∧ VH K' := by
  induction k generalizing t with
  | zero =>
    obtain ⟨m, L, a, b⟩ := par_factor h
    exact ⟨m, L, a, b.vh hv⟩
  | succ s _ ih =>
    obtain ⟨m, L, a, b⟩ := par_factor h
    obtain ⟨L', c, d⟩ := int_ns b s
    obtain ⟨m', K', e, f⟩ := ih d hv
    exact ⟨_, K', a.trans (.succ c e), f⟩

/-! ### Application to a list, and η -/

def appsT : Term → List Term → Term
  | f, [] => f
  | f, a :: l => appsT (.app f a) l

theorem appsT_append (f : Term) (l l' : List Term) :
    appsT f (l ++ l') = appsT (appsT f l) l' := by
  induction l generalizing f with
  | nil => rfl
  | cons a l ih => exact ih _

theorem ns_appsT {f f' : Term} (s : NS f f') (l : List Term) : NS (appsT f l) (appsT f' l) := by
  induction l generalizing f f' with
  | nil => exact s
  | cons a l ih => exact ih (.app a s)

theorem run_appsT {n : Nat} {f f' : Term} (s : Run n f f') (l : List Term) :
    Run n (appsT f l) (appsT f' l) := by
  induction l generalizing f f' with
  | nil => exact s
  | cons a l ih => exact ih (s.app a)

theorem vh_appsT {f : Term} (h : VH f) (l : List Term) : VH (appsT f l) := by
  induction l generalizing f with
  | nil => exact h
  | cons a l ih => exact ih (.app a h)

theorem par_appsT {f f' : Term} (s : Par true false f f') (l : List Term) :
    Par true false (appsT f l) (appsT f' l) := by
  induction l generalizing f f' with
  | nil => exact s
  | cons a l ih => exact ih (.app s (par_refl a))

/-- Parallel η. -/
abbrev E := Par false true

/-- A `βη` step is a β step or a parallel η step. -/
theorem step_split {t u : Term} (h : Step true t u) : Step false t u ∨ E t u := by
  induction h with
  | root r =>
    cases r with
    | beta => exact .inl (.root (.beta _ _ _))
    | eta => exact .inr (.eta rfl (par_refl _))
  | lam _ ih => exact ih.imp .lam .lam
  | appL a _ ih => exact ih.imp (.appL a) (.app · (par_refl a))
  | appR f _ ih => exact ih.imp (.appR f) (.app (par_refl f))

inductive EL : List Term → List Term → Prop
  | nil : EL [] []
  | cons {a a' l l'} : E a a' → EL l l' → EL (a :: l) (a' :: l')

/-- **η simulation.** Let `E t u`, with `E`-related lists. If `u ul` reaches a variable head, then so does
`t tl l` for some `l`. Outer induction on the length of the run, inner on `E t u`. -/
theorem eta_run : ∀ (n : Nat) (t u : Term), E t u → ∀ (K : Term) (tl ul : List Term),
    EL tl ul → Run n (appsT u ul) K → VH K →
    ∃ l m K', Run m (appsT t (tl ++ l)) K' ∧ VH K' := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n outer =>
    intro t u hE
    induction hE with
    | var m => exact fun _ tl _ _ _ _ => ⟨[], 0, _, .zero _, vh_appsT (.var m) _⟩
    | x => exact fun _ tl _ _ _ _ => ⟨[], 0, _, .zero _, vh_appsT .x _⟩
    | @app f f' a a' _ ha ihf _ =>
      exact fun K tl ul hl r hv => ihf K (a :: tl) (a' :: ul) (.cons ha hl) r hv
    | beta he => cases he
    | @eta f f' _ _ ih =>
      intro K tl ul hl r hv
      obtain ⟨l, m, K', a, b⟩ := ih K tl ul hl r hv
      have root : ∀ w rest, NS (appsT (lam (app (shift f 1 0) (var 0))) (w :: rest))
          (appsT f (w :: rest)) := by
        intro w rest
        refine ns_appsT ?_ rest
        have : subst (app (shift f 1 0) (var 0)) w 0 = app f w := by simp [subst, subst_shift]
        rw [← this]
        exact .beta _ _
      have a' : Run m (appsT f ((tl ++ l) ++ [.x])) (.app K' .x) := by
        rw [appsT_append]; exact a.app _
      cases h : (tl ++ l) ++ [.x] with
      | nil => simp at h
      | cons w rest =>
        rw [h] at a'
        exact ⟨l ++ [.x], _, _, by rw [← List.append_assoc, h]; exact .succ (root w rest) a', .app _ b⟩
    | @lam b b' hb _ =>
      intro K tl ul hl r hv
      cases hl with
      | nil => exact (lam_stuck r hv).elim
      | @cons a0 a1 tl' ul' ha hl' =>
        obtain ⟨m, rfl, r'⟩ := run_step (ns_appsT (.beta b' a1) ul') r hv
        obtain ⟨l, m', K', x1, x2⟩ := outer m (by omega) _ _ (par_subst hb ha 0) K tl' ul' hl' r' hv
        exact ⟨l, _, K', .succ (ns_appsT (.beta _ _) (tl' ++ l)) x1, x2⟩

/-- Some padding of `t` reaches a variable head. -/
def HR (t : Term) : Prop := ∃ l n K, Run n (appsT t l) K ∧ VH K

theorem forall2_refl (l : List Term) : EL l l := by
  induction l with
  | nil => exact .nil
  | cons a l ih => exact .cons (par_refl a) ih

theorem HR.of_reds {t u : Term} (r : Reds true t u) (h : HR u) : HR t := by
  induction r with
  | refl => exact h
  | step s _ ih =>
    obtain ⟨l, n, K, r, hv⟩ := ih h
    rcases step_split s with b | e
    · obtain ⟨m, K', a, c⟩ := par_run_vh (par_appsT (step_toPar b) _) r hv
      exact ⟨l, m, K', a, c⟩
    · obtain ⟨l', m, K', a, c⟩ := eta_run n _ _ e K l l (forall2_refl _) r hv
      exact ⟨l ++ l', m, K', a, c⟩

/-! ## 3. The first-argument lemma -/

/-- Closed combinations of `B`, `M`, `I`. -/
inductive W where
  | B | M | I
  | app (f a : W)

def W.term : W → Term
  | .B => Atom.B.term
  | .M => Atom.M.term
  | .I => Atom.I.term
  | .app f a => .app f.term a.term

theorem run_conv {n : Nat} {a b : Term} (h : Run n a b) : Conv false a b := by
  have ns : ∀ {a b : Term}, NS a b → Step false a b := by
    intro a b s
    induction s with
    | beta b a => exact .root (.beta _ _ _)
    | app a _ ih => exact .appL a ih
  induction h with
  | zero => exact .refl _
  | succ s _ ih => exact .trans (.step (ns s)) ih

theorem run_B (a b c : Term) (l : List Term) :
    Run 3 (appsT Atom.B.term (a :: b :: c :: l)) (appsT a (.app b c :: l)) := by
  have s1 : NS (.app Atom.B.term a) (.lam (.lam (.app (shift a 2 0) (.app (.var 1) (.var 0))))) := by
    have := NS.beta (.lam (.lam (.app (.var 2) (.app (.var 1) (.var 0))))) a
    simpa [subst, Atom.term] using this
  have s2 : NS (.app (.lam (.lam (.app (shift a 2 0) (.app (.var 1) (.var 0))))) b)
      (.lam (.app (shift a 1 0) (.app (shift b 1 0) (.var 0)))) := by
    have := NS.beta (.lam (.app (shift a 2 0) (.app (.var 1) (.var 0)))) b
    simpa [subst, subst_shift_succ] using this
  have s3 : NS (.app (.lam (.app (shift a 1 0) (.app (shift b 1 0) (.var 0)))) c)
      (.app a (.app b c)) := by
    have := NS.beta (.app (shift a 1 0) (.app (shift b 1 0) (.var 0))) c
    simpa [subst, subst_shift] using this
  exact run_appsT (.succ (.app _ (.app _ s1)) (.succ (.app _ s2) (.succ s3 (.zero _)))) l

theorem run_M (a : Term) (l : List Term) :
    Run 1 (appsT Atom.M.term (a :: l)) (appsT a (a :: l)) := by
  have := NS.beta (.app (.var 0) (.var 0)) a
  simp only [subst, if_true, shift_zero] at this
  exact .succ (ns_appsT this l) (.zero _)

theorem run_I (a : Term) (l : List Term) : Run 1 (appsT Atom.I.term (a :: l)) (appsT a l) := by
  have := NS.beta (.var 0) a
  simp only [subst, if_true, shift_zero] at this
  exact .succ (ns_appsT this l) (.zero _)

/-- With too few arguments the run stops at an abstraction. So `B` has three arguments. -/
theorem B_run {n : Nat} {L : List Term} {K : Term} (r : Run n (appsT Atom.B.term L) K) (hv : VH K) :
    ∃ a b c L' m, L = a :: b :: c :: L' ∧ n = 3 + m ∧ Run m (appsT a (.app b c :: L')) K := by
  match L, r with
  | [], r => exact (lam_stuck r hv).elim
  | [a], r =>
    obtain ⟨m, _, r⟩ := run_step (.beta _ a) r hv
    exact (lam_stuck (by simpa [subst] using r) hv).elim
  | [a, b], r =>
    obtain ⟨m, _, r⟩ := run_step (.app _ (.beta _ a)) r hv
    obtain ⟨m, _, r⟩ := run_step (.beta _ b) (by simpa [subst] using r) hv
    exact (lam_stuck (by simpa [subst] using r) hv).elim
  | a :: b :: c :: l, r =>
    obtain ⟨m, rfl, r'⟩ := run_prefix (run_B a b c l) r hv
    exact ⟨a, b, c, l, m, rfl, rfl, r'⟩

theorem M_run {n : Nat} {L : List Term} {K : Term} (r : Run n (appsT Atom.M.term L) K) (hv : VH K) :
    ∃ a L' m, L = a :: L' ∧ n = 1 + m ∧ Run m (appsT a (a :: L')) K := by
  match L, r with
  | [], r => exact (lam_stuck r hv).elim
  | a :: l, r =>
    obtain ⟨m, rfl, r'⟩ := run_prefix (run_M a l) r hv
    exact ⟨a, l, m, rfl, rfl, r'⟩

theorem I_run {n : Nat} {L : List Term} {K : Term} (r : Run n (appsT Atom.I.term L) K) (hv : VH K) :
    ∃ a L' m, L = a :: L' ∧ n = 1 + m ∧ Run m (appsT a L') K := by
  match L, r with
  | [], r => exact (lam_stuck r hv).elim
  | a :: l, r =>
    obtain ⟨m, rfl, r'⟩ := run_prefix (run_I a l) r hv
    exact ⟨a, l, m, rfl, rfl, r'⟩

/-- A combination has a head step, or it is `B`, `M`, `I`, `B U`, `B U V`. -/
inductive Stuck : W → Prop
  | B : Stuck .B
  | M : Stuck .M
  | I : Stuck .I
  | BU (u) : Stuck (.app .B u)
  | BUV (u v) : Stuck (.app (.app .B u) v)

theorem W.cases' (X : W) :
    (∃ (X' : W) (j : Nat), 0 < j ∧ ∀ l, Run j (appsT X.term l) (appsT X'.term l)) ∨ Stuck X := by
  induction X with
  | B => exact .inr .B
  | M => exact .inr .M
  | I => exact .inr .I
  | app f a ihf _ =>
    rcases ihf with ⟨f', j, hj, h⟩ | p
    · exact .inl ⟨.app f' a, j, hj, fun l => h (a.term :: l)⟩
    · cases p with
      | B => exact .inr (.BU _)
      | M => exact .inl ⟨.app a a, 1, by omega, fun l => run_M a.term l⟩
      | I => exact .inl ⟨a, 1, by omega, fun l => run_I a.term l⟩
      | BU u => exact .inr (.BUV _ _)
      | BUV u v => exact .inl ⟨.app u (.app v a), 3, by omega, fun l => run_B u.term v.term a.term l⟩

/-! ### Words -/

/-- `X` acts as the word `l`. The word of `I` is empty. -/
def Rep (X : W) (l : List (Nat × Atom)) : Prop :=
  (∀ m ∈ l, m.2 = .B ∨ m.2 = .M) ∧ ∀ z, Conv true (.app X.term z) (S l z)

theorem W.shift (X : W) (d c : Nat) : shift X.term d c = X.term := by
  induction X with
  | app f a ihf iha => simp [W.term, Term.shift, ihf, iha]
  | _ => rfl

theorem shift_mono (n : Nat) (a : Atom) (d c : Nat) : shift (mono n a) d c = mono n a := by
  induction n with
  | zero => cases a <;> rfl
  | succ n ih => simp only [mono, Term.shift, ih]; rfl

theorem shift_S (l : List (Nat × Atom)) (z : Term) (d c : Nat) :
    shift (S l z) d c = S l (shift z d c) := by
  induction l with
  | nil => rfl
  | cons m l ih => simp [S, Term.shift, shift_mono, ih]

theorem S_append (l l' : List (Nat × Atom)) (z : Term) : S (l ++ l') z = S l (S l' z) := by
  induction l with
  | nil => rfl
  | cons m l ih => simp [S, ih]

def lift (l : List (Nat × Atom)) : List (Nat × Atom) := l.map fun m => (m.1 + 1, m.2)

theorem S_lift (l : List (Nat × Atom)) (z v : Term) :
    Conv true (.app (S (lift l) z) v) (S l (.app z v)) := by
  induction l with
  | nil => exact .refl _
  | cons m l ih => exact .trans (conv_B _ _ _ _) (Conv.appR _ ih)

theorem Rep.BU {U : W} {l : List (Nat × Atom)} (h : Rep U l) : Rep (.app .B U) (lift l) := by
  refine ⟨fun m hm => ?_, fun z => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm
    exact h.1 c hc
  · have eta : ∀ f : Term, Conv true (.lam (.app (Term.shift f 1 0) (.var 0))) f :=
      fun f => .step (.root (.eta f))
    refine .trans (.symm (eta _)) (.trans (Conv.lam ?_) (eta _))
    rw [shift_S]
    simp only [W.term, Term.shift, W.shift]
    exact .trans (conv_B _ _ _ _) (.trans (h.2 _) (.symm (S_lift l _ _)))

theorem Rep.BUV {U V : W} {l l' : List (Nat × Atom)} (h : Rep U l) (k : Rep V l') :
    Rep (.app (.app .B U) V) (l ++ l') := by
  refine ⟨fun m hm => (List.mem_append.mp hm).elim (h.1 m) (k.1 m), fun z => ?_⟩
  rw [S_append]
  exact .trans (conv_B _ _ _ _) (.trans (Conv.appR _ (k.2 z)) (h.2 _))

/-- **First-argument lemma.** Let `X` be a closed combination and `l` any list of terms. If `X l` runs to a
variable head, then `l` has a first element `a`, the run passes through some `a s`, and `X` acts as a word. -/
theorem first_arg : ∀ (n : Nat) (X : W) (l : List Term) (K : Term), Run n (appsT X.term l) K → VH K →
    ∃ a l' s j m, l = a :: l' ∧ j + m = n ∧ Run j (appsT X.term l) (appsT a s) ∧ Run m (appsT a s) K ∧ ∃ w, Rep X w := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro X l K r hv
    rcases W.cases' X with ⟨X', j, hj, hs⟩ | p
    · obtain ⟨m, rfl, r'⟩ := run_prefix (hs l) r hv
      obtain ⟨a, l', s, j1, m', e, hm, p1, r2, w, hw⟩ := ih m (by omega) X' l K r' hv
      refine ⟨a, l', s, j + j1, m', e, by omega, (hs l).trans p1, r2, w, hw.1, fun z => ?_⟩
      exact .trans (Conv.appL _ (Conv.mono (run_conv (hs [])))) (hw.2 z)
    · cases p with
      | B =>
        obtain ⟨a, b, c, L, m, rfl, rfl, r'⟩ := B_run r hv
        exact ⟨a, _, _, 3, m, rfl, rfl, run_B a b c L, r', [(0, .B)], by simp, fun z => .refl _⟩
      | M =>
        obtain ⟨a, L, m, rfl, rfl, r'⟩ := M_run r hv
        exact ⟨a, _, _, 1, m, rfl, rfl, run_M a L, r', [(0, .M)], by simp, fun z => .refl _⟩
      | I =>
        obtain ⟨a, L, m, rfl, rfl, r'⟩ := I_run r hv
        exact ⟨a, _, _, 1, m, rfl, rfl, run_I a L, r', [], by simp, fun z => conv_I _ _⟩
      | BU U =>
        obtain ⟨_, b, c, L, m, h1, rfl, r'⟩ := B_run (L := U.term :: l) r hv
        injection h1 with ha hl
        subst ha hl
        obtain ⟨_, l', s, j1, m', e, hm, p1, r2, w, hw⟩ := ih m (by omega) U _ K r' hv
        injection e with he
        subst he
        exact ⟨b, _, c :: s, 3 + j1, m', rfl, by omega, (run_B U.term b c L).trans p1, r2, _, hw.BU⟩
      | BUV U V =>
        obtain ⟨_, _, c, L, m, h1, rfl, r'⟩ := B_run (L := U.term :: V.term :: l) r hv
        injection h1 with ha h2
        injection h2 with hb hl
        subst ha hb hl
        obtain ⟨_, l', s, j1, m', e, hm, p1, r2, w, hw⟩ := ih m (by omega) U _ K r' hv
        injection e with he
        subst he
        obtain ⟨_, l2, s2, j2, m2, e2, hm2, p2, r3, w2, hw2⟩ := ih m' (by omega) V (c :: s) K r2 hv
        injection e2 with he2
        subst he2
        exact ⟨c, _, s2, 3 + j1 + j2, m2, rfl, by omega, ((run_B U.term V.term c L).trans p1).trans p2, r3, _, hw.BUV hw2⟩

/-! ## The statement -/

def toW : Tree → W
  | .atom .M => .M
  | .atom .I => .I
  | .atom _ => .B
  | .app s t => .app (toW s) (toW t)

theorem toW_term {t : Tree} (h : t.over [.B, .M, .I] = true) : (toW t).term = Y t := by
  induction t with
  | atom a => cases a <;> first | rfl | (simp [Tree.over] at h)
  | app s t ihs iht =>
    simp only [Tree.over, Bool.and_eq_true] at h
    simp [toW, W.term, Y, ihs h.1, iht h.2]

theorem J_xp {t : Term} (h : J t) (q : Nat) : J (xp q t) := by
  induction q with
  | zero => exact h
  | succ q ih => exact ⟨trivial, ih⟩

theorem VH_xp {t : Term} {q : Nat} (hq : 1 ≤ q) : VH (xp q t) := by
  cases q with
  | zero => omega
  | succ q => exact .app _ .x

/-- **Part A.** -/
theorem partA {e : Bool} {t : Tree} {q : Nat} (ht : t.over [.B, .M, .I] = true) (hq : 1 ≤ q)
    (h : Conv e (.app (Y t) .x) (xp q (.app (Y t) .x))) :
    ∃ l : List (Nat × Atom), (∀ m ∈ l, m.2 = .B ∨ m.2 = .M) ∧ Conv false (S l .x) (xp q (S l .x)) := by
  have h' : Conv true (.app (Y t) .x) (xp q (.app (Y t) .x)) := h.mono
  obtain ⟨D, r1, r2⟩ := church_rosser h'
  obtain ⟨L, n, K, r, hK⟩ := HR.of_reds r1 ⟨[], 0, D, .zero _, VH.reds (VH_xp hq) r2⟩
  rw [show Term.app (Y t) .x = Term.app (toW t).term .x by rw [toW_term ht]] at r
  obtain ⟨_, _, _, _, _, _, _, _, _, l, hl, hr⟩ := first_arg n (toW t) (.x :: L) K r hK
  rw [toW_term ht] at hr
  have hS : Conv true (S l .x) (xp q (S l .x)) :=
    .trans (.symm (hr .x)) (.trans h' (conv_xp q (hr .x)))
  exact ⟨l, hl, J_conv (J_S hl) (J_xp (J_S hl) q) hS⟩

end PartA
