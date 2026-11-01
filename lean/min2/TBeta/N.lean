import TBeta.Alive
import TBeta.Core2

/-! # Part B: if `P[x]` is alive, then `P[x] =β L[a a]`, the term of part C (`shape_of_alive`).

A letter is `Bⁿ C`, `C` is `M`, `B` or `x`. A word is a list of letters. `w[t] = plug w t`, `ŵ = hat w`. -/

namespace TBeta.N

open LeanJudge LeanJudge.Term

/-- The degree: the change of the list length. -/
def Ch.d : Ch → Int
  | .M => 1
  | .B => -1
  | .x => 0

/-- `ŵ`. -/
def hat : List Lt → Term
  | [] => .x
  | [l] => lt l
  | l :: a :: r => .app (.app Atom.B.term (lt l)) (hat (a :: r))

def dg : List Lt → Int
  | [] => 0
  | l :: w => l.2.d + dg w

/-- A letter may act on a list of length `ℓ`. -/
def legal (ℓ : Int) (l : Lt) : Prop :=
  match l.2 with
  | .M => (l.1 : Int) ≤ ℓ
  | .B => (l.1 : Int) + 2 ≤ ℓ
  | .x => (l.1 : Int) = ℓ

/-- **The list rule** as a predicate. The list length at a letter is its height. -/
def Walk : Int → List Lt → Prop
  | _, [] => True
  | ℓ, l :: w => legal ℓ l ∧ Walk (ℓ + l.2.d) w

theorem plug_append (a b : List Lt) (t : Term) : plug (a ++ b) t = plug a (plug b t) := by
  induction a with
  | nil => rfl
  | cons l a ih => simp only [List.cons_append, plug, ih]

theorem dg_append (a b : List Lt) : dg (a ++ b) = dg a + dg b := by
  induction a with
  | nil => simp [dg]
  | cons l a ih => simp only [List.cons_append, dg, ih]; omega

theorem walk_append (a b : List Lt) (ℓ : Int) : Walk ℓ (a ++ b) ↔ Walk ℓ a ∧ Walk (ℓ + dg a) b := by
  induction a generalizing ℓ with
  | nil => simp [Walk, dg]
  | cons l a ih =>
    simp only [List.cons_append, Walk, ih, dg, and_assoc]
    rw [show ℓ + l.2.d + dg a = ℓ + (l.2.d + dg a) by omega]

theorem conv_plug (w : List Lt) {a b : Term} (h : Conv false a b) : Conv false (plug w a) (plug w b) := by
  induction w with
  | nil => exact h
  | cons l w ih => exact Conv.appR _ ih

/-! ### One letter -/

theorem exists_split (s : List Term) (n : Nat) (h : n ≤ s.length) : ∃ s1 r, s = s1 ++ r ∧ s1.length = n :=
  ⟨s.take n, s.drop n, (List.take_append_drop n s).symm, by simp; omega⟩

theorem bp_conv (n : Nat) (C : Term) (f : Term) (s1 r : List Term) (h : s1.length = n) :
    Conv false (sp (.app (bp n C) f) (s1 ++ r)) (sp (.app C (sp f s1)) r) := by
  induction n generalizing f s1 with
  | zero =>
    cases s1 with
    | nil => exact .refl _
    | cons _ _ => simp at h
  | succ n ih =>
    cases s1 with
    | nil => simp at h
    | cons a s1 =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      exact .trans (sp_conv (conv_B false _ _ _) _) (ih (.app f a) s1 h)

theorem bp_short (n : Nat) (C : Term) (f : Term) (s : List Term) (h : s.length < n) :
    ∃ q, Conv false (sp (.app (bp n C) f) s) (.lam q) := by
  induction n generalizing f s with
  | zero => omega
  | succ n ih =>
    cases s with
    | nil => exact B2_lam _ _
    | cons a s =>
      simp only [List.length_cons] at h
      obtain ⟨q, hq⟩ := ih (.app f a) s (by omega)
      exact ⟨q, .trans (sp_conv (conv_B false _ _ _) _) hq⟩

theorem sp_snoc_mid (f z : Term) (s1 r : List Term) : sp f (s1 ++ z :: r) = sp (.app (sp f s1) z) r := by
  rw [sp_append]
  rfl

/-- **One letter of the list rule.** -/
theorem letter {l : Lt} {s : List Term} {f : Term} (hA : Alive (sp (.app (lt l) f) s)) :
    legal s.length l ∧ ∃ e s', Conv false (sp (.app (lt l) f) s) (xp e (sp f s')) ∧
      (s'.length : Int) = s.length + l.2.d := by
  obtain ⟨n, C⟩ := l
  have short : ¬ s.length < n := fun h => by
    obtain ⟨q, hq⟩ := bp_short n C.t f s h
    exact not_alive_lam hq hA
  obtain ⟨s1, r, rfl, rfl⟩ := exists_split s n (by omega)
  have c1 := bp_conv s1.length C.t f s1 r rfl
  have h2 := hA.conv c1
  cases C with
  | M =>
    refine ⟨by show ((s1.length : Nat) : Int) ≤ _; simp; omega, 0, s1 ++ sp f s1 :: r, ?_, by simp [Ch.d]; omega⟩
    rw [sp_snoc_mid]
    exact .trans c1 (sp_conv (conv_M false _) _)
  | B =>
    cases r with
    | nil =>
      obtain ⟨q, hq⟩ := B1_lam (sp f s1)
      exact absurd h2 (not_alive_lam hq)
    | cons p r =>
      cases r with
      | nil =>
        obtain ⟨q, hq⟩ := B2_lam (sp f s1) p
        exact absurd h2 (not_alive_lam hq)
      | cons q r =>
        refine ⟨by show ((s1.length : Nat) : Int) + 2 ≤ _; simp; omega, 0, s1 ++ .app p q :: r, ?_, by simp [Ch.d]; omega⟩
        rw [sp_snoc_mid f (.app p q) s1 r]
        exact .trans c1 (sp_conv (conv_B false _ _ _) _)
  | x =>
    cases r with
    | nil =>
      rw [List.append_nil] at c1 ⊢
      exact ⟨rfl, 1, s1, c1, by simp [Ch.d]⟩
    | cons z r => exact absurd h2 not_alive_two

/-- **The list rule.** -/
theorem list_rule (w : List Lt) (ξ : Term) (s : List Term) (hA : Alive (sp (plug w ξ) s)) :
    Walk s.length w ∧ ∃ e s', Conv false (sp (plug w ξ) s) (xp e (sp ξ s')) ∧ (s'.length : Int) = s.length + dg w := by
  induction w generalizing s with
  | nil => exact ⟨trivial, 0, s, .refl _, by simp [dg]⟩
  | cons l w ih =>
    obtain ⟨h1, e, s', c, h2⟩ := letter hA
    obtain ⟨w2, e2, s2, c2, h3⟩ := ih s' (Alive.peelN _ (hA.conv c))
    refine ⟨⟨h1, h2 ▸ w2⟩, e + e2, s2, ?_, by simp only [dg]; omega⟩
    rw [← xp_add]
    exact .trans c (conv_xp _ c2)

/-- `w` has an `x` letter. -/
def HasX (w : List Lt) : Prop := ∃ n, (n, Ch.x) ∈ w

theorem hasX_cons {l : Lt} {w : List Lt} (h : HasX (l :: w)) (hl : l.2 ≠ .x) : HasX w := by
  obtain ⟨n, hn⟩ := h
  rcases List.mem_cons.1 hn with rfl | h2
  · exact absurd rfl hl
  · exact ⟨n, h2⟩

/-- Two legal walks of a word with an `x` start at the same length. -/
theorem two_walk (w : List Lt) (a b : Int) (ha : Walk a w) (hb : Walk b w) (hx : HasX w) : a = b := by
  induction w generalizing a b with
  | nil =>
    obtain ⟨_, h⟩ := hx
    cases h
  | cons l w ih =>
    obtain ⟨n, C⟩ := l
    cases C with
    | x =>
      have e1 : (n : Int) = a := ha.1
      have e2 : (n : Int) = b := hb.1
      omega
    | M =>
      have := ih _ _ ha.2 hb.2 (hasX_cons hx (by simp))
      simp only [Ch.d] at this
      omega
    | B =>
      have := ih _ _ ha.2 hb.2 (hasX_cons hx (by simp))
      simp only [Ch.d] at this
      omega

/-- From a list of length `≥ 1` there is no `B⁰x` letter, and the length stays `≥ 1`. -/
theorem walk_pos (w : List Lt) (a : Int) (ha : Walk a w) (h1 : 1 ≤ a) : ∀ l ∈ w, l ≠ (0, Ch.x) := by
  induction w generalizing a with
  | nil => intro _ h; cases h
  | cons l w ih =>
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz2
    · rintro rfl
      have : ((0 : Nat) : Int) = a := ha.1
      omega
    · obtain ⟨n, C⟩ := l
      cases C with
      | x => exact ih _ ha.2 (by simp only [Ch.d]; omega) z hz2
      | M => exact ih _ ha.2 (by simp only [Ch.d]; omega) z hz2
      | B =>
        have : (n : Int) + 2 ≤ a := ha.1
        exact ih _ ha.2 (by simp only [Ch.d]; omega) z hz2

/-- From `0`, with no `B⁰M`, the degree is `0`. -/
theorem walk_zero (w : List Lt) (ha : Walk 0 w) (hm : ∀ l ∈ w, l ≠ (0, Ch.M)) : dg w = 0 := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨n, C⟩ := l
    cases C with
    | M =>
      have : (n : Int) ≤ 0 := ha.1
      obtain rfl : n = 0 := by omega
      exact absurd rfl (hm _ (List.mem_cons_self ..))
    | B =>
      have : (n : Int) + 2 ≤ 0 := ha.1
      omega
    | x =>
      have h2 : Walk 0 w := by simpa [Ch.d] using ha.2
      have := ih h2 (fun l hl => hm l (List.mem_cons_of_mem _ hl))
      simp [dg, Ch.d, this]

/-! ### Pop -/

def up (w : List Lt) : List Lt := w.map fun l => (l.1 + 1, l.2)

/-- May be popped: not `B⁰M`, not `B⁰x`. -/
def OK (l : Lt) : Prop := l.1 = 0 → l.2 = .B

def pop1 : Lt → List Lt → List Lt
  | (n + 1, C), R => (n, C) :: R
  | (0, _), R => up R

/-- `W·R`. -/
def pop : List Lt → List Lt → List Lt
  | [], R => R
  | l :: W, R => pop1 l (pop W R)

/-- The number of `B⁰B`. -/
def bz : List Lt → Nat
  | [] => 0
  | (0, .B) :: w => bz w + 1
  | _ :: w => bz w

theorem hat_app (w : List Lt) (t : Term) (h : w ≠ []) : Conv false (.app (hat w) t) (plug w t) := by
  match w, h with
  | [l], _ => exact .refl _
  | l :: a :: r, _ => exact .trans (conv_B false _ _ _) (Conv.appR _ (hat_app (a :: r) t (by simp)))

theorem hat_up (w : List Lt) (h : w ≠ []) : Conv false (.app Atom.B.term (hat w)) (hat (up w)) := by
  match w, h with
  | [l], _ => exact .refl _
  | l :: a :: r, _ => exact .trans (fact_dist false _ _) (Conv.appR _ (hat_up (a :: r) (by simp)))

theorem up_ne {w : List Lt} (h : w ≠ []) : up w ≠ [] := by simpa [up] using h

theorem pop1_ne {l : Lt} {R : List Lt} (h : R ≠ []) : pop1 l R ≠ [] := by
  obtain ⟨n, C⟩ := l
  cases n with
  | zero => exact up_ne h
  | succ n => simp [pop1]

theorem pop_ne (W : List Lt) {R : List Lt} (h : R ≠ []) : pop W R ≠ [] := by
  induction W with
  | nil => exact h
  | cons l W ih => exact pop1_ne ih

/-- **Pop (a).** -/
theorem pop_conv (W R : List Lt) (hW : ∀ l ∈ W, OK l) (hR : R ≠ []) :
    Conv false (plug W (hat R)) (hat (pop W R)) := by
  induction W with
  | nil => exact .refl _
  | cons l W ih =>
    have hT := pop_ne W hR
    refine .trans (Conv.appR _ (ih fun z hz => hW z (List.mem_cons_of_mem _ hz))) ?_
    obtain ⟨n, C⟩ := l
    show Conv false _ (hat (pop1 (n, C) (pop W R)))
    generalize pop W R = T at hT
    cases n with
    | zero =>
      have : C = .B := hW _ (List.mem_cons_self ..) rfl
      subst this
      exact hat_up T hT
    | succ n =>
      cases T with
      | nil => exact absurd rfl hT
      | cons a r => exact .refl _

theorem dg_up (w : List Lt) : dg (up w) = dg w := by
  induction w with
  | nil => rfl
  | cons l w ih => simpa [up, dg] using ih

/-- **Pop (b).** -/
theorem dg_pop (W R : List Lt) (hW : ∀ l ∈ W, OK l) : dg (pop W R) = dg W + bz W + dg R := by
  induction W with
  | nil => simp [pop, dg, bz]
  | cons l W ih =>
    have i := ih fun z hz => hW z (List.mem_cons_of_mem _ hz)
    obtain ⟨n, C⟩ := l
    cases n with
    | zero =>
      have : C = .B := hW _ (List.mem_cons_self ..) rfl
      subst this
      simp only [pop, pop1, dg_up, i, dg, bz, Ch.d]
      omega
    | succ n =>
      simp only [pop, pop1, dg, i, bz]
      omega

/-- All `M` letters have `height − level ≤ ρ`, with the word at heights from `H`. -/
def Bd (ρ : Int) : Int → List Lt → Prop
  | _, [] => True
  | H, l :: w => (l.2 = .M → H - l.1 ≤ ρ) ∧ Bd ρ (H + l.2.d) w

theorem Bd_up (ρ H : Int) (w : List Lt) (h : Bd ρ H w) : Bd ρ (H + 1) (up w) := by
  induction w generalizing H with
  | nil => trivial
  | cons l w ih =>
    refine ⟨fun e => ?_, ?_⟩
    · have := h.1 e
      show H + 1 - ((l.1 + 1 : Nat) : Int) ≤ ρ
      omega
    · have := ih _ h.2
      rwa [show H + l.2.d + 1 = H + 1 + l.2.d by omega] at this

/-- **Pop (c).** -/
theorem Bd_pop (ρ H : Int) (W R : List Lt) (hW : ∀ l ∈ W, OK l) (h1 : Bd ρ H W) (h2 : Bd ρ (H + dg W - 1) R) :
    Bd ρ (H - 1) (pop W R) := by
  induction W generalizing H with
  | nil =>
    show Bd ρ (H - 1) R
    simpa [dg] using h2
  | cons l W ih =>
    have i : Bd ρ (H + l.2.d - 1) (pop W R) :=
      ih _ (fun z hz => hW z (List.mem_cons_of_mem _ hz)) h1.2 (by
        have e : H + l.2.d + dg W - 1 = H + dg (l :: W) - 1 := by simp only [dg]; omega
        rwa [e])
    obtain ⟨n, C⟩ := l
    cases n with
    | zero =>
      have : C = .B := hW _ (List.mem_cons_self ..) rfl
      subst this
      have := Bd_up ρ _ _ i
      simp only [Ch.d] at this
      rwa [show H + -1 - 1 + 1 = H - 1 by omega] at this
    | succ n =>
      refine ⟨fun e => ?_, ?_⟩
      · have : H - ((n + 1 : Nat) : Int) ≤ ρ := h1.1 e
        show H - 1 - (n : Int) ≤ ρ
        omega
      · rwa [show H - 1 + C.d = H + C.d - 1 by omega]

theorem Bd_append (ρ H : Int) (a b : List Lt) : Bd ρ H (a ++ b) ↔ Bd ρ H a ∧ Bd ρ (H + dg a) b := by
  induction a generalizing H with
  | nil => simp [Bd, dg]
  | cons l a ih =>
    simp only [List.cons_append, Bd, ih, dg, and_assoc]
    rw [show H + l.2.d + dg a = H + (l.2.d + dg a) by omega]

theorem exists_Bd (H : Int) (w : List Lt) : ∃ ρ, ∀ ρ', ρ ≤ ρ' → Bd ρ' H w := by
  induction w generalizing H with
  | nil => exact ⟨0, fun _ _ => trivial⟩
  | cons l w ih =>
    obtain ⟨ρ, hρ⟩ := ih (H + l.2.d)
    refine ⟨max ρ (H - l.1), fun ρ' h => ⟨fun _ => by omega, hρ ρ' (by omega)⟩⟩

/-! ### States -/

/-- The last letter is an `x` letter. -/
def LastX : List Lt → Prop
  | [] => False
  | [l] => l.2 = .x
  | _ :: a :: r => LastX (a :: r)

theorem LastX.ne {w : List Lt} (h : LastX w) : w ≠ [] := by
  cases w with
  | nil => exact h.elim
  | cons _ _ => simp

theorem LastX.hasX {w : List Lt} (h : LastX w) : HasX w := by
  induction w with
  | nil => exact h.elim
  | cons l w ih =>
    cases w with
    | nil =>
      obtain ⟨n, C⟩ := l
      have : C = .x := h
      subst this
      exact ⟨n, List.mem_cons_self ..⟩
    | cons a r =>
      obtain ⟨n, hn⟩ := ih h
      exact ⟨n, List.mem_cons_of_mem _ hn⟩

theorem LastX.cons {w : List Lt} (l : Lt) (h : LastX w) : LastX (l :: w) := by
  cases w with
  | nil => exact h.elim
  | cons a r => exact h

theorem LastX.up {w : List Lt} (h : LastX w) : LastX (up w) := by
  induction w with
  | nil => exact h
  | cons l w ih =>
    cases w with
    | nil => exact h
    | cons a r => exact ih h

theorem LastX.pop (W : List Lt) {R : List Lt} (h : LastX R) : LastX (pop W R) := by
  induction W with
  | nil => exact h
  | cons l W ih =>
    obtain ⟨n, C⟩ := l
    cases n with
    | zero => exact ih.up
    | succ n => exact ih.cons _

theorem LastX.of_append {c g : List Lt} {l : Lt} (h : LastX (c ++ l :: g)) (hl : l.2 ≠ .x) : LastX g := by
  induction c with
  | nil =>
    cases g with
    | nil => exact absurd h hl
    | cons a r => exact h
  | cons a c ih =>
    cases c with
    | nil =>
      refine ih ?_
      exact h
    | cons b c => exact ih h

theorem not_alive_hat {V : List Lt} (h : LastX V) : ¬ Alive (hat V) := by
  match V, h with
  | [(0, C)], h =>
    have : C = .x := h
    subst this
    exact not_alive_x
  | [(n + 1, C)], _ =>
    obtain ⟨q, hq⟩ := B1_lam (bp n C.t)
    exact not_alive_lam hq
  | l :: a :: r, _ =>
    obtain ⟨q, hq⟩ := B2_lam (lt l) (hat (a :: r))
    exact not_alive_lam hq

/-- **A state.** -/
structure St (X : Term) (S V : List Lt) : Prop where
  conv : Conv false X (plug S (.app Atom.M.term (hat V)))
  last : LastX V

/-- **Each state has `deg V = 1`.** -/
theorem St.facts {X : Term} {S V : List Lt} (hA : Alive X) (h : St X S V) :
    Walk 0 S ∧ Walk (dg S) V ∧ dg V = 1 ∧ 0 ≤ dg S := by
  have hne := h.last.ne
  have hA1 : Alive (sp (plug S (.app Atom.M.term (hat V))) []) := hA.conv h.conv
  obtain ⟨WS, _, c0, c1, e1⟩ := list_rule S _ [] hA1
  have e1' : (c0.length : Int) = dg S := by simpa using e1
  have hA3 := (Alive.peelN _ (hA1.conv c1)).conv (sp_conv (.trans (conv_M false _) (hat_app V _ hne)) c0)
  obtain ⟨WV, _, s', c3, e3⟩ := list_rule V _ c0 hA3
  have hA4 := Alive.peelN _ (hA3.conv c3)
  cases s' with
  | nil => exact absurd hA4 (not_alive_hat h.last)
  | cons s1 r =>
    obtain ⟨WV2, _⟩ := list_rule V _ r (hA4.conv (sp_conv (hat_app V s1 hne) r))
    have e4 := two_walk V _ _ WV WV2 h.last.hasX
    simp only [List.length_cons] at e3
    exact ⟨by simpa using WS, e1' ▸ WV, by omega, by omega⟩

/-- **The next state.** `S V = S' M h`. -/
theorem St.next {X : Term} {S V S' h : List Lt} (hs : St X S V) (e : S ++ V = S' ++ (0, Ch.M) :: h)
    (hh : ∀ l ∈ h, OK l) : St X S' (pop h V) := by
  have hne := hs.last.ne
  refine ⟨.trans hs.conv ?_, hs.last.pop h⟩
  refine .trans (conv_plug S (.trans (conv_M false _) (hat_app _ _ hne))) ?_
  rw [← plug_append, e, plug_append]
  exact conv_plug S' (Conv.appR _ (pop_conv h V hh hne))

/-- The rightmost `B⁰M`. -/
theorem rsplit (w : List Lt) :
    (∃ c g, w = c ++ (0, Ch.M) :: g ∧ ∀ l ∈ g, l ≠ (0, Ch.M)) ∨ ∀ l ∈ w, l ≠ (0, Ch.M) := by
  induction w with
  | nil => exact .inr (by simp)
  | cons a w ih =>
    rcases ih with ⟨c, g, rfl, hg⟩ | h
    · exact .inl ⟨a :: c, g, rfl, hg⟩
    · by_cases e : a = (0, Ch.M)
      · subst e
        exact .inl ⟨[], w, rfl, h⟩
      · refine .inr fun l hl => ?_
        rcases List.mem_cons.1 hl with rfl | h2
        · exact e
        · exact h l h2

theorem ok_of {w : List Lt} (h1 : ∀ l ∈ w, l ≠ (0, Ch.M)) (h2 : ∀ l ∈ w, l ≠ (0, Ch.x)) : ∀ l ∈ w, OK l := by
  rintro ⟨n, C⟩ hl (rfl : n = 0)
  cases C with
  | B => rfl
  | M => exact absurd rfl (h1 _ hl)
  | x => exact absurd rfl (h2 _ hl)

theorem level_of_bz {g : List Lt} (h : ∀ l ∈ g, OK l) (hb : bz g = 0) : ∀ l ∈ g, 1 ≤ l.1 := by
  induction g with
  | nil => intro _ h; cases h
  | cons l g ih =>
    obtain ⟨n, C⟩ := l
    cases n with
    | zero =>
      have : C = .B := h _ (List.mem_cons_self ..) rfl
      subst this
      simp [bz] at hb
    | succ n =>
      have hb' : bz g = 0 := by
        cases C <;> simpa [bz] using hb
      intro z hz
      rcases List.mem_cons.1 hz with rfl | h2
      · exact Nat.succ_pos n
      · exact ih (fun z hz => h z (List.mem_cons_of_mem _ hz)) hb' z h2

/-- Where the rightmost `B⁰M` of `S V` is. -/
theorem split_where {S V S' h : List Lt} (e : S ++ V = S' ++ (0, Ch.M) :: h) :
    (∃ c, V = c ++ (0, Ch.M) :: h ∧ S' = S ++ c) ∨ (∃ h0, S = S' ++ (0, Ch.M) :: h0 ∧ h = h0 ++ V) := by
  rcases List.append_eq_append_iff.1 e with ⟨c, rfl, e2⟩ | ⟨c, rfl, e2⟩
  · exact .inl ⟨c, e2, rfl⟩
  · cases c with
    | nil =>
      simp only [List.nil_append] at e2
      exact .inl ⟨[], by simpa using e2.symm, by simp⟩
    | cons a c =>
      simp only [List.cons_append, List.cons.injEq] at e2
      obtain ⟨rfl, rfl⟩ := e2
      exact .inr ⟨c, rfl, rfl⟩

/-- **The run stops.** -/
theorem run {X : Term} (hA : Alive X) (ρ : Int) : ∀ (a n : Nat) (S V : List Lt), St X S V → Bd ρ 0 S → Bd ρ (dg S) V →
    dg S ≤ ρ → ρ - dg S ≤ a → S.length ≤ n →
    ∃ S c g, St X S (c ++ (0, Ch.M) :: g) ∧ ∀ l ∈ g, 1 ≤ l.1 := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a iha =>
    intro n
    induction n using Nat.strongRecOn with
    | ind n ihn =>
      intro S V hs bS bV hE ha hn
      obtain ⟨wS, wV, dV, E0⟩ := hs.facts hA
      have wA : Walk 0 (S ++ V) := (walk_append _ _ _).2 ⟨wS, by simpa using wV⟩
      have bA : Bd ρ 0 (S ++ V) := (Bd_append _ _ _ _).2 ⟨bS, by simpa using bV⟩
      have dA : dg (S ++ V) = dg S + dg V := dg_append _ _
      rcases rsplit (S ++ V) with ⟨S', h, e, hh⟩ | hS
      · have w2 := (walk_append _ _ _).1 (e ▸ wA)
        have w0 : (0 : Int) ≤ dg S' := by
          have : ((0 : Nat) : Int) ≤ 0 + dg S' := w2.2.1
          omega
        have hOK := ok_of hh (walk_pos h _ w2.2.2 (by simp only [Ch.d]; omega))
        have ns := hs.next e hOK
        obtain ⟨_, _, dV', _⟩ := ns.facts hA
        rw [dg_pop _ _ hOK] at dV'
        have eA : dg S + dg V = dg S' + 1 + dg h := by
          rw [← dA, e, dg_append]
          simp only [dg, Ch.d]
          omega
        have b2 := (Bd_append _ _ _ _).1 (e ▸ bA)
        have hE' : dg S' ≤ ρ := by
          have := b2.2.1 rfl
          simpa using this
        have bN : Bd ρ (dg S') (pop h V) := by
          have := Bd_pop ρ (dg S' + 1) h V hOK (by simpa [Ch.d] using b2.2.2)
            (by rw [show dg S' + 1 + dg h - 1 = dg S by omega]; exact bV)
          rwa [show dg S' + 1 - 1 = dg S' by omega] at this
        have bS' : Bd ρ 0 S' := b2.1
        by_cases hb : bz h = 0
        · rcases split_where e with ⟨c, rfl, _⟩ | ⟨h0, rfl, _⟩
          · exact ⟨S, c, h, hs, level_of_bz hOK hb⟩
          · have em : (S' ++ (0, Ch.M) :: h0).length = S'.length + h0.length + 1 := by simp; omega
            exact ihn S'.length (by omega) S' _ ns bS' bN hE' (by omega) (Nat.le_refl _)
        · exact iha (a - 1) (by omega) S'.length S' _ ns bS' bN hE' (by omega) (Nat.le_refl _)
      · have := walk_zero _ wA hS
        omega

/-- **The initial state.** `P = S M h`, `M` the rightmost `B⁰M`. The first state is `(S, h·[x])`. -/
theorem St.init {S h : List Lt} (hOK : ∀ l ∈ h, OK l) :
    St (plug (S ++ (0, Ch.M) :: h) .x) S (pop h [(0, Ch.x)]) := by
  refine ⟨?_, LastX.pop h rfl⟩
  rw [plug_append]
  exact conv_plug S (Conv.appR _ (pop_conv h [(0, Ch.x)] hOK (by simp)))

/-- **The run from the initial state.** It ends with `V = c M g`, and all letters of `g` have level `≥ 1`. -/
theorem start {P : List Lt} (hP : ∀ l ∈ P, l.2 ≠ .x) (hA : Alive (plug P .x)) :
    ∃ S c g, St (plug P .x) S (c ++ (0, Ch.M) :: g) ∧ ∀ l ∈ g, 1 ≤ l.1 := by
  have hA0 : Alive (sp (plug P .x) []) := hA
  have WP : Walk 0 P := by simpa using (list_rule P .x [] hA0).1
  have split : ∃ S h, P = S ++ (0, Ch.M) :: h ∧ ∀ l ∈ h, l ≠ (0, Ch.M) := by
    rcases rsplit P with h | h
    · exact h
    · exfalso
      cases P with
      | nil => exact not_alive_x hA
      | cons l w =>
        obtain ⟨n, C⟩ := l
        cases C with
        | x => exact hP _ (List.mem_cons_self ..) rfl
        | B =>
          have : (n : Int) + 2 ≤ 0 := WP.1
          omega
        | M =>
          have : (n : Int) ≤ 0 := WP.1
          obtain rfl : n = 0 := by omega
          exact h _ (List.mem_cons_self ..) rfl
  obtain ⟨S, h, rfl, hh⟩ := split
  have hx0 : ∀ l ∈ h, l ≠ (0, Ch.x) := by
    rintro l hl rfl
    exact hP _ (List.mem_append_right _ (List.mem_cons_of_mem _ hl)) rfl
  have hOK := ok_of hh hx0
  obtain ⟨ρ, hρ⟩ := exists_Bd 0 (S ++ (0, Ch.M) :: h)
  have bP := (Bd_append _ _ _ _).1 (hρ ρ (Int.le_refl _))
  have hE : dg S ≤ ρ := by
    have := bP.2.1 rfl
    simpa using this
  have bV : Bd ρ (dg S) (pop h [(0, Ch.x)]) := by
    have := Bd_pop ρ (dg S + 1) h [(0, Ch.x)] hOK (by simpa [Ch.d] using bP.2.2) ⟨by simp, trivial⟩
    rwa [show dg S + 1 - 1 = dg S by omega] at this
  exact run hA ρ (ρ - dg S).toNat _ S _ (St.init hOK) bP.1 bV hE (by omega) (Nat.le_refl _)

/-! ### The end: the term of part C -/

theorem shift_plug (w : List Lt) (t : Term) (d c : Nat) : shift (plug w t) d c = plug w (shift t d c) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    show Term.app (shift (lt l) d c) (shift (plug w t) d c) = _
    rw [shift_lt, ih]
    rfl

theorem shift_hat (w : List Lt) (d c : Nat) : shift (hat w) d c = hat w := by
  match w with
  | [] => rfl
  | [l] => exact shift_lt l d c
  | l :: a :: r =>
    show Term.app (.app (shift Atom.B.term d c) (shift (lt l) d c)) (shift (hat (a :: r)) d c) = _
    rw [shift_lt, shift_hat (a :: r)]
    rfl

/-- `g[ξ] z =β u[ξ z]`, for `g = ↑u`. -/
theorem plug_up_app (u : List Lt) (ξ z : Term) : Conv false (.app (plug (up u) ξ) z) (plug u (.app ξ z)) := by
  induction u with
  | nil => exact .refl _
  | cons l u ih => exact .trans (conv_B false _ _ _) (Conv.appR _ ih)

theorem exists_down (g : List Lt) (h : ∀ l ∈ g, 1 ≤ l.1) : ∃ u, g = up u := by
  induction g with
  | nil => exact ⟨[], rfl⟩
  | cons l g ih =>
    obtain ⟨u, rfl⟩ := ih fun z hz => h z (List.mem_cons_of_mem _ hz)
    obtain ⟨n, C⟩ := l
    have : 1 ≤ n := h _ (List.mem_cons_self ..)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨(m, C) :: u, rfl⟩

theorem hasX_of_up {u : List Lt} (h : HasX (up u)) : HasX u := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨⟨m, C⟩, h1, e⟩ := List.mem_map.1 hn
  cases e
  exact ⟨m, h1⟩

theorem two_letters (c g : List Lt) (hg : g ≠ []) : ∃ l a r, c ++ (0, Ch.M) :: g = l :: a :: r := by
  cases c with
  | nil =>
    cases g with
    | nil => exact absurd rfl hg
    | cons a r => exact ⟨_, a, r, rfl⟩
  | cons l c =>
    cases c with
    | nil => exact ⟨l, _, g, rfl⟩
    | cons a c => exact ⟨l, a, _, rfl⟩

theorem nx_pos {u : List Lt} (h : HasX u) : 1 ≤ G2.nx u := by
  obtain ⟨n, hn⟩ := h
  induction u with
  | nil => cases hn
  | cons l u ih =>
    show 1 ≤ l.2.c + G2.nx u
    rcases List.mem_cons.1 hn with rfl | h2
    · exact Nat.le_add_right _ _
    · have := ih h2
      omega

/-- **The last state gives the term of part C.** -/
theorem St.shape {X : Term} {S c g : List Lt} (hs : St X S (c ++ (0, Ch.M) :: g)) (hg : ∀ l ∈ g, 1 ≤ l.1) :
    ∃ u, HasX u ∧ Conv false X (G2.coreW S c u) := by
  obtain ⟨u, rfl⟩ := exists_down g hg
  have hu2 := (hs.last.of_append (l := (0, Ch.M)) (by simp)).ne
  have hxu : HasX u := hasX_of_up (hs.last.of_append (by simp)).hasX
  -- `g[y] =β D_y`
  have hD : Conv false (plug (up u) (.var 0)) (G2.Dy u) := by
    have hlam : ∃ q, Conv false (plug (up u) (.var 0)) (.lam q) := by
      cases u with
      | nil => exact absurd rfl hu2
      | cons l u => exact B2_lam _ _
    obtain ⟨q, hq⟩ := hlam
    refine .trans (conv_eta_exp hq) (Conv.lam ?_)
    rw [shift_plug]
    exact plug_up_app u _ _
  -- `V̂ =β a`
  have hV : Conv false (hat (c ++ (0, Ch.M) :: up u)) (G2.aT c u) := by
    obtain ⟨l0, a0, r0, e⟩ := two_letters c (up u) hu2
    obtain ⟨q, hq⟩ : ∃ q, Conv false (hat (c ++ (0, Ch.M) :: up u)) (.lam q) := by
      rw [e]
      exact B2_lam _ _
    refine .trans (conv_eta_exp hq) (Conv.lam ?_)
    rw [shift_hat]
    refine .trans (hat_app _ _ (by simp)) ?_
    rw [plug_append]
    exact conv_plug c (.trans (conv_M false _) (.trans (Conv.appL _ hD) (Conv.appR _ hD)))
  exact ⟨u, hxu, .trans hs.conv (conv_plug S (.trans (conv_M false _) (.trans (Conv.appL _ hV) (Conv.appR _ hV))))⟩

/-- **Theorem (Shape).** A word `P` over `BⁿB`, `BⁿM` with `P[x]` alive has `P[x] =β L[a a]`,
`a = λy. c[D_y D_y]`, `D_y = λw. u[y w]`, with an `x` letter in `u`. -/
theorem shape_of_alive {P : List Lt} (hP : ∀ l ∈ P, l.2 ≠ .x) (hA : Alive (plug P .x)) :
    ∃ L c u, HasX u ∧ Conv false (plug P .x) (G2.coreW L c u) := by
  obtain ⟨S, c, g, hs, hg⟩ := start hP hA
  obtain ⟨u, hu, hW⟩ := hs.shape hg
  exact ⟨S, c, u, hu, hW⟩

end TBeta.N
