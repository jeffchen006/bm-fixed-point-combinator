/-! # The statement. Read this file to read the final theorem.

De Bruijn lambda terms with one free constant `x`, beta and eta with congruence,
conversion, the combinators by their lambda terms, and `Y : Tree → Term`.
A `Tree` has only combinator atoms at its leaves, so `Y t` is closed by construction. -/

namespace LeanJudge

inductive Term where
  | var : Nat → Term
  | lam : Term → Term
  | app : Term → Term → Term
  | x : Term

namespace Term

/-- Add `d` to the indices `≥ c`. -/
def shift : Term → Nat → Nat → Term
  | var n, d, c => var (if c ≤ n then n + d else n)
  | lam b, d, c => lam (shift b d (c + 1))
  | app f a, d, c => app (shift f d c) (shift a d c)
  | x, _, _ => x

/-- `t[i := s]`, and lower the indices above `i`. -/
def subst : Term → Term → Nat → Term
  | var n, s, i => if n = i then shift s i 0 else if i < n then var (n - 1) else var n
  | lam b, s, i => lam (subst b s (i + 1))
  | app f a, s, i => app (subst f s i) (subst a s i)
  | x, _, _ => x

end Term

open Term

/-- Contraction at the root. Eta is allowed only when `e = true`. -/
inductive Root : Bool → Term → Term → Prop
  | beta (e b a) : Root e (app (lam b) a) (subst b a 0)
  | eta (f) : Root true (lam (app (shift f 1 0) (var 0))) f

/-- One step, at any position. -/
inductive Step (e : Bool) : Term → Term → Prop
  | root {t u} : Root e t u → Step e t u
  | lam {t u} : Step e t u → Step e (lam t) (lam u)
  | appL {f g} (a) : Step e f g → Step e (app f a) (app g a)
  | appR (f) {a b} : Step e a b → Step e (app f a) (app f b)

/-- Conversion: `Conv false` is `=β`, `Conv true` is `=βη`. -/
inductive Conv (e : Bool) : Term → Term → Prop
  | refl (t) : Conv e t t
  | step {t u} : Step e t u → Conv e t u
  | symm {t u} : Conv e t u → Conv e u t
  | trans {t u v} : Conv e t u → Conv e u v → Conv e t v

inductive Atom where
  | B | M | I | W | C | K | S
  deriving DecidableEq, Repr

def Atom.term : Atom → Term
  | .B => lam (lam (lam (app (var 2) (app (var 1) (var 0)))))
  | .M => lam (app (var 0) (var 0))
  | .I => lam (var 0)
  | .W => lam (lam (app (app (var 1) (var 0)) (var 0)))
  | .C => lam (lam (lam (app (app (var 2) (var 0)) (var 1))))
  | .K => lam (lam (var 1))
  | .S => lam (lam (lam (app (app (var 2) (var 0)) (app (var 1) (var 0)))))

/-- An applicative combination of atoms. It has no variable and no `x`. -/
inductive Tree where
  | atom : Atom → Tree
  | app : Tree → Tree → Tree

/-- The lambda term of a combination. -/
def Y : Tree → Term
  | .atom a => a.term
  | .app s t => .app (Y s) (Y t)

/-- `t.over l`: every atom of `t` is in `l`. -/
def Tree.over (l : List Atom) : Tree → Bool
  | .atom a => l.contains a
  | .app s t => s.over l && t.over l

/-! ## Combinatory weak equality, for `system = weak` certificates. -/

inductive CL where
  | atom : Atom → CL
  | x : CL
  | app : CL → CL → CL

namespace CL
local infixl:70 " ⬝ " => CL.app

inductive WRoot : CL → CL → Prop
  | B (a b c) : WRoot (atom .B ⬝ a ⬝ b ⬝ c) (a ⬝ (b ⬝ c))
  | M (a) : WRoot (atom .M ⬝ a) (a ⬝ a)
  | I (a) : WRoot (atom .I ⬝ a) a
  | W (a b) : WRoot (atom .W ⬝ a ⬝ b) (a ⬝ b ⬝ b)
  | C (a b c) : WRoot (atom .C ⬝ a ⬝ b ⬝ c) (a ⬝ c ⬝ b)
  | K (a b) : WRoot (atom .K ⬝ a ⬝ b) a
  | S (a b c) : WRoot (atom .S ⬝ a ⬝ b ⬝ c) (a ⬝ c ⬝ (b ⬝ c))

inductive WStep : CL → CL → Prop
  | root {t u} : WRoot t u → WStep t u
  | appL {f g} (a) : WStep f g → WStep (f ⬝ a) (g ⬝ a)
  | appR (f) {a b} : WStep a b → WStep (f ⬝ a) (f ⬝ b)

/-- `=w`. -/
inductive WConv : CL → CL → Prop
  | refl (t) : WConv t t
  | step {t u} : WStep t u → WConv t u
  | symm {t u} : WConv t u → WConv u t
  | trans {t u v} : WConv t u → WConv u v → WConv t v

/-- The lambda interpretation of a CL term. -/
def term : CL → Term
  | atom a => a.term
  | x => .x
  | app s t => .app s.term t.term

end CL

/-- A combination as a CL term. -/
def Tree.cl : Tree → CL
  | .atom a => .atom a
  | .app s t => .app s.cl t.cl

end LeanJudge
