import LeanJudge.Defs
/-! # The final statements. The definitions are all in `LeanJudge/Defs.lean`.

-/

namespace LeanJudge

/-- `Y t` satisfies the fixed-point equation for every term `M`. `e = false`: `=β`. `e = true`: `=βη`. -/
def IsFixedPointCombinator (e : Bool) (t : Tree) : Prop :=
  ∀ M : Term, Conv e (.app (Y t) M) (.app M (.app (Y t) M))

end LeanJudge
