import TBeta.Core2

/-! # Control, not used by the final theorem. The paper cites it. -/

namespace TBeta.G2

open LeanJudge LeanJudge.Term

/-- `a = λy. x (y (λw. y w))`. This is `σ = 0`. -/
def a0 : Term := .lam (.app .x (.app (.var 0) (.lam (.app (.var 1) (.var 0)))))

theorem a0_F : G 0 .F 1 a0 := .mk (.cx (.nf .dv))

/-- At `σ = 0` the family holds a true fixed point: `a a ->> x (a a)`. So `state_not_fix` fails without `σ ≥ 1`. -/
theorem sigma_zero_control : G 0 (.C (.H 1)) 1 (.app a0 a0) ∧ Conv false (.app a0 a0) (.app .x (.app a0 a0)) := by
  refine ⟨.st a0_F a0_F, ?_⟩
  have s1 : Step false (.app a0 a0) (.app .x (.app a0 (.lam (.app a0 (.var 0))))) := by
    have := Step.root (e := false) (Root.beta false (.app .x (.app (.var 0) (.lam (.app (.var 1) (.var 0))))) a0)
    simpa [a0, Term.subst, LeanJudge.Term.shift] using this
  have s2 : Step false (.lam (.app a0 (.var 0))) a0 := by
    have := Step.lam (e := false) (Step.root (Root.beta false (.app .x (.app (.var 0) (.lam (.app (.var 1) (.var 0))))) (.var 0)))
    simpa [a0, Term.subst, LeanJudge.Term.shift] using this
  exact .trans (.step s1) (.step (.appR _ (.appR _ s2)))

end TBeta.G2
