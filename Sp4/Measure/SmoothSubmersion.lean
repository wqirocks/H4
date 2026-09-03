import Mathlib

/-!
# Coordinate criterion for smooth submersions

The normalized configuration spaces used in this development are open subsets of
finite-dimensional complex normed spaces.  On such charts, the ordinary
differential-rank definition is the most economical interface to the classical
submersion theorem.
-/

namespace Sp4

/-- A complex-differentiable map whose Fréchet derivative is onto at `x`.
In finite dimension this is equivalent to the local projection normal form. -/
def HasSurjectiveComplexFDerivAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : E → F) (x : E) : Prop :=
  DifferentiableAt ℂ f x ∧ Function.Surjective (fderiv ℂ f x)

end Sp4
