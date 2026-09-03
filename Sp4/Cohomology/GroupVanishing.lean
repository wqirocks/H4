import Sp4.Cohomology.ActionVanishing
import Sp4.Cohomology.ContinuousBounded

/-!
# Final reduction from the projective action to `Sp(4, ℂ)`

The continuous bounded cohomology groups and the rank-one restriction below are
the concrete quotient and concrete cochain map defined in
`ContinuousBounded.lean`.  Only the kernel identification and rank-one vanishing
remain literature inputs.

Blatz's input is Lemma 6.2.8 of A. Blatz, *The Low-Degree Bounded Cohomology of
Classical Groups*, doctoral dissertation, Karlsruhe Institute of Technology
(2026), DOI 10.5445/IR/1000194533.  Its projective-action target is written here
as the actual bounded cohomology quotient of the measurable projective action.
The separately proved natural-measure cochain equivalence in
`NaturalProjectiveCoordinates.lean` identifies that quotient with Pfaffian
coordinates; it is not part of the literature input.

The rank-one input is
`H_cb^4(SL(2, ℂ); ℝ) = 0`.  The source article derives it from M. Bucher and
A. Savini, *Continuous cochains on Furstenberg boundaries and injectivity of the
comparison map*, arXiv:2510.05333v1 (2025), Theorem 5, together with the compact
dual computation and invariance under the finite central quotient.
-/

namespace Sp4

noncomputable section

open ContinuousBounded

/-- The exact degree-four consequence of Blatz's projective Stiefel spectral
sequence, for the concrete standard restriction map. -/
structure BlatzProjectiveActionInterface where
  kernelEquiv :
    LinearMap.ker rankOneRestrictionH4 ≃ₗ[ℝ]
      ProjectiveAction.NaturalActionBoundedH4

/-- The external rank-one bounded-cohomology vanishing statement. -/
def RankOneBoundedVanishing : Prop :=
  ∀ a : H4SL2C, a = 0

/-- The article's final theorem: fourth continuous bounded cohomology of the
complex rank-two symplectic group vanishes. -/
theorem continuousBoundedH4_sp4_vanishes
    (BM : Pfaffian.BoundedAlternationInterface)
    (I : Pfaffian.ProjectiveResolutionInterface)
    (Blatz : BlatzProjectiveActionInterface)
    (rankOne : RankOneBoundedVanishing) :
    ∀ a : H4Sp4C, a = 0 := by
  intro a
  have hares : rankOneRestrictionH4 a = 0 := rankOne _
  let z : LinearMap.ker rankOneRestrictionH4 := ⟨a, hares⟩
  have hActionZero :
      ∀ b : ProjectiveAction.NaturalActionBoundedH4, b = 0 := by
    intro b
    apply ProjectiveAction.naturalBoundedH4Equiv.symm.injective
    simpa using Pfaffian.boundedH4_vanishes BM I
      (ProjectiveAction.naturalBoundedH4Equiv.symm b)
  have hzimage : Blatz.kernelEquiv z = 0 := hActionZero _
  have hz : z = 0 := Blatz.kernelEquiv.injective (by simpa using hzimage)
  exact congrArg Subtype.val hz

end
end Sp4
