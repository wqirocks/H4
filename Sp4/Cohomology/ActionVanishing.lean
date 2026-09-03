import Sp4.Cohomology.BoundedAlternation
import Sp4.Cohomology.MeasurableResolution

/-!
# Vanishing of the normalized bounded projective-action complex

This is the purely logical assembly of the article's two comparison arguments.
The ordinary quotient is exhausted by the affine classes `theta ell`; every
nonzero such class has no bounded representative, whereas Burger--Monod
alternation makes the bounded-to-measurable comparison injective.  Therefore the
bounded quotient is zero.
-/

namespace Sp4
namespace Pfaffian

noncomputable section

/-- The normalized degree-four bounded projective-action cohomology vanishes. -/
theorem boundedH4_vanishes
    (BM : BoundedAlternationInterface)
    (I : ProjectiveResolutionInterface) :
    ∀ a : BoundedH4, a = 0 := by
  intro a
  obtain ⟨ell, hell⟩ := I.theta_surjective (comparison a)
  have hell0 : ell = 0 := by
    by_contra hne
    exact theta_not_mem_range_comparison ell hne ⟨a, hell.symm⟩
  apply comparison_injective BM
  simpa [hell0] using hell.symm

/-- Exactness of the concrete bounded Pfaffian complex in degree four. -/
theorem bounded_pfaffian_exact
    (BM : BoundedAlternationInterface)
    (I : ProjectiveResolutionInterface) :
    LinearMap.ker (Einfₗ concreteFace5QuasiMeasurePreserving) =
      LinearMap.range (Dinfₗ concreteFace4QuasiMeasurePreserving) :=
  bounded_exact_of_h4_zero (boundedH4_vanishes BM I)

/-- Elementwise form: every bounded five-point cocycle has a bounded
four-point primitive. -/
theorem bounded_pfaffian_primitive
    (BM : BoundedAlternationInterface)
    (I : ProjectiveResolutionInterface)
    (F : Linfty U5 measureU5)
    (hF : Einf concreteFace5QuasiMeasurePreserving F = 0) :
    ∃ f : Linfty U4 measureU4,
      Dinf concreteFace4QuasiMeasurePreserving f = F :=
  bounded_primitive_of_h4_zero (boundedH4_vanishes BM I) F hF

end
end Pfaffian
end Sp4
