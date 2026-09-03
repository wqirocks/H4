import Sp4.Cohomology.GroupVanishing

/-!
# Degree-four vanishing for `Sp(4, ℂ)`: theorem assembly

All article-specific algebraic, geometric, measure-theoretic, period, and diagram-
chase arguments occur in the imported modules.  This file exposes the four final
statements in the same order as the paper.  The arguments are explicit interfaces
for the older results which the article cites rather than reproves:

* Burger--Monod bounded alternation;
* the Moore/Austin--Moore/van Est measurable-resolution identifications;
* Blatz's projective-action kernel theorem;
* rank-one continuous bounded-cohomology vanishing.
-/

namespace Sp4

noncomputable section

/-- The affine cocycle gives every ordinary measurable projective-action class,
and gives it uniquely. -/
def ordinaryProjectiveActionH4Equiv
    (I : Pfaffian.ProjectiveResolutionInterface) :
    (ℂ →ₗ[ℝ] ℝ) ≃ₗ[ℝ] Pfaffian.MeasurableH4 :=
  I.thetaEquiv

/-- Vanishing of degree-four bounded projective-action cohomology in normalized
Pfaffian coordinates. -/
theorem boundedProjectiveActionH4_vanishes
    (BM : Pfaffian.BoundedAlternationInterface)
    (I : Pfaffian.ProjectiveResolutionInterface) :
    ∀ a : Pfaffian.BoundedH4, a = 0 :=
  Pfaffian.boundedH4_vanishes BM I

/-- Equality of kernel and image for the concrete bounded operators `E` and `D`. -/
theorem pfaffianDegreeFour_exact
    (BM : Pfaffian.BoundedAlternationInterface)
    (I : Pfaffian.ProjectiveResolutionInterface) :
    LinearMap.ker
        (Pfaffian.Einfₗ Pfaffian.concreteFace5QuasiMeasurePreserving) =
      LinearMap.range
        (Pfaffian.Dinfₗ Pfaffian.concreteFace4QuasiMeasurePreserving) :=
  Pfaffian.bounded_pfaffian_exact BM I

/-- Fully expanded exactness statement on almost-everywhere classes. -/
theorem pfaffianDegreeFour_primitive
    (BM : Pfaffian.BoundedAlternationInterface)
    (I : Pfaffian.ProjectiveResolutionInterface)
    (F : Linfty Pfaffian.U5 Pfaffian.measureU5)
    (hF : Pfaffian.Einf Pfaffian.concreteFace5QuasiMeasurePreserving F = 0) :
    ∃ f : Linfty Pfaffian.U4 Pfaffian.measureU4,
      Pfaffian.Dinf Pfaffian.concreteFace4QuasiMeasurePreserving f = F :=
  Pfaffian.bounded_pfaffian_primitive BM I F hF

/-- Main theorem of the article, for the explicitly defined homogeneous
continuous bounded cohomology quotient of the standard matrix group `Sp(4, ℂ)`. -/
theorem mainDegreeFourVanishing
    (BM : Pfaffian.BoundedAlternationInterface)
    (I : Pfaffian.ProjectiveResolutionInterface)
    (Blatz : BlatzProjectiveActionInterface)
    (rankOne : RankOneBoundedVanishing) :
    ∀ a : ContinuousBounded.H4Sp4C, a = 0 :=
  continuousBoundedH4_sp4_vanishes BM I Blatz rankOne

end
end Sp4
