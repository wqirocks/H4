import Sp4.Measure.ReferenceSix
import Sp4.Measure.FibreKernel

/-!
# Degree-four cohomology of the normalized Pfaffian complex

This file defines the actual almost-everywhere quotient spaces used in the final
argument.  In particular, neither `MeasurableH4` nor `BoundedH4` is an opaque name:
each is the quotient of the kernel of the six-term operator by the range of the
five-term operator.
-/

namespace Sp4
namespace Pfaffian

noncomputable section

open MeasureTheory

/-- The measurable degree-four cocycles in normalized Pfaffian coordinates. -/
def MeasurableCocycles : Submodule ℝ (L0 U5 measureU5) :=
  LinearMap.ker (E0 concreteFace5QuasiMeasurePreserving)

/-- The measurable degree-four coboundaries, regarded inside the cocycles. -/
def MeasurableBoundaries : Submodule ℝ MeasurableCocycles :=
  (LinearMap.range (D0 concreteFace4QuasiMeasurePreserving)).comap
    MeasurableCocycles.subtype

/-- Ordinary measurable degree-four cohomology of the normalized Pfaffian complex. -/
abbrev MeasurableH4 : Type :=
  (MeasurableCocycles : Type) ⧸ MeasurableBoundaries

/-- The essentially bounded degree-four cocycles in normalized coordinates. -/
def BoundedCocycles : Submodule ℝ (Linfty U5 measureU5) :=
  LinearMap.ker (Einfₗ concreteFace5QuasiMeasurePreserving)

/-- The essentially bounded degree-four coboundaries, regarded inside cocycles. -/
def BoundedBoundaries : Submodule ℝ BoundedCocycles :=
  (LinearMap.range (Dinfₗ concreteFace4QuasiMeasurePreserving)).comap
    BoundedCocycles.subtype

/-- Bounded degree-four cohomology of the normalized Pfaffian complex. -/
abbrev BoundedH4 : Type :=
  (BoundedCocycles : Type) ⧸ BoundedBoundaries

/-- Forget essential boundedness at the cochain level. -/
def linftyToL0 : Linfty U5 measureU5 →ₗ[ℝ] L0 U5 measureU5 where
  toFun F := F.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Forget essential boundedness on degree-four cocycles. -/
def comparisonCocycles : BoundedCocycles →ₗ[ℝ] MeasurableCocycles where
  toFun F := ⟨F.1.1, by
    change E0 concreteFace5QuasiMeasurePreserving F.1.1 = 0
    rw [← coe_Einfₗ concreteFace5QuasiMeasurePreserving]
    exact congrArg Subtype.val F.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem comparisonCocycles_maps_boundaries :
    BoundedBoundaries ≤
      MeasurableBoundaries.comap comparisonCocycles := by
  intro F hF
  change F.1.1 ∈ LinearMap.range
    (D0 concreteFace4QuasiMeasurePreserving)
  change F.1 ∈ LinearMap.range
    (Dinfₗ concreteFace4QuasiMeasurePreserving) at hF
  rcases hF with ⟨f, hf⟩
  refine ⟨f.1, ?_⟩
  rw [← coe_Dinfₗ concreteFace4QuasiMeasurePreserving]
  exact congrArg Subtype.val hf

/-- The bounded-to-measurable comparison map on the concrete quotient spaces. -/
def comparison : BoundedH4 →ₗ[ℝ] MeasurableH4 :=
  BoundedBoundaries.mapQ MeasurableBoundaries comparisonCocycles
    comparisonCocycles_maps_boundaries

@[simp]
theorem comparison_mk (F : BoundedCocycles) :
    comparison (Submodule.Quotient.mk F) =
      Submodule.Quotient.mk (comparisonCocycles F) :=
  rfl

/-- Vanishing of the bounded quotient gives exactness of the bounded Pfaffian
complex at its five-point term. -/
theorem bounded_exact_of_h4_zero
    (hzero : ∀ a : BoundedH4, a = 0) :
    LinearMap.ker (Einfₗ concreteFace5QuasiMeasurePreserving) =
      LinearMap.range (Dinfₗ concreteFace4QuasiMeasurePreserving) := by
  apply le_antisymm
  · intro F hF
    let z : BoundedCocycles := ⟨F, hF⟩
    have hz : Submodule.Quotient.mk z = (0 : BoundedH4) := hzero _
    rw [Submodule.Quotient.mk_eq_zero] at hz
    exact hz
  · intro F hF
    rcases hF with ⟨f, rfl⟩
    exact Einf_Dinf concreteFace4QuasiMeasurePreserving
      concreteFace5QuasiMeasurePreserving f

/-- Expanded, elementwise form of bounded exactness. -/
theorem bounded_primitive_of_h4_zero
    (hzero : ∀ a : BoundedH4, a = 0)
    (F : Linfty U5 measureU5)
    (hF : Einf concreteFace5QuasiMeasurePreserving F = 0) :
    ∃ f : Linfty U4 measureU4,
      Dinf concreteFace4QuasiMeasurePreserving f = F := by
  have hF' : F ∈ LinearMap.ker
      (Einfₗ concreteFace5QuasiMeasurePreserving) := hF
  have := (bounded_exact_of_h4_zero hzero).le hF'
  exact this

end
end Pfaffian
end Sp4
