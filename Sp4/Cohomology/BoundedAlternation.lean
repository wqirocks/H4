import Sp4.Cohomology.PfaffianComplex
import Sp4.Cohomology.FullAlternation
import Sp4.Measure.Permutation
import Sp4.Pfaffian.MeasurableRigidity

/-!
# Bounded alternation and comparison injectivity

`BoundedAlternationInterface` is the exact coordinate-level portion of the
Burger--Monod bounded alternation theorem consumed by the article: a bounded
cocycle can be changed by a bounded coboundary to an alternating one.  Commutation
of full alternation with the measurable differential is finite simplicial
combinatorics and is proved internally in `FullAlternation`; it is not an external
field.  The remaining argument, including the constant-seven bounded-defect
theorem, is proved here.

External source for this interface: M. Burger and N. Monod, *Continuous bounded
cohomology and applications to rigidity theory*, Geom. Funct. Anal. 12 (2002),
Section 1.7 and Corollary 2.3.2.
-/

namespace Sp4
namespace Pfaffian

noncomputable section

open MeasureTheory OrbitChain

/-- The sole consequence of the Burger--Monod bounded chain homotopy needed
in degree four after transport to normalized Gram coordinates. -/
structure BoundedAlternationInterface : Prop where
  normalForm : ∀ F : BoundedCocycles,
    ∃ (A : BoundedCocycles) (b : Linfty U4 measureU4),
      F.1 = A.1 + Dinfₗ concreteFace4QuasiMeasurePreserving b ∧
      AEMeasurableAlternating5 A.1.1

/-- Burger--Monod alternation plus the article's constant-seven theorem makes
the bounded-to-measurable comparison map injective. -/
theorem comparison_injective
    (BM : BoundedAlternationInterface) :
    Function.Injective comparison := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro a ha
    change comparison a = 0 at ha
    obtain ⟨F, rfl⟩ := BoundedBoundaries.mkQ_surjective a
    change (Submodule.Quotient.mk F : BoundedH4) = 0
    change comparison (Submodule.Quotient.mk F) = 0 at ha
    rw [comparison_mk, Submodule.Quotient.mk_eq_zero] at ha
    rw [Submodule.Quotient.mk_eq_zero]
    change F.1.1 ∈ LinearMap.range
      (D0 concreteFace4QuasiMeasurePreserving) at ha
    rcases ha with ⟨f, hf⟩
    obtain ⟨A, b, hnormal, hAalt⟩ := BM.normalForm F
    have hnormal0 :
        F.1.1 = A.1.1 + D0 concreteFace4QuasiMeasurePreserving b.1 := by
      have h := congrArg Subtype.val hnormal
      change F.1.1 = A.1.1 +
        (Dinfₗ concreteFace4QuasiMeasurePreserving b : L0 U5 measureU5) at h
      rwa [coe_Dinfₗ concreteFace4QuasiMeasurePreserving] at h
    let fA : L0 U4 measureU4 := f - b.1
    have hfA : D0 concreteFace4QuasiMeasurePreserving fA = A.1.1 := by
      dsimp [fA]
      rw [map_sub, hf, hnormal0]
      abel
    let fAlt : L0 U4 measureU4 :=
      FullAlt4 fA
    have hfAltD : D0 concreteFace4QuasiMeasurePreserving fAlt = A.1.1 := by
      exact D0_FullAlt4_eq_of_alternating5 A.1.1 fA hAalt hfA
    have hfAlt : AEMeasurableAlternating
        concreteCoordSymmQuasiMeasurePreserving fAlt := by
      exact FullAlt4_coordinate_alternating fA
    obtain ⟨aBounded, haCoe, _haNorm⟩ :=
      concrete_measurable_bounded_defect fAlt A.1 hfAltD hfAlt
    have hAeq :
        Dinfₗ concreteFace4QuasiMeasurePreserving aBounded = A.1 := by
      apply Subtype.ext
      rw [coe_Dinfₗ concreteFace4QuasiMeasurePreserving, haCoe, hfAltD]
    change F.1 ∈ LinearMap.range
      (Dinfₗ concreteFace4QuasiMeasurePreserving)
    refine ⟨aBounded + b, ?_⟩
    rw [map_add, hAeq]
    exact hnormal.symm
  · exact bot_le

/-- Expanded primitive form of comparison injectivity. -/
theorem bounded_primitive_of_measurable_primitive
    (BM : BoundedAlternationInterface)
    (F : Linfty U5 measureU5)
    (hFcoc : Einfₗ concreteFace5QuasiMeasurePreserving F = 0)
    (f : L0 U4 measureU4)
    (hf : D0 concreteFace4QuasiMeasurePreserving f = F.1) :
    ∃ b : Linfty U4 measureU4,
      Dinfₗ concreteFace4QuasiMeasurePreserving b = F := by
  let z : BoundedCocycles := ⟨F, hFcoc⟩
  have hcomp : comparison (Submodule.Quotient.mk z) = 0 := by
    rw [comparison_mk, Submodule.Quotient.mk_eq_zero]
    change F.1 ∈ LinearMap.range (D0 concreteFace4QuasiMeasurePreserving)
    exact ⟨f, hf⟩
  have hz : (Submodule.Quotient.mk z : BoundedH4) = 0 :=
    comparison_injective BM (hcomp.trans (map_zero comparison).symm)
  rw [Submodule.Quotient.mk_eq_zero] at hz
  exact hz

end
end Pfaffian
end Sp4
