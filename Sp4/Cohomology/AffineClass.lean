import Sp4.Cohomology.PfaffianComplex
import Sp4.Cohomology.NoBoundedRepresentative

/-!
# The affine cocycle as an ordinary cohomology class

The pointwise affine formula is inserted into the genuine `L0` quotient complex.
The period obstruction is then upgraded from a statement about representatives to
a statement about the range of the bounded-to-measurable comparison map.
-/

namespace Sp4
namespace Pfaffian

noncomputable section

open MeasureTheory

/-- The continuous real component of the affine cocycle as an a.e. class. -/
def realComponentL0 (ell : ℂ →ₗ[ℝ] ℝ) : L0 U5 measureU5 :=
  AEEqFun.mk (MeasureChain.realComponentCocycle ell)
    (MeasureChain.realComponentCocycle_stronglyMeasurable ell).aestronglyMeasurable

theorem coeFn_realComponentL0 (ell : ℂ →ₗ[ℝ] ℝ) :
    (realComponentL0 ell : U5 → ℝ) =ᵐ[measureU5]
      MeasureChain.realComponentCocycle ell :=
  AEEqFun.coeFn_mk _ _

/-- Formation of the real scalar component is linear already at cochain level. -/
def realComponentL0ₗ : (ℂ →ₗ[ℝ] ℝ) →ₗ[ℝ] L0 U5 measureU5 where
  toFun := realComponentL0
  map_add' ell eta := by
    apply AEEqFun.ext
    filter_upwards [coeFn_realComponentL0 (ell + eta),
      coeFn_realComponentL0 ell, coeFn_realComponentL0 eta,
      AEEqFun.coeFn_add (realComponentL0 ell) (realComponentL0 eta)] with
        q hsum hell heta hadd
    rw [hsum, hadd]
    simp only [Pi.add_apply]
    rw [hell, heta]
    simp [MeasureChain.realComponentCocycle]
  map_smul' a ell := by
    apply AEEqFun.ext
    filter_upwards [coeFn_realComponentL0 (a • ell),
      coeFn_realComponentL0 ell,
      AEEqFun.coeFn_smul a (realComponentL0 ell)] with q hsmul hell hout
    rw [hsmul]
    change MeasureChain.realComponentCocycle (a • ell) q =
      (a • realComponentL0 ell : L0 U5 measureU5) q
    rw [hout]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hell]
    simp [MeasureChain.realComponentCocycle]

theorem E_realComponentCocycle_apply (ell : ℂ →ₗ[ℝ] ℝ) (q : U6) :
    E (MeasureChain.realComponentCocycle ell) q = 0 := by
  have h := congrArg ell (AffineCocycle.E_reducedR_apply q)
  simpa only [E_apply, MeasureChain.realComponentCocycle, map_add, map_sub,
    map_zero] using h

theorem E0_realComponentL0 (ell : ℂ →ₗ[ℝ] ℝ) :
    E0 concreteFace5QuasiMeasurePreserving (realComponentL0 ell) = 0 := by
  apply AEEqFun.ext
  have hcongr := E_ae_congr concreteFace5QuasiMeasurePreserving
    (coeFn_realComponentL0 ell)
  filter_upwards [coeFn_E0 concreteFace5QuasiMeasurePreserving
      (realComponentL0 ell),
    hcongr,
    (AEEqFun.coeFn_zero :
      ((0 : L0 U6 measureU6) : U6 → ℝ) =ᵐ[measureU6]
        (0 : U6 → ℝ))] with q hE hC hzero
  rw [hE, hC, E_realComponentCocycle_apply, hzero]
  rfl

/-- The affine formula as a linear family of measurable cocycles. -/
def realComponentCocycles :
    (ℂ →ₗ[ℝ] ℝ) →ₗ[ℝ] MeasurableCocycles where
  toFun ell := ⟨realComponentL0 ell, E0_realComponentL0 ell⟩
  map_add' ell eta := by
    apply Subtype.ext
    exact realComponentL0ₗ.map_add ell eta
  map_smul' a ell := by
    apply Subtype.ext
    exact realComponentL0ₗ.map_smul a ell

/-- `Θ(ell) = [ell ∘ R]` in the actual ordinary quotient complex. -/
def theta : (ℂ →ₗ[ℝ] ℝ) →ₗ[ℝ] MeasurableH4 :=
  MeasurableBoundaries.mkQ.comp realComponentCocycles

@[simp]
theorem theta_apply (ell : ℂ →ₗ[ℝ] ℝ) :
    theta ell = Submodule.Quotient.mk (realComponentCocycles ell) :=
  rfl

/-- A nonzero affine component is not in the image of the bounded comparison map. -/
theorem theta_not_mem_range_comparison
    (ell : ℂ →ₗ[ℝ] ℝ) (hell : ell ≠ 0) :
    theta ell ∉ LinearMap.range comparison := by
  rintro ⟨a, ha⟩
  obtain ⟨F, rfl⟩ := BoundedBoundaries.mkQ_surjective a
  change comparison (Submodule.Quotient.mk F) = theta ell at ha
  rw [comparison_mk, theta_apply] at ha
  have hboundary :
      realComponentCocycles ell - comparisonCocycles F ∈
        MeasurableBoundaries :=
    QuotientAddGroup.eq_iff_sub_mem.mp ha.symm
  change (realComponentL0 ell - F.1.1) ∈ LinearMap.range
    (D0 concreteFace4QuasiMeasurePreserving) at hboundary
  rcases hboundary with ⟨f, hf⟩
  have hclass :
      realComponentL0 ell = F.1.1 +
        D0 concreteFace4QuasiMeasurePreserving f := by
    rw [hf]
    abel
  have hchosen := congrArg
    (fun g : L0 U5 measureU5 => (g : U5 → ℝ)) hclass
  have hrel : MeasureChain.realComponentCocycle ell =ᵐ[measureU5]
      fun q ↦ F.1 q + D f q := by
    filter_upwards [coeFn_realComponentL0 ell,
      AEEqFun.coeFn_add F.1.1
        (D0 concreteFace4QuasiMeasurePreserving f),
      coeFn_D0 concreteFace4QuasiMeasurePreserving f] with q hC hadd hD
    calc
      MeasureChain.realComponentCocycle ell q = realComponentL0 ell q := hC.symm
      _ = (F.1.1 + D0 concreteFace4QuasiMeasurePreserving f) q :=
        congrFun hchosen q
      _ = F.1 q + (D0 concreteFace4QuasiMeasurePreserving f) q := hadd
      _ = F.1 q + D f q := by rw [hD]
  exact realComponentCocycle_not_ae_bounded_mod_D ell hell
    ⟨f, F.1, ‖F.1‖, f.stronglyMeasurable, F.1.1.stronglyMeasurable,
      norm_nonneg _, Linfty.ae_abs_le_norm F.1, hrel⟩

/-- In particular, the affine-class map is injective. -/
theorem theta_injective : Function.Injective theta := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro ell hell
    change theta ell = 0 at hell
    by_contra hne
    apply theta_not_mem_range_comparison ell hne
    refine ⟨0, ?_⟩
    simpa using hell.symm
  · exact bot_le

theorem theta_ne_zero {ell : ℂ →ₗ[ℝ] ℝ} (hell : ell ≠ 0) :
    theta ell ≠ 0 := by
  intro h
  exact hell (theta_injective (h.trans (map_zero theta).symm))

end
end Pfaffian
end Sp4
