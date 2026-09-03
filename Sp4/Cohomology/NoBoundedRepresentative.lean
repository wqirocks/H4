import Sp4.Cohomology.OrbitCocycle
import Sp4.Period.Pole

/-!
# The period obstruction to bounded representatives

This module is the final analytic consequence of the article's two-cone diffusion
and explicit pole calculation.  It is kept below the abstract cohomological
assembly so the latter contains no hidden geometry or integration.
-/

namespace Sp4

noncomputable section

open MeasureTheory

/-- If a real component of the affine cocycle had an essentially bounded
representative modulo a measurable coboundary, all of the article's explicit
fixed-line periods would satisfy one uniform bound. -/
theorem realComponent_fixedLinePeriod_le_of_ae_bounded_mod_D
    (ell : ℂ →ₗ[ℝ] ℝ)
    (f : Pfaffian.U4 → ℝ) (hf : StronglyMeasurable f)
    (F : Pfaffian.U5 → ℝ) (hF : StronglyMeasurable F)
    (K : ℝ) (hK : 0 ≤ K)
    (hFbound : ∀ᵐ q ∂Pfaffian.measureU5, |F q| ≤ K)
    (hrel : MeasureChain.realComponentCocycle ell =ᵐ[Pfaffian.measureU5]
      fun q ↦ F q + Pfaffian.D f q)
    (A : ℂ) (hA : Pfaffian.FixedLineAdmissible A) :
    |ell (Pfaffian.fixedPeriod A)| ≤ 320 * K := by
  let Z := OrbitChain.periodCycle A 3 hA.toPeriodCycleAdmissible
  have hZ : OrbitChain.boundary ℝ 4 Z = 0 :=
    OrbitChain.boundary_periodCycle A 3 hA.toPeriodCycleAdmissible
  have hdiff :=
    TwoConeParameterization.abs_evaluation5_cycle_le_twenty_mul_quotientL1
      Z hZ f hf (MeasureChain.realComponentCocycle ell)
      (MeasureChain.realComponentCocycle_stronglyMeasurable ell)
      (MeasureChain.realComponentCocycle_isAlternatingFunction5 ell)
      (MeasureChain.realComponentCocycle_isPointwiseCocycle5 ell)
      F hF K hK hFbound hrel
  have heval := MeasureChain.evaluation5_realComponentCocycle_periodCycle
    ell A 3 hA.toPeriodCycleAdmissible
  have hvalue := Pfaffian.periodCycleValue_fixedLine A hA
  have hmass : OrbitChain.quotientL1 Z ≤ 16 :=
    OrbitChain.quotientL1_periodCycle_le_sixteen A 3
      hA.toPeriodCycleAdmissible
  rw [heval, hvalue] at hdiff
  calc
    |ell (Pfaffian.fixedPeriod A)| ≤
        20 * OrbitChain.quotientL1 Z * K := hdiff
    _ ≤ 20 * 16 * K :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmass (by norm_num)) hK
    _ = 320 * K := by ring

/-- No nonzero real scalar component of the affine cocycle is represented,
modulo a measurable four-cochain, by an essentially bounded measurable
five-cochain. -/
theorem realComponentCocycle_not_ae_bounded_mod_D
    (ell : ℂ →ₗ[ℝ] ℝ) (hell : ell ≠ 0) :
    ¬ ∃ (f : Pfaffian.U4 → ℝ) (F : Pfaffian.U5 → ℝ) (K : ℝ),
      StronglyMeasurable f ∧ StronglyMeasurable F ∧ 0 ≤ K ∧
      (∀ᵐ q ∂Pfaffian.measureU5, |F q| ≤ K) ∧
      MeasureChain.realComponentCocycle ell =ᵐ[Pfaffian.measureU5]
        (fun q ↦ F q + Pfaffian.D f q) := by
  rintro ⟨f, F, K, hf, hF, hK, hFbound, hrel⟩
  obtain ⟨A, _hpos, _hlt, hA, hlarge⟩ :=
    Pfaffian.realComponent_unbounded_on_admissible_fixedLine
      ell hell (show (0 : ℝ) < 1 by norm_num) (320 * K)
  have hle := realComponent_fixedLinePeriod_le_of_ae_bounded_mod_D
    ell f hf F hF K hK hFbound hrel A hA
  exact (not_lt_of_ge hle) hlarge

end
end Sp4
