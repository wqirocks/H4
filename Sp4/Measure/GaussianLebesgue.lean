import Sp4.Measure.SmoothProbability
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Null-set equivalence of finite complex Gaussians and Lebesgue measure

The standard complex Gaussian has an everywhere positive density with
respect to Lebesgue measure.  This file proves the resulting equivalence of
null sets, first on `ℂ` and then on every finite complex coordinate space.
The finite-product statement is proved by induction through the canonical
`Fin (n+1)` product equivalence; no density formula is postulated.
-/

open MeasureTheory ProbabilityTheory
open Sp4

noncomputable section

theorem standardComplexGaussian_absolutelyContinuous_volume :
    standardComplexGaussian ≪ (volume : Measure ℂ) := by
  have hprod : standardRealGaussian.prod standardRealGaussian ≪
      (volume : Measure ℝ).prod volume :=
    (gaussianReal_absolutelyContinuous 0 one_ne_zero).prod
      (gaussianReal_absolutelyContinuous 0 one_ne_zero)
  have hmap := hprod.map
    Complex.measurableEquivRealProd.symm.measurable
  have hvolprod : (volume : Measure (ℝ × ℝ)) =
      (volume : Measure ℝ).prod volume := rfl
  rw [← hvolprod] at hmap
  have hv := MeasurePreserving.symm Complex.measurableEquivRealProd
    Complex.volume_preserving_equiv_real_prod
  rw [hv.map_eq] at hmap
  simpa [standardComplexGaussian, Complex.measurableEquivRealProd] using hmap

theorem volume_absolutelyContinuous_standardComplexGaussian :
    (volume : Measure ℂ) ≪ standardComplexGaussian := by
  have hprod : (volume : Measure ℝ).prod volume ≪
      standardRealGaussian.prod standardRealGaussian :=
    (gaussianReal_absolutelyContinuous' 0 one_ne_zero).prod
      (gaussianReal_absolutelyContinuous' 0 one_ne_zero)
  have hmap := hprod.map
    Complex.measurableEquivRealProd.symm.measurable
  have hvolprod : (volume : Measure (ℝ × ℝ)) =
      (volume : Measure ℝ).prod volume := rfl
  rw [← hvolprod] at hmap
  have hv := MeasurePreserving.symm Complex.measurableEquivRealProd
    Complex.volume_preserving_equiv_real_prod
  rw [hv.map_eq] at hmap
  simpa [standardComplexGaussian, Complex.measurableEquivRealProd] using hmap

/-- Independent standard complex Gaussians are absolutely continuous with
respect to Lebesgue measure in every finite dimension. -/
theorem standardComplexGaussianPi_absolutelyContinuous_volume : ∀ n : ℕ,
    standardComplexGaussianPi n ≪ (volume : Measure (Fin n → ℂ)) := by
  intro n
  induction n with
  | zero =>
      rw [standardComplexGaussianPi, Measure.pi_of_empty,
        Measure.volume_pi_eq_dirac]
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => ℂ) (0 : Fin (n + 1))
      have hprod : standardComplexGaussian.prod
          (standardComplexGaussianPi n) ≪
          (volume : Measure ℂ).prod
            (volume : Measure (Fin n → ℂ)) :=
        standardComplexGaussian_absolutelyContinuous_volume.prod ih
      have hmap := hprod.map e.symm.measurable
      have hg := MeasurePreserving.symm e
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => standardComplexGaussian)
          (0 : Fin (n + 1)))
      have hv := MeasurePreserving.symm e
        (volume_preserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => ℂ) (0 : Fin (n + 1)))
      have hgeq : Measure.map e.symm
          (standardComplexGaussian.prod (standardComplexGaussianPi n)) =
          standardComplexGaussianPi (n + 1) := by
        simpa [standardComplexGaussianPi] using hg.map_eq
      have hveq : Measure.map e.symm
          ((volume : Measure ℂ).prod
            (volume : Measure (Fin n → ℂ))) =
          (volume : Measure (Fin (n + 1) → ℂ)) := by
        have hvolprod :
            (volume : Measure (ℂ × (Fin n → ℂ))) =
              (volume : Measure ℂ).prod
                (volume : Measure (Fin n → ℂ)) := rfl
        rw [← hvolprod]
        exact hv.map_eq
      rwa [hgeq, hveq] at hmap

/-- Conversely, Lebesgue measure is absolutely continuous with respect to
the finite standard complex Gaussian. -/
theorem volume_absolutelyContinuous_standardComplexGaussianPi : ∀ n : ℕ,
    (volume : Measure (Fin n → ℂ)) ≪ standardComplexGaussianPi n := by
  intro n
  induction n with
  | zero =>
      rw [standardComplexGaussianPi, Measure.pi_of_empty,
        Measure.volume_pi_eq_dirac]
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => ℂ) (0 : Fin (n + 1))
      have hprod : (volume : Measure ℂ).prod
          (volume : Measure (Fin n → ℂ)) ≪
          standardComplexGaussian.prod
            (standardComplexGaussianPi n) :=
        volume_absolutelyContinuous_standardComplexGaussian.prod ih
      have hmap := hprod.map e.symm.measurable
      have hg := MeasurePreserving.symm e
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => standardComplexGaussian)
          (0 : Fin (n + 1)))
      have hv := MeasurePreserving.symm e
        (volume_preserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => ℂ) (0 : Fin (n + 1)))
      have hgeq : Measure.map e.symm
          (standardComplexGaussian.prod (standardComplexGaussianPi n)) =
          standardComplexGaussianPi (n + 1) := by
        simpa [standardComplexGaussianPi] using hg.map_eq
      have hveq : Measure.map e.symm
          ((volume : Measure ℂ).prod
            (volume : Measure (Fin n → ℂ))) =
          (volume : Measure (Fin (n + 1) → ℂ)) := by
        have hvolprod :
            (volume : Measure (ℂ × (Fin n → ℂ))) =
              (volume : Measure ℂ).prod
                (volume : Measure (Fin n → ℂ)) := rfl
        rw [← hvolprod]
        exact hv.map_eq
      rwa [hveq, hgeq] at hmap

/-- Backwards-compatible two-dimensional specialization. -/
theorem standardComplexGaussianPi_two_absolutelyContinuous_volume :
    standardComplexGaussianPi 2 ≪ (volume : Measure (Fin 2 → ℂ)) :=
  standardComplexGaussianPi_absolutelyContinuous_volume 2

/-- Backwards-compatible two-dimensional reverse specialization. -/
theorem volume_absolutelyContinuous_standardComplexGaussianPi_two :
    (volume : Measure (Fin 2 → ℂ)) ≪ standardComplexGaussianPi 2 :=
  volume_absolutelyContinuous_standardComplexGaussianPi 2

namespace MeasureTheory.Measure

/-- Absolute continuity is stable under finite powers.  Mathlib provides the
binary product result; this theorem iterates it through the canonical
`Fin (n+1)` splitting. -/
theorem piFin_absolutelyContinuous
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (h : μ ≪ ν) : ∀ n : ℕ,
      (Measure.pi fun _ : Fin n => μ) ≪
        (Measure.pi fun _ : Fin n => ν) := by
  intro n
  induction n with
  | zero =>
      rw [Measure.pi_of_empty, Measure.pi_of_empty]
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => α) (0 : Fin (n + 1))
      have hprod : μ.prod (Measure.pi fun _ : Fin n => μ) ≪
          ν.prod (Measure.pi fun _ : Fin n => ν) := h.prod ih
      have hmap := hprod.map e.symm.measurable
      have hμ := MeasurePreserving.symm e
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => μ) (0 : Fin (n + 1)))
      have hν := MeasurePreserving.symm e
        (measurePreserving_piFinSuccAbove
          (fun _ : Fin (n + 1) => ν) (0 : Fin (n + 1)))
      rw [hμ.map_eq, hν.map_eq] at hmap
      exact hmap

end MeasureTheory.Measure

namespace Sp4

universe u

/-- A standard finite complex Gaussian transported through a chosen complex
linear coordinate system. -/
def coordinateGaussian
    {E : Type u} [MeasurableSpace E] [NormedAddCommGroup E]
    [NormedSpace ℂ E] (d : ℕ) (e : E ≃L[ℂ] (Fin d → ℂ)) : Measure E :=
  Measure.map e.symm (standardComplexGaussianPi d)

def coordinateGaussianPresentation
    {E : Type u} [MeasurableSpace E] [NormedAddCommGroup E]
    [NormedSpace ℂ E] (d : ℕ) (e : E ≃L[ℂ] (Fin d → ℂ)) :
    GaussianCoordinatePresentation (coordinateGaussian d e) where
  dimension := d
  coordinates := e
  measure_eq := rfl

/-- A transported coordinate Gaussian is absolutely continuous with respect
to the canonical Lebesgue measure on a finite-dimensional real inner-product
space. -/
theorem coordinateGaussian_absolutelyContinuous_volume
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (d : ℕ) (e : E ≃L[ℂ] (Fin d → ℂ)) :
    coordinateGaussian d e ≪ (volume : Measure E) := by
  have h₁ := (standardComplexGaussianPi_absolutelyContinuous_volume d).map
    e.symm.continuous.measurable
  let _ : Measure.IsAddHaarMeasure
      (Measure.map e.symm (volume : Measure (Fin d → ℂ))) :=
    e.symm.isAddHaarMeasure_map (volume : Measure (Fin d → ℂ))
  have h₂ : Measure.map e.symm (volume : Measure (Fin d → ℂ)) ≪
      (volume : Measure E) :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  exact h₁.trans h₂

/-- The reverse null-set comparison for a transported coordinate Gaussian. -/
theorem volume_absolutelyContinuous_coordinateGaussian
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (d : ℕ) (e : E ≃L[ℂ] (Fin d → ℂ)) :
    (volume : Measure E) ≪ coordinateGaussian d e := by
  let _ : Measure.IsAddHaarMeasure
      (Measure.map e.symm (volume : Measure (Fin d → ℂ))) :=
    e.symm.isAddHaarMeasure_map (volume : Measure (Fin d → ℂ))
  have h₁ : (volume : Measure E) ≪
      Measure.map e.symm (volume : Measure (Fin d → ℂ)) :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have h₂ := (volume_absolutelyContinuous_standardComplexGaussianPi d).map
    e.symm.continuous.measurable
  exact h₁.trans h₂

end Sp4
