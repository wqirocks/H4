import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# A finite reciprocal diffusion weight

For finitely many real measurable functions `h j`, the density

`1 / (1 + ∑ j, |h j|)`

is everywhere positive and at most one.  Reweighting any probability
measure by this density and normalizing therefore gives another probability
measure under which every `h j` is integrable.  This is the precise
positivity/integrability device used in the two-cone diffusion.
-/

namespace Sp4

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

variable {P J : Type*} [MeasurableSpace P] [Fintype J]

/-- The finite sum of absolute values which the diffusion weight controls. -/
def reciprocalLoad (h : J → P → ℝ) (p : P) : ℝ :=
  ∑ j, |h j p|

theorem reciprocalLoad_nonneg (h : J → P → ℝ) (p : P) :
    0 ≤ reciprocalLoad h p := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

theorem abs_le_reciprocalLoad (h : J → P → ℝ) (j : J) (p : P) :
    |h j p| ≤ reciprocalLoad h p := by
  simpa [reciprocalLoad] using
    (Finset.single_le_sum (s := Finset.univ) (f := fun k ↦ |h k p|)
      (fun k _ ↦ abs_nonneg (h k p)) (Finset.mem_univ j))

/-- The real-valued reciprocal weight. -/
def reciprocalWeight (h : J → P → ℝ) (p : P) : ℝ :=
  (1 + reciprocalLoad h p)⁻¹

theorem reciprocalWeight_pos (h : J → P → ℝ) (p : P) :
    0 < reciprocalWeight h p := by
  apply inv_pos.mpr
  exact add_pos_of_pos_of_nonneg zero_lt_one (reciprocalLoad_nonneg h p)

theorem reciprocalWeight_le_one (h : J → P → ℝ) (p : P) :
    reciprocalWeight h p ≤ 1 := by
  rw [reciprocalWeight]
  apply (inv_le_one₀
    (add_pos_of_pos_of_nonneg zero_lt_one
      (reciprocalLoad_nonneg h p))).2
  exact le_add_of_nonneg_right (reciprocalLoad_nonneg h p)

/-- The same weight as an extended nonnegative density. -/
def reciprocalDensity (h : J → P → ℝ) (p : P) : ℝ≥0∞ :=
  ENNReal.ofReal (reciprocalWeight h p)

theorem measurable_reciprocalLoad (h : J → P → ℝ)
    (hh : ∀ j, Measurable (h j)) : Measurable (reciprocalLoad h) := by
  change Measurable (fun p ↦ ∑ j, |h j p|)
  apply Finset.measurable_sum
  intro j _hj
  simpa only [Real.norm_eq_abs] using (hh j).norm

theorem measurable_reciprocalWeight (h : J → P → ℝ)
    (hh : ∀ j, Measurable (h j)) : Measurable (reciprocalWeight h) := by
  exact (measurable_const.add (measurable_reciprocalLoad h hh)).inv

theorem measurable_reciprocalDensity (h : J → P → ℝ)
    (hh : ∀ j, Measurable (h j)) : Measurable (reciprocalDensity h) :=
  ENNReal.measurable_ofReal.comp (measurable_reciprocalWeight h hh)

theorem reciprocalDensity_ne_zero (h : J → P → ℝ) (p : P) :
    reciprocalDensity h p ≠ 0 := by
  rw [reciprocalDensity, ENNReal.ofReal_ne_zero_iff]
  exact reciprocalWeight_pos h p

theorem reciprocalDensity_le_one (h : J → P → ℝ) (p : P) :
    reciprocalDensity h p ≤ 1 := by
  rw [reciprocalDensity, ENNReal.ofReal_le_one]
  exact reciprocalWeight_le_one h p

theorem reciprocalDensity_toReal (h : J → P → ℝ) (p : P) :
    (reciprocalDensity h p).toReal = reciprocalWeight h p := by
  rw [reciprocalDensity, ENNReal.toReal_ofReal]
  exact (reciprocalWeight_pos h p).le

/-- Before normalization, the reciprocal reweighting of a base measure. -/
def reciprocalRawMeasure (mu : Measure P) (h : J → P → ℝ) : Measure P :=
  mu.withDensity (reciprocalDensity h)

noncomputable instance reciprocalRawMeasure_isFinite
    (mu : Measure P) [IsProbabilityMeasure mu] (h : J → P → ℝ) :
    IsFiniteMeasure (reciprocalRawMeasure mu h) := by
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  calc
    ∫⁻ p, reciprocalDensity h p ∂mu ≤ 1 :=
      lintegral_le_const (ae_of_all _ (reciprocalDensity_le_one h))
    _ < ∞ := ENNReal.one_lt_top

theorem reciprocalRawMeasure_ne_zero
    (mu : Measure P) [IsProbabilityMeasure mu]
    (h : J → P → ℝ) (hh : ∀ j, Measurable (h j)) :
    reciprocalRawMeasure mu h ≠ 0 := by
  intro hz
  have hae : reciprocalDensity h =ᵐ[mu] 0 :=
    (withDensity_eq_zero_iff
      (measurable_reciprocalDensity h hh).aemeasurable).mp hz
  have hfalse : ∀ᵐ _p ∂mu, False :=
    hae.mono fun p hp ↦ reciprocalDensity_ne_zero h p hp
  obtain ⟨_p, hp⟩ := hfalse.exists
  exact hp

/-- The finite measure object fed to `FiniteMeasure.normalize`. -/
def reciprocalFiniteMeasure
    (mu : Measure P) [IsProbabilityMeasure mu]
    (h : J → P → ℝ) : FiniteMeasure P :=
  ⟨reciprocalRawMeasure mu h, inferInstance⟩

theorem reciprocalFiniteMeasure_ne_zero
    (mu : Measure P) [IsProbabilityMeasure mu]
    (h : J → P → ℝ) (hh : ∀ j, Measurable (h j)) :
    reciprocalFiniteMeasure mu h ≠ 0 := by
  intro hz
  apply reciprocalRawMeasure_ne_zero mu h hh
  exact congrArg (↑· : FiniteMeasure P → Measure P) hz

/-- The normalized reciprocal-weight probability measure. -/
def reciprocalProbability
    (mu : Measure P) [IsProbabilityMeasure mu] [Nonempty P]
    (h : J → P → ℝ) : ProbabilityMeasure P :=
  (reciprocalFiniteMeasure mu h).normalize

theorem reciprocalProbability_toMeasure
    (mu : Measure P) [IsProbabilityMeasure mu] [Nonempty P]
    (h : J → P → ℝ) (hh : ∀ j, Measurable (h j)) :
    ((reciprocalProbability mu h : ProbabilityMeasure P) : Measure P) =
      (reciprocalFiniteMeasure mu h).mass⁻¹ •
        reciprocalRawMeasure mu h := by
  exact FiniteMeasure.toMeasure_normalize_eq_of_nonzero _
    (reciprocalFiniteMeasure_ne_zero mu h hh)

/-- The normalized reciprocal measure is in the same measure class as the
base probability measure.  Only the forward absolute-continuity direction
is needed by diffusion. -/
theorem reciprocalProbability_absolutelyContinuous
    (mu : Measure P) [IsProbabilityMeasure mu] [Nonempty P]
    (h : J → P → ℝ) (hh : ∀ j, Measurable (h j)) :
    ((reciprocalProbability mu h : ProbabilityMeasure P) : Measure P) ≪ mu := by
  rw [reciprocalProbability_toMeasure mu h hh]
  exact Measure.smul_absolutelyContinuous.trans
    (withDensity_absolutelyContinuous mu (reciprocalDensity h))

theorem abs_mul_reciprocalWeight_le_one
    (h : J → P → ℝ) (j : J) (p : P) :
    |h j p * reciprocalWeight h p| ≤ 1 := by
  rw [abs_mul, abs_of_pos (reciprocalWeight_pos h p), reciprocalWeight]
  rw [← div_eq_mul_inv, div_le_one]
  · exact (abs_le_reciprocalLoad h j p).trans
      (le_add_of_nonneg_left zero_le_one)
  · have := reciprocalLoad_nonneg h p
    linarith

theorem integrable_reciprocalRawMeasure
    (mu : Measure P) [IsProbabilityMeasure mu]
    (h : J → P → ℝ) (hh : ∀ j, Measurable (h j)) (j : J) :
    Integrable (h j) (reciprocalRawMeasure mu h) := by
  rw [reciprocalRawMeasure,
    integrable_withDensity_iff
      (measurable_reciprocalDensity h hh)
      (ae_of_all _ fun p ↦ by
        simp [reciprocalDensity])]
  rw [show (fun p ↦ h j p * (reciprocalDensity h p).toReal) =
      fun p ↦ h j p * reciprocalWeight h p by
    funext p
    rw [reciprocalDensity_toReal]]
  apply (integrable_const (1 : ℝ)).mono
  · exact ((hh j).mul (measurable_reciprocalWeight h hh)).aestronglyMeasurable
  · filter_upwards with p
    rw [Real.norm_eq_abs, norm_one]
    exact abs_mul_reciprocalWeight_le_one h j p

/-- Every function used in the denominator is integrable for the normalized
diffusion probability. -/
theorem integrable_reciprocalProbability
    (mu : Measure P) [IsProbabilityMeasure mu] [Nonempty P]
    (h : J → P → ℝ) (hh : ∀ j, Measurable (h j)) (j : J) :
    Integrable (h j)
      ((reciprocalProbability mu h : ProbabilityMeasure P) : Measure P) := by
  rw [reciprocalProbability_toMeasure mu h hh]
  exact (integrable_reciprocalRawMeasure mu h hh j).smul_measure_nnreal

end

end Sp4
