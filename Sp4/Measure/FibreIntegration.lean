import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# The measure-theoretic output of smooth fibre integration

This file contains no existence assertion.  It records the exact package produced
by a properly supported smooth vertical probability density.  Separating this
package from its differential-geometric construction lets the article's averaging
argument be checked using mathlib's genuine measures, kernels, integrals, and
almost-everywhere filters.
-/

namespace Sp4

open MeasureTheory ProbabilityTheory
open Filter
open scoped ProbabilityTheory Topology

noncomputable section

universe u v

/-- The usable output of a properly supported smooth probability density along
the fibres of `projection`.

The local density bound is the coordinate form of proper parameterized
pushforward: over a neighborhood of a base point, every nuisance pushforward has
a uniformly bounded density with respect to `mu`.  The final two fields record
the corresponding integrability and continuity statements for locally integrable
functions. -/
structure SmoothFibreKernel
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [MeasurableSpace X]
    [MeasurableSpace Y]
    (mu : Measure X) (nu : Measure Y)
    (projection : Y → X) {ι : Type*} [Fintype ι]
    (nuisance : ι → Y → X) where
  kernel : Kernel X Y
  markov : IsMarkovKernel kernel
  projection_ae : ∀ x, ∀ᵐ y ∂kernel x, projection y = x
  mixture_absolutelyContinuous : kernel ∘ₘ mu ≪ nu
  nuisance_measurable : ∀ i, Measurable (nuisance i)
  local_density_bound :
    ∀ x, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ x' ∈ V, ∀ i, ∀ s : Set X, MeasurableSet s →
        (kernel x').real ((nuisance i) ⁻¹' s) ≤ C * mu.real s
  nuisance_integrable :
    ∀ (f : X → ℝ), LocallyIntegrable f mu →
      ∀ x i, Integrable (f ∘ nuisance i) (kernel x)
  nuisance_average_continuous :
    ∀ (f : X → ℝ), LocallyIntegrable f mu → ∀ i,
      Continuous (fun x => ∫ y, f (nuisance i y) ∂(kernel x))

namespace SmoothFibreKernel

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [MeasurableSpace X] [MeasurableSpace Y]
  {mu : Measure X} {nu : Measure Y} {projection : Y → X}
  {ι : Type*} [Fintype ι] {nuisance : ι → Y → X}

/-- A `nu`-almost-everywhere statement holds on almost every fibre.  This is the
precise Fubini/disintegration step that prevents restriction of an a.e. identity
to a positive-codimension point-set fibre. -/
theorem ae_ae (K : SmoothFibreKernel mu nu projection nuisance)
    {P : Y → Prop} (hP : ∀ᵐ y ∂nu, P y) :
    ∀ᵐ x ∂mu, ∀ᵐ y ∂K.kernel x, P y := by
  letI : IsMarkovKernel K.kernel := K.markov
  exact Measure.ae_ae_of_ae_comp (K.mixture_absolutelyContinuous.ae_le hP)

/-- The measure of the region on which a finite measurable real function exceeds
a natural cutoff tends to zero.  This is the continuity-from-above step used in
the article's local boundedness argument. -/
theorem tendsto_measureReal_abs_gt_atTop [IsFiniteMeasure mu]
    (f : X → ℝ) (hf : StronglyMeasurable f) :
    Tendsto (fun n : ℕ => mu.real {x | (n : ℝ) < |f x|}) atTop (𝓝 0) := by
  let s : ℕ → Set X := fun n => {x | (n : ℝ) < |f x|}
  have hs : ∀ n, NullMeasurableSet (s n) mu := by
    intro n
    exact (by measurability : MeasurableSet (s n)).nullMeasurableSet
  have hanti : Antitone s := by
    intro n m hnm x hx
    change (n : ℝ) < |f x|
    exact (Nat.cast_le.mpr hnm).trans_lt hx
  have hinter : ⋂ n, s n = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt |f x|
    exact (not_lt_of_ge hn.le) (Set.mem_iInter.mp hx n)
  have ht := tendsto_measure_iInter_atTop (μ := mu) hs hanti
    ⟨0, measure_ne_top mu (s 0)⟩
  rw [hinter, measure_empty] at ht
  change Tendsto (ENNReal.toReal ∘ (mu ∘ s)) atTop (𝓝 0)
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht

theorem exists_nat_measureReal_abs_gt_lt [IsFiniteMeasure mu]
    (f : X → ℝ) (hf : StronglyMeasurable f) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, mu.real {x | (n : ℝ) < |f x|} < ε :=
  ((tendsto_measureReal_abs_gt_atTop f hf).eventually
    (Iio_mem_nhds hε)).exists

end SmoothFibreKernel

end


end Sp4
