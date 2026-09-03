import Sp4.Basic.ComplexAlgebra

/-!
Almost-everywhere functions and nonsingular pullback.

The quotient `L0 α μ` is mathlib's space of a.e.-equal, a.e. strongly measurable
real-valued functions.  `Linfty α μ` is the genuine `L^∞` subspace, rather than a
chosen collection of representatives.  A quasi-measure-preserving map pulls both
spaces back; for `L^∞` the pullback is a contraction.
-/

namespace Sp4

open MeasureTheory
open scoped ENNReal

/-- Real-valued measurable functions modulo almost-everywhere equality. -/
abbrev L0 (α : Type*) [MeasurableSpace α] (μ : Measure α) :=
  α →ₘ[μ] ℝ

/-- Real `L^∞`, represented by a.e.-equal measurable functions. -/
abbrev Linfty (α : Type*) [MeasurableSpace α] (μ : Measure α) :=
  MeasureTheory.Lp ℝ ∞ μ

namespace L0

variable {α β γ : Type*}
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {μ : Measure α} {ν : Measure β} {ξ : Measure γ}

/-- Pullback of a.e.-classes along a nonsingular measurable map. -/
def pullbackₗ (T : α → β) (hT : Measure.QuasiMeasurePreserving T μ ν) :
    L0 β ν →ₗ[ℝ] L0 α μ where
  toFun f := f.compQuasiMeasurePreserving T hT
  map_add' f g := by
    apply AEEqFun.ext
    filter_upwards [
      AEEqFun.coeFn_compQuasiMeasurePreserving (f + g) hT,
      hT.ae (AEEqFun.coeFn_add f g),
      AEEqFun.coeFn_compQuasiMeasurePreserving f hT,
      AEEqFun.coeFn_compQuasiMeasurePreserving g hT,
      AEEqFun.coeFn_add
        (f.compQuasiMeasurePreserving T hT)
        (g.compQuasiMeasurePreserving T hT)] with x hfg hadd hf hg hout
    simpa only [Pi.add_apply, Function.comp_apply] using
      hfg.trans (hadd.trans ((congrArg₂ (· + ·) hf hg).symm.trans hout.symm))
  map_smul' c f := by
    apply AEEqFun.ext
    filter_upwards [
      AEEqFun.coeFn_compQuasiMeasurePreserving (c • f) hT,
      hT.ae (AEEqFun.coeFn_smul c f),
      AEEqFun.coeFn_compQuasiMeasurePreserving f hT,
      AEEqFun.coeFn_smul c (f.compQuasiMeasurePreserving T hT)] with x hcf hsmul hf hout
    simpa only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, RingHom.id_apply] using
      hcf.trans (hsmul.trans ((congrArg (c • ·) hf).symm.trans hout.symm))

theorem coe_pullbackₗ (T : α → β) (hT : Measure.QuasiMeasurePreserving T μ ν)
    (f : L0 β ν) :
    (pullbackₗ T hT f : α → ℝ) =ᵐ[μ] f ∘ T :=
  AEEqFun.coeFn_compQuasiMeasurePreserving f hT

@[simp]
theorem pullbackₗ_id (f : L0 α μ) :
    pullbackₗ id (.id μ) f = f :=
  AEEqFun.compQuasiMeasurePreserving_id f

theorem pullbackₗ_comp (S : β → γ) (hS : Measure.QuasiMeasurePreserving S ν ξ)
    (T : α → β) (hT : Measure.QuasiMeasurePreserving T μ ν) (f : L0 γ ξ) :
    pullbackₗ (S ∘ T) (hS.comp hT) f = pullbackₗ T hT (pullbackₗ S hS f) :=
  AEEqFun.compQuasiMeasurePreserving_comp f hS hT

/-- `L⁰` depends only on the null sets of the measure.  Mutually absolutely
continuous measures on the same measurable space therefore give canonically
linearly equivalent almost-everywhere function spaces. -/
noncomputable def measureClassEquiv {μ ν : Measure α}
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    L0 α μ ≃ₗ[ℝ] L0 α ν where
  toFun := pullbackₗ id
    ⟨measurable_id, by simpa using hνμ⟩
  invFun := pullbackₗ id
    ⟨measurable_id, by simpa using hμν⟩
  left_inv f := by
    rw [← pullbackₗ_comp]
    exact pullbackₗ_id f
  right_inv f := by
    rw [← pullbackₗ_comp]
    exact pullbackₗ_id f
  map_add' f g := LinearMap.map_add _ f g
  map_smul' c f := LinearMap.map_smul _ c f

section Finite

variable {ι : Type*} [Fintype ι]

/-- A finite real linear combination of nonsingular pullbacks.  Simplicial
coboundaries and coordinate alternation are instances of this construction. -/
noncomputable def weightedPullbackₗ (T : ι → α → β)
    (hT : ∀ i, Measure.QuasiMeasurePreserving (T i) μ ν) (c : ι → ℝ) :
    L0 β ν →ₗ[ℝ] L0 α μ :=
  ∑ i, c i • pullbackₗ (T i) (hT i)

theorem coeFn_weightedPullbackₗ (T : ι → α → β)
    (hT : ∀ i, Measure.QuasiMeasurePreserving (T i) μ ν) (c : ι → ℝ)
    (f : L0 β ν) :
    (weightedPullbackₗ T hT c f : α → ℝ) =ᵐ[μ]
      fun x => ∑ i, c i * f (T i x) := by
  have hpull : ∀ᵐ x ∂μ, ∀ i,
      (pullbackₗ (T i) (hT i) f : α → ℝ) x = f (T i x) :=
    Filter.eventually_all.2 fun i => coe_pullbackₗ (T i) (hT i) f
  have hsmul : ∀ᵐ x ∂μ, ∀ i,
      (c i • pullbackₗ (T i) (hT i) f : L0 α μ) x =
        c i * (pullbackₗ (T i) (hT i) f : L0 α μ) x :=
    Filter.eventually_all.2 fun i => by
      exact (AEEqFun.coeFn_smul (c i) (pullbackₗ (T i) (hT i) f)).mono
        fun x hx => by simpa only [Pi.smul_apply, smul_eq_mul] using hx
  filter_upwards [
    AEEqFun.coeFn_finsetSum Finset.univ
      (fun i => c i • pullbackₗ (T i) (hT i) f),
    hpull, hsmul] with x hsum hpullx hsmulx
  rw [show weightedPullbackₗ T hT c f =
      ∑ i, c i • pullbackₗ (T i) (hT i) f by
        simp [weightedPullbackₗ]]
  rw [hsum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hsmulx i, hpullx i]

end Finite

end L0

namespace Linfty

variable {α β γ : Type*}
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {μ : Measure α} {ν : Measure β} {ξ : Measure γ}

private theorem eLpNorm_pullback_le (T : α → β)
    (hT : Measure.QuasiMeasurePreserving T μ ν) (f : L0 β ν) :
    eLpNorm (f.compQuasiMeasurePreserving T hT) ∞ μ ≤ eLpNorm f ∞ ν := by
  simp only [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  filter_upwards [
    AEEqFun.coeFn_compQuasiMeasurePreserving f hT,
    hT.ae (enorm_ae_le_eLpNormEssSup f ν)] with x hcomp hbound
  rw [hcomp]
  exact hbound

/-- Pullback on `L^∞` along a nonsingular measurable map. -/
def pullbackₗ (T : α → β) (hT : Measure.QuasiMeasurePreserving T μ ν) :
    Linfty β ν →ₗ[ℝ] Linfty α μ where
  toFun f :=
    ⟨f.1.compQuasiMeasurePreserving T hT,
      (eLpNorm_pullback_le T hT f.1).trans_lt f.2⟩
  map_add' f g := by
    apply Subtype.ext
    exact L0.pullbackₗ T hT |>.map_add f.1 g.1
  map_smul' c f := by
    apply Subtype.ext
    exact L0.pullbackₗ T hT |>.map_smul c f.1

@[simp]
theorem coe_pullbackₗ (T : α → β) (hT : Measure.QuasiMeasurePreserving T μ ν)
    (f : Linfty β ν) :
    (pullbackₗ T hT f : L0 α μ) = f.1.compQuasiMeasurePreserving T hT :=
  rfl

theorem coeFn_pullbackₗ (T : α → β) (hT : Measure.QuasiMeasurePreserving T μ ν)
    (f : Linfty β ν) :
    (pullbackₗ T hT f : α → ℝ) =ᵐ[μ] f ∘ T :=
  AEEqFun.coeFn_compQuasiMeasurePreserving f.1 hT

theorem norm_pullbackₗ_le (T : α → β)
    (hT : Measure.QuasiMeasurePreserving T μ ν) (f : Linfty β ν) :
    ‖pullbackₗ T hT f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_pullback_le T hT f.1)

/-- The nonsingular `L^∞` pullback as a continuous linear contraction. -/
noncomputable def pullbackCLM (T : α → β) (hT : Measure.QuasiMeasurePreserving T μ ν) :
    Linfty β ν →L[ℝ] Linfty α μ :=
  (pullbackₗ T hT).mkContinuous 1 fun f => by
    simpa using norm_pullbackₗ_le T hT f

@[simp]
theorem pullbackₗ_id (f : Linfty α μ) :
    pullbackₗ id (.id μ) f = f := by
  apply Subtype.ext
  exact AEEqFun.compQuasiMeasurePreserving_id f.1

theorem pullbackₗ_comp (S : β → γ) (hS : Measure.QuasiMeasurePreserving S ν ξ)
    (T : α → β) (hT : Measure.QuasiMeasurePreserving T μ ν) (f : Linfty γ ξ) :
    pullbackₗ (S ∘ T) (hS.comp hT) f = pullbackₗ T hT (pullbackₗ S hS f) := by
  apply Subtype.ext
  exact AEEqFun.compQuasiMeasurePreserving_comp f.1 hS hT

/-- `L∞` and its essential-supremum norm depend only on the measure class.
The identity map gives the canonical linear equivalence for two mutually
absolutely continuous measures. -/
noncomputable def measureClassEquiv {μ ν : Measure α}
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ) :
    Linfty α μ ≃ₗ[ℝ] Linfty α ν where
  toFun := pullbackₗ id
    ⟨measurable_id, by simpa using hνμ⟩
  invFun := pullbackₗ id
    ⟨measurable_id, by simpa using hμν⟩
  left_inv f := by
    rw [← pullbackₗ_comp]
    exact pullbackₗ_id f
  right_inv f := by
    rw [← pullbackₗ_comp]
    exact pullbackₗ_id f
  map_add' f g := LinearMap.map_add _ f g
  map_smul' c f := LinearMap.map_smul _ c f

/-- Replacing a measure by an equivalent representative does not change the
essential-supremum norm. -/
@[simp]
theorem norm_measureClassEquiv_apply {μ ν : Measure α}
    (hμν : μ ≪ ν) (hνμ : ν ≪ μ) (f : Linfty α μ) :
    ‖measureClassEquiv hμν hνμ f‖ = ‖f‖ := by
  apply le_antisymm
  · change ‖pullbackₗ id _ f‖ ≤ ‖f‖
    exact norm_pullbackₗ_le id _ f
  · let E := measureClassEquiv hμν hνμ
    have hcontract := norm_pullbackₗ_le id
      (show Measure.QuasiMeasurePreserving id μ ν from
        ⟨measurable_id, by simpa using hμν⟩) (E f)
    have hinv : pullbackₗ id
        (show Measure.QuasiMeasurePreserving id μ ν from
          ⟨measurable_id, by simpa using hμν⟩) (E f) = f := by
      exact E.symm_apply_apply f
    rw [hinv] at hcontract
    exact hcontract

section Finite

variable {ι : Type*} [Fintype ι]

/-- A finite real linear combination of nonsingular pullbacks on `L^∞`. -/
noncomputable def weightedPullbackₗ (T : ι → α → β)
    (hT : ∀ i, Measure.QuasiMeasurePreserving (T i) μ ν) (c : ι → ℝ) :
    Linfty β ν →ₗ[ℝ] Linfty α μ :=
  ∑ i, c i • pullbackₗ (T i) (hT i)

theorem norm_weightedPullbackₗ_le (T : ι → α → β)
    (hT : ∀ i, Measure.QuasiMeasurePreserving (T i) μ ν) (c : ι → ℝ)
    (f : Linfty β ν) :
    ‖weightedPullbackₗ T hT c f‖ ≤ (∑ i, |c i|) * ‖f‖ := by
  rw [show weightedPullbackₗ T hT c f =
      ∑ i, c i • pullbackₗ (T i) (hT i) f by
        simp [weightedPullbackₗ]]
  calc
    ‖∑ i, c i • pullbackₗ (T i) (hT i) f‖ ≤
        ∑ i, ‖c i • pullbackₗ (T i) (hT i) f‖ := norm_sum_le _ _
    _ = ∑ i, |c i| * ‖pullbackₗ (T i) (hT i) f‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, |c i| * ‖f‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (norm_pullbackₗ_le (T i) (hT i) f) (abs_nonneg _)
    _ = (∑ i, |c i|) * ‖f‖ := by rw [Finset.sum_mul]

/-- The finite weighted pullback as a bounded operator. -/
noncomputable def weightedPullbackCLM (T : ι → α → β)
    (hT : ∀ i, Measure.QuasiMeasurePreserving (T i) μ ν) (c : ι → ℝ) :
    Linfty β ν →L[ℝ] Linfty α μ :=
  (weightedPullbackₗ T hT c).mkContinuous (∑ i, |c i|) fun f =>
    norm_weightedPullbackₗ_le T hT c f

theorem coeFn_weightedPullbackₗ (T : ι → α → β)
    (hT : ∀ i, Measure.QuasiMeasurePreserving (T i) μ ν) (c : ι → ℝ)
    (f : Linfty β ν) :
    (weightedPullbackₗ T hT c f : α → ℝ) =ᵐ[μ]
      fun x => ∑ i, c i * f (T i x) := by
  have hpull : ∀ᵐ x ∂μ, ∀ i,
      (pullbackₗ (T i) (hT i) f : α → ℝ) x = f (T i x) :=
    Filter.eventually_all.2 fun i => coeFn_pullbackₗ (T i) (hT i) f
  have hsmul : ∀ᵐ x ∂μ, ∀ i,
      (c i • pullbackₗ (T i) (hT i) f : Linfty α μ) x =
        c i * (pullbackₗ (T i) (hT i) f : Linfty α μ) x :=
    Filter.eventually_all.2 fun i => by
      exact (Lp.coeFn_smul (c i) (pullbackₗ (T i) (hT i) f)).mono
        fun x hx => by simpa only [Pi.smul_apply, smul_eq_mul] using hx
  filter_upwards [
    Lp.coeFn_finsetSum Finset.univ
      (fun i => c i • pullbackₗ (T i) (hT i) f),
    hpull, hsmul] with x hsum hpullx hsmulx
  rw [show weightedPullbackₗ T hT c f =
      ∑ i, c i • pullbackₗ (T i) (hT i) f by
        simp [weightedPullbackₗ]]
  rw [hsum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hsmulx i, hpullx i]

theorem coe_weightedPullbackₗ (T : ι → α → β)
    (hT : ∀ i, Measure.QuasiMeasurePreserving (T i) μ ν) (c : ι → ℝ)
    (f : Linfty β ν) :
    (weightedPullbackₗ T hT c f : L0 α μ) =
      L0.weightedPullbackₗ T hT c f.1 := by
  apply AEEqFun.ext
  exact (coeFn_weightedPullbackₗ T hT c f).trans
    (L0.coeFn_weightedPullbackₗ T hT c f.1).symm

end Finite

/-- Regard an a.e.-class with a supplied real essential bound as an element of
`L^∞`. -/
def ofClassBound (f : L0 α μ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂μ, |f x| ≤ C) : Linfty α μ := by
  refine ⟨f, ?_⟩
  change eLpNorm f ∞ μ < ∞
  rw [eLpNorm_exponent_top]
  exact (eLpNormEssSup_le_of_ae_bound (by
    simpa only [Real.norm_eq_abs] using hf)).trans_lt ENNReal.ofReal_lt_top

@[simp]
theorem coe_ofClassBound (f : L0 α μ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂μ, |f x| ≤ C) :
    (ofClassBound f C hC hf : L0 α μ) = f := rfl

theorem norm_ofClassBound_le (f : L0 α μ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂μ, |f x| ≤ C) :
    ‖ofClassBound f C hC hf‖ ≤ C := by
  rw [Lp.norm_def, eLpNorm_exponent_top]
  calc
    ENNReal.toReal (eLpNormEssSup
        (ofClassBound f C hC hf : α → ℝ) μ) ≤
        ENNReal.toReal (ENNReal.ofReal C) :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (eLpNormEssSup_le_of_ae_bound (by
          rw [coe_ofClassBound]
          simpa only [Real.norm_eq_abs] using hf))
    _ = C := ENNReal.toReal_ofReal hC

/-- The `L∞` norm is bounded by every almost-everywhere pointwise absolute
bound.  Unlike the corresponding finite-`p` statement, this needs no
finiteness hypothesis on the measure. -/
theorem norm_le_of_ae_abs_le (f : Linfty α μ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂μ, |f x| ≤ C) : ‖f‖ ≤ C := by
  let g := ofClassBound f.1 C hC hf
  have hgf : g = f := by
    apply Subtype.ext
    rfl
  rw [← hgf]
  exact norm_ofClassBound_le f.1 C hC hf

end Linfty

/-! ## Full-support representatives -/

/-- The canonical representative of an `L^∞` class is bounded almost everywhere
by its norm. -/
theorem Linfty.ae_abs_le_norm
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Linfty α μ) : ∀ᵐ x ∂μ, |f x| ≤ ‖f‖ := by
  simpa only [Real.norm_eq_abs, ← toReal_eLpNorm (Lp.aestronglyMeasurable f),
    Lp.norm_def] using ae_le_lpNorm_exponent_top (Lp.memLp f)

/-- An almost-everywhere bound on a continuous function is pointwise whenever
nonempty open sets have positive measure. -/
theorem continuous_abs_le_of_ae
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ : Measure α} [Measure.IsOpenPosMeasure μ]
    {f : α → ℝ} (hf : Continuous f) {C : ℝ}
    (hbound : ∀ᵐ x ∂μ, |f x| ≤ C) :
    ∀ x, |f x| ≤ C := by
  let good : Set α := {x | |f x| ≤ C}
  have hclosed : IsClosed good := isClosed_le hf.abs continuous_const
  have hae : good =ᵐ[μ] Set.univ := by
    filter_upwards [hbound] with x hx
    change (|f x| ≤ C) = True
    exact propext ⟨fun _ => trivial, fun _ => hx⟩
  have hall : good = Set.univ := hclosed.ae_eq_univ_iff_eq.mp hae
  intro x
  have hx : x ∈ good := by rw [hall]; exact Set.mem_univ x
  exact hx

/-- A continuous representative of an `L^∞` class is bounded everywhere by the
`L^∞` norm. -/
theorem Linfty.continuous_rep_norm_bound
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ : Measure α} [Measure.IsOpenPosMeasure μ]
    (f : Linfty α μ) (g : α → ℝ) (hg : Continuous g)
    (hgf : g =ᵐ[μ] f) :
    ∀ x, |g x| ≤ ‖f‖ := by
  have hfbound : ∀ᵐ x ∂μ, |f x| ≤ ‖f‖ := by
    exact Linfty.ae_abs_le_norm f
  have hgbound : ∀ᵐ x ∂μ, |g x| ≤ ‖f‖ := by
    filter_upwards [hgf, hfbound] with x hx hbound
    rw [hx]
    exact hbound
  exact continuous_abs_le_of_ae hg hgbound

end Sp4
