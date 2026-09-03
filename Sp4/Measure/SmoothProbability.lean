import Mathlib.Probability.Distributions.Gaussian.Real
import Sp4.Pfaffian.Coordinates

/-!
# Concrete Gaussian probability measures on the normalized charts

The article permits any smooth probability measure with strictly positive density.
We choose independent centered real Gaussians, pair them into complex Gaussians,
transport them through the displayed coordinate equivalences, restrict to the open
generic loci, and normalize.  All statements below are genuine measure-theoretic
definitions and proofs; no measure is left implicit.
-/

namespace Sp4

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

/-- A centered real Gaussian of variance one. -/
def standardRealGaussian : Measure ℝ := gaussianReal 0 1

instance : IsProbabilityMeasure standardRealGaussian := by
  dsimp [standardRealGaussian]
  infer_instance

/-- The standard real Gaussian has the same null sets as Lebesgue measure, hence
gives positive mass to every nonempty open set. -/
instance : Measure.IsOpenPosMeasure standardRealGaussian where
  open_pos U hU hUne := by
    have hvol : volume U ≠ 0 := hU.measure_ne_zero volume hUne
    intro hzero
    exact hvol (gaussianReal_absolutelyContinuous' 0 one_ne_zero hzero)

/-- Independent standard Gaussians on the real and imaginary coordinates. -/
def standardComplexGaussian : Measure ℂ :=
  Measure.map Complex.equivRealProdCLM.symm
    (standardRealGaussian.prod standardRealGaussian)

instance : IsProbabilityMeasure standardComplexGaussian :=
  Measure.isProbabilityMeasure_map
    Complex.equivRealProdCLM.symm.continuous.measurable.aemeasurable

instance : Measure.IsOpenPosMeasure standardComplexGaussian :=
  Complex.equivRealProdCLM.symm.continuous.isOpenPosMeasure_map
    Complex.equivRealProdCLM.symm.surjective

/-- Independent standard complex Gaussians on a finite coordinate space. -/
def standardComplexGaussianPi (n : ℕ) : Measure (Fin n → ℂ) :=
  Measure.pi fun _ => standardComplexGaussian

instance (n : ℕ) : IsProbabilityMeasure (standardComplexGaussianPi n) := by
  dsimp [standardComplexGaussianPi]
  infer_instance

instance (n : ℕ) : Measure.IsOpenPosMeasure (standardComplexGaussianPi n) := by
  dsimp [standardComplexGaussianPi]
  infer_instance

/-- A measure presented as independent complex Gaussians in some finite complex
linear coordinate system.  This data records, rather than merely asserts, the
smooth strictly positive coordinate density needed by the submersion theorem. -/
structure GaussianCoordinatePresentation {E : Type u}
    [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℂ E]
    (mu : Measure E) : Type u where
  dimension : ℕ
  coordinates : E ≃L[ℂ] (Fin dimension → ℂ)
  measure_eq : mu = Measure.map coordinates.symm
    (standardComplexGaussianPi dimension)

/-! ## Restriction and normalization on a nonempty open set -/

section OpenRestriction

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]
  (ambient : Measure E) [IsFiniteMeasure ambient]
  (s : Set E)

/-- Pull the restriction of an ambient measure back to the corresponding open
subtype. -/
def openRestrictionRaw : Measure s :=
  (ambient.restrict s).comap Subtype.val

theorem openRestrictionRaw_isOpenPos [ambient.IsOpenPosMeasure]
    (hs : IsOpen s) :
    (openRestrictionRaw ambient s).IsOpenPosMeasure := by
  constructor
  intro V hV hVne
  let emb : Topology.IsOpenEmbedding (@Subtype.val E fun x => x ∈ s) :=
    IsOpen.isOpenEmbedding_subtypeVal hs
  have himOpen : IsOpen (Subtype.val '' V : Set E) :=
    emb.isOpen_iff_image_isOpen.mp hV
  have himNe : (Subtype.val '' V : Set E).Nonempty := hVne.image _
  rw [openRestrictionRaw, MeasurableEmbedding.comap_apply emb.measurableEmbedding]
  rw [Measure.restrict_apply himOpen.measurableSet]
  rw [Set.inter_eq_left.mpr]
  · exact himOpen.measure_ne_zero ambient himNe
  · rintro _ ⟨x, _, rfl⟩
    exact x.2

theorem openRestrictionRaw_ne_zero [ambient.IsOpenPosMeasure]
    (hs : IsOpen s) (hne : s.Nonempty) :
    openRestrictionRaw ambient s ≠ 0 := by
  letI : Nonempty s := hne.to_subtype
  letI : (openRestrictionRaw ambient s).IsOpenPosMeasure :=
    openRestrictionRaw_isOpenPos ambient s hs
  intro h
  have hpos := isOpen_univ.measure_ne_zero
    (openRestrictionRaw ambient s) Set.univ_nonempty
  exact hpos (by simpa [h])

theorem openRestrictionRaw_univ_lt_top (hs : IsOpen s) :
    openRestrictionRaw ambient s Set.univ < ⊤ := by
  let emb : Topology.IsOpenEmbedding (@Subtype.val E fun x => x ∈ s) :=
    IsOpen.isOpenEmbedding_subtypeVal hs
  rw [openRestrictionRaw, MeasurableEmbedding.comap_apply emb.measurableEmbedding]
  rw [Measure.restrict_apply
    ((emb.isOpen_iff_image_isOpen.mp isOpen_univ).measurableSet)]
  exact lt_of_le_of_lt (measure_mono (Set.subset_univ _))
    (measure_lt_top ambient Set.univ)

/-- The finite measure obtained before probability normalization. -/
def openRestrictionFinite (hs : IsOpen s) : FiniteMeasure s :=
  ⟨openRestrictionRaw ambient s,
    ⟨openRestrictionRaw_univ_lt_top ambient s hs⟩⟩

theorem openRestrictionFinite_ne_zero [ambient.IsOpenPosMeasure]
    (hs : IsOpen s) (hne : s.Nonempty) :
    openRestrictionFinite ambient s hs ≠ 0 := by
  intro h
  apply openRestrictionRaw_ne_zero ambient s hs hne
  exact congrArg Subtype.val h

/-- The normalized restriction, as an actual probability measure. -/
def normalizedOpenProbability (hs : IsOpen s) (hne : s.Nonempty) :
    ProbabilityMeasure s := by
  letI : Nonempty s := hne.to_subtype
  exact (openRestrictionFinite ambient s hs).normalize

/-- The measure underlying `normalizedOpenProbability`. -/
def normalizedOpenMeasure (hs : IsOpen s) (hne : s.Nonempty) : Measure s :=
  (normalizedOpenProbability ambient s hs hne : Measure s)

theorem normalizedOpenMeasure_isProbability (hs : IsOpen s) (hne : s.Nonempty) :
    IsProbabilityMeasure (normalizedOpenMeasure ambient s hs hne) :=
  (normalizedOpenProbability ambient s hs hne).2

theorem normalizedOpenMeasure_isOpenPos [ambient.IsOpenPosMeasure]
    (hs : IsOpen s) (hne : s.Nonempty) :
    (normalizedOpenMeasure ambient s hs hne).IsOpenPosMeasure := by
  letI : Nonempty s := hne.to_subtype
  let rawFinite := openRestrictionFinite ambient s hs
  have hfinite : rawFinite ≠ 0 := openRestrictionFinite_ne_zero ambient s hs hne
  have hrawOpen : (openRestrictionRaw ambient s).IsOpenPosMeasure :=
    openRestrictionRaw_isOpenPos ambient s hs
  constructor
  intro V hV hVne
  have hraw : openRestrictionRaw ambient s V ≠ 0 :=
    @Measure.IsOpenPosMeasure.open_pos s _ _ _ hrawOpen V hV hVne
  rw [normalizedOpenMeasure, normalizedOpenProbability,
    rawFinite.toMeasure_normalize_eq_of_nonzero hfinite, Measure.smul_apply]
  apply mul_ne_zero
  · exact_mod_cast inv_ne_zero (rawFinite.mass_nonzero_iff.mpr hfinite)
  · exact hraw

/-- A measurable set in an open subtype is null for the normalized
restriction exactly when its image is null for the ambient measure. -/
theorem normalizedOpenMeasure_eq_zero_iff_image
    [ambient.IsOpenPosMeasure] (hs : IsOpen s) (hne : s.Nonempty)
    {t : Set s} (ht : MeasurableSet t) :
    normalizedOpenMeasure ambient s hs hne t = 0 ↔
      ambient (Subtype.val '' t) = 0 := by
  let _ : Nonempty s := hne.to_subtype
  let rawFinite := openRestrictionFinite ambient s hs
  have hfinite : rawFinite ≠ 0 :=
    openRestrictionFinite_ne_zero ambient s hs hne
  have hemb : MeasurableEmbedding (@Subtype.val E fun x => x ∈ s) :=
    MeasurableEmbedding.subtype_coe hs.measurableSet
  have him : MeasurableSet (Subtype.val '' t : Set E) :=
    hemb.measurableSet_image' ht
  have hsubset : Subtype.val '' t ⊆ s := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  rw [normalizedOpenMeasure, normalizedOpenProbability,
    rawFinite.toMeasure_normalize_eq_of_nonzero hfinite, Measure.smul_apply]
  change rawFinite.mass⁻¹ * (openRestrictionRaw ambient s) t = 0 ↔ _
  rw [openRestrictionRaw]
  rw [MeasurableEmbedding.comap_apply hemb,
    Measure.restrict_apply him, Set.inter_eq_left.mpr hsubset]
  have hmass : rawFinite.mass ≠ 0 := rawFinite.mass_nonzero_iff.mpr hfinite
  exact mul_eq_zero_iff_left
    (ENNReal.coe_ne_zero.mpr (inv_ne_zero hmass))

/-- Absolute continuity of finite open-positive ambient measures descends to
their normalized restrictions to the same nonempty open set. -/
theorem normalizedOpenMeasure_absolutelyContinuous
    {mu nu : Measure E} [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    [mu.IsOpenPosMeasure] [nu.IsOpenPosMeasure]
    (h : mu ≪ nu) (hs : IsOpen s) (hne : s.Nonempty) :
    normalizedOpenMeasure mu s hs hne ≪
      normalizedOpenMeasure nu s hs hne := by
  apply Measure.AbsolutelyContinuous.mk
  intro t ht hnull
  apply (normalizedOpenMeasure_eq_zero_iff_image mu s hs hne ht).mpr
  apply h
  exact (normalizedOpenMeasure_eq_zero_iff_image nu s hs hne ht).mp hnull

end OpenRestriction

namespace Pfaffian

/-! ## The chosen measures on `U4` and `U5` -/

instance : Nonempty U4 :=
  ⟨⟨⟨1, 1⟩, ⟨one_ne_zero, one_ne_zero, by simp [delta4]⟩⟩⟩

instance : Nonempty U5 :=
  ⟨⟨⟨1, 1, 1, 1, 1⟩, by
    refine ⟨one_ne_zero, one_ne_zero, one_ne_zero, one_ne_zero, one_ne_zero,
      ?_, ?_, ?_, ?_, ?_⟩ <;> simp [p0, p1, p2, p3, p4]⟩⟩

theorem u4Set_nonempty : u4Set.Nonempty := by
  refine ⟨⟨1, 1⟩, ?_⟩
  exact ⟨one_ne_zero, one_ne_zero, by simp [delta4]⟩

theorem u5Set_nonempty : u5Set.Nonempty := by
  refine ⟨⟨1, 1, 1, 1, 1⟩, ?_⟩
  refine ⟨one_ne_zero, one_ne_zero, one_ne_zero, one_ne_zero, one_ne_zero,
    ?_, ?_, ?_, ?_, ?_⟩ <;> simp [p0, p1, p2, p3, p4]

/-- Gaussian probability measure in the ambient four-point coordinates. -/
def coord4Gaussian : Measure Coord4 :=
  Measure.map coord4ContinuousLinearEquivFun.symm (standardComplexGaussianPi 2)

instance : IsProbabilityMeasure coord4Gaussian :=
  Measure.isProbabilityMeasure_map
    coord4ContinuousLinearEquivFun.symm.continuous.measurable.aemeasurable

instance : Measure.IsOpenPosMeasure coord4Gaussian :=
  coord4ContinuousLinearEquivFun.symm.continuous.isOpenPosMeasure_map
    coord4ContinuousLinearEquivFun.symm.surjective

/-- Gaussian probability measure in the ambient five-point coordinates. -/
def coord5Gaussian : Measure Coord5 :=
  Measure.map coord5LinearIsometryEquivFun.symm (standardComplexGaussianPi 5)

instance : IsProbabilityMeasure coord5Gaussian :=
  Measure.isProbabilityMeasure_map
    coord5LinearIsometryEquivFun.symm.continuous.measurable.aemeasurable

instance : Measure.IsOpenPosMeasure coord5Gaussian :=
  coord5LinearIsometryEquivFun.symm.continuous.isOpenPosMeasure_map
    coord5LinearIsometryEquivFun.symm.surjective

def coord4GaussianPresentation : GaussianCoordinatePresentation coord4Gaussian where
  dimension := 2
  coordinates := coord4ContinuousLinearEquivFun
  measure_eq := rfl

def coord5GaussianPresentation : GaussianCoordinatePresentation coord5Gaussian where
  dimension := 5
  coordinates := coord5LinearIsometryEquivFun.toContinuousLinearEquiv
  measure_eq := rfl

/-- The article's fixed smooth probability measure on the four-point chart. -/
def measureU4 : Measure U4 :=
  normalizedOpenMeasure coord4Gaussian u4Set isOpen_u4Set u4Set_nonempty

instance : IsProbabilityMeasure measureU4 :=
  normalizedOpenMeasure_isProbability coord4Gaussian u4Set isOpen_u4Set u4Set_nonempty

instance : Measure.IsOpenPosMeasure measureU4 :=
  normalizedOpenMeasure_isOpenPos coord4Gaussian u4Set isOpen_u4Set u4Set_nonempty

/-- The article's fixed smooth probability measure on the five-point chart. -/
def measureU5 : Measure U5 :=
  normalizedOpenMeasure coord5Gaussian u5Set isOpen_u5Set u5Set_nonempty

instance : IsProbabilityMeasure measureU5 :=
  normalizedOpenMeasure_isProbability coord5Gaussian u5Set isOpen_u5Set u5Set_nonempty

instance : Measure.IsOpenPosMeasure measureU5 :=
  normalizedOpenMeasure_isOpenPos coord5Gaussian u5Set isOpen_u5Set u5Set_nonempty

end Pfaffian

end

end Sp4
