import Sp4.Pfaffian.Permutation
import Sp4.Measure.L0
import Mathlib.MeasureTheory.VectorMeasure.Integral
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure

/-! Signed measure chains, alternation, boundary, the Dirac map, and Stokes. -/

namespace Sp4

namespace MeasureChain

noncomputable section

open MeasureTheory Pfaffian OrbitChain
open scoped BigOperators ENNReal NNReal

variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Z]

/-- The chain group of finite real signed Borel measures.  Mathlib's
`SignedMeasure` is a real-valued countably additive vector measure; its Jordan
decomposition implies finite total variation. -/
abbrev Chain (X : Type*) [MeasurableSpace X] := SignedMeasure X

/-- The variation of every real signed measure is finite. -/
noncomputable instance signedMeasureVariationFinite (ν : SignedMeasure X) :
    IsFiniteMeasure ν.variation := by
  rw [← SignedMeasure.totalVariation_eq_variation]
  infer_instance

/-- Total-variation mass, as a finite real number. -/
def mass (ν : SignedMeasure X) : ℝ := ν.variation.real Set.univ

theorem mass_nonneg (ν : SignedMeasure X) : 0 ≤ mass ν :=
  measureReal_nonneg

@[simp]
theorem mass_zero : mass (0 : SignedMeasure X) = 0 := by
  simp [mass]

@[simp]
theorem mass_neg (ν : SignedMeasure X) : mass (-ν) = mass ν := by
  simp [mass]

theorem mass_add_le (ν η : SignedMeasure X) :
    mass (ν + η) ≤ mass ν + mass η := by
  unfold mass
  rw [← measureReal_add_apply, measureReal_def, measureReal_def]
  exact ENNReal.toReal_mono (by finiteness)
    (VectorMeasure.variation_add_le Set.univ)

theorem mass_finset_sum_le {ι : Type*} (s : Finset ι)
    (ν : ι → SignedMeasure X) :
    mass (∑ i ∈ s, ν i) ≤ ∑ i ∈ s, mass (ν i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (mass_add_le _ _).trans (add_le_add_right ih _)

@[simp]
theorem mass_smul (c : ℝ) (ν : SignedMeasure X) :
    mass (c • ν) = |c| * mass ν := by
  unfold mass
  rw [VectorMeasure.variation_smul]
  simp [measureReal_def, ENNReal.toReal_mul]

/-! ### Absolute continuity of signed chains -/

/-- A signed chain is absolutely continuous when its total variation is.  This
is the formulation needed to transport almost-everywhere identities. -/
def IsAbsolutelyContinuous (ν : SignedMeasure X) (μ : Measure X) : Prop :=
  ν.variation ≪ μ

theorem isAbsolutelyContinuous_iff_totalVariation
    (ν : SignedMeasure X) (μ : Measure X) :
    IsAbsolutelyContinuous ν μ ↔ ν.totalVariation ≪ μ := by
  simp [IsAbsolutelyContinuous, SignedMeasure.totalVariation_eq_variation]

/-- Equivalence with the usual vector-measure null-set definition. -/
theorem isAbsolutelyContinuous_iff_vectorMeasure
    (ν : SignedMeasure X) (μ : Measure X) :
    IsAbsolutelyContinuous ν μ ↔ ν ≪ᵥ μ.toENNRealVectorMeasure := by
  rw [isAbsolutelyContinuous_iff_totalVariation,
    SignedMeasure.absolutelyContinuous_ennreal_iff]
  simp

@[simp]
theorem isAbsolutelyContinuous_zero (μ : Measure X) :
    IsAbsolutelyContinuous (0 : SignedMeasure X) μ := by
  simp [IsAbsolutelyContinuous]

theorem IsAbsolutelyContinuous.neg {ν : SignedMeasure X} {μ : Measure X}
    (hν : IsAbsolutelyContinuous ν μ) : IsAbsolutelyContinuous (-ν) μ := by
  simpa [IsAbsolutelyContinuous] using hν

theorem IsAbsolutelyContinuous.smul {ν : SignedMeasure X} {μ : Measure X}
    (hν : IsAbsolutelyContinuous ν μ) (c : ℝ) :
    IsAbsolutelyContinuous (c • ν) μ := by
  intro s hs
  rw [VectorMeasure.variation_smul]
  simp [hν hs]

theorem IsAbsolutelyContinuous.add {ν η : SignedMeasure X} {μ : Measure X}
    (hν : IsAbsolutelyContinuous ν μ) (hη : IsAbsolutelyContinuous η μ) :
    IsAbsolutelyContinuous (ν + η) μ := by
  intro s hs
  apply le_antisymm
  · calc
      (ν + η).variation s ≤ (ν.variation + η.variation) s :=
        VectorMeasure.variation_add_le s
      _ = 0 := by simp [hν hs, hη hs]
  · exact bot_le

theorem IsAbsolutelyContinuous.finsetSum {ι : Type*} (s : Finset ι)
    {ν : ι → SignedMeasure X} {μ : Measure X}
    (hν : ∀ i ∈ s, IsAbsolutelyContinuous (ν i) μ) :
    IsAbsolutelyContinuous (∑ i ∈ s, ν i) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hν a (by simp)).add (ih fun i hi ↦ hν i (by simp [hi]))

/-- Nonsingular pushforward preserves absolute continuity of signed chains. -/
theorem IsAbsolutelyContinuous.map {ν : SignedMeasure X} {μ : Measure X}
    {ξ : Measure Y} {f : X → Y} (hν : IsAbsolutelyContinuous ν μ)
    (hf : Measure.QuasiMeasurePreserving f μ ξ) :
    IsAbsolutelyContinuous (ν.map f) ξ := by
  exact (Measure.absolutelyContinuous_of_le
      VectorMeasure.variation_map_le).trans
    ((Measure.AbsolutelyContinuous.map hν hf.measurable).trans
      hf.absolutelyContinuous)

/-- Pushforward, packaged as a real linear map. -/
def pushforward (f : X → Y) : SignedMeasure X →ₗ[ℝ] SignedMeasure Y :=
  VectorMeasure.mapₗ f

@[simp]
theorem pushforward_apply (f : X → Y) (ν : SignedMeasure X) :
    pushforward f ν = ν.map f := rfl

/-- Functoriality of signed pushforward for measurable maps. -/
theorem map_map (ν : SignedMeasure X) {f : X → Y} {g : Y → Z}
    (hf : Measurable f) (hg : Measurable g) :
    (ν.map f).map g = ν.map (g ∘ f) := by
  ext s hs
  rw [VectorMeasure.map_apply _ hg hs,
    VectorMeasure.map_apply _ hf (hg hs),
    VectorMeasure.map_apply _ (hg.comp hf) hs]
  rfl

theorem map_fintype_sum {ι : Type*} [Fintype ι]
    (ν : ι → SignedMeasure X) (f : X → Y) :
    (∑ i, ν i).map f = ∑ i, (ν i).map f := by
  change VectorMeasure.mapGm f (∑ i, ν i) = ∑ i, VectorMeasure.mapGm f (ν i)
  simpa using map_sum (VectorMeasure.mapGm f) ν Finset.univ

/-- Pushforward does not increase total variation. -/
theorem mass_map_le (ν : SignedMeasure X) {f : X → Y} (hf : Measurable f) :
    mass (ν.map f) ≤ mass ν := by
  unfold mass
  rw [measureReal_def, measureReal_def]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).2
  calc
    (ν.map f).variation Set.univ ≤ (ν.variation.map f) Set.univ :=
      VectorMeasure.variation_map_le Set.univ
    _ = ν.variation Set.univ := by
      rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]

/-! ### Coordinate measure boundaries -/

/-- The five-term measure boundary from five-point to four-point orbit
coordinates. -/
def boundary4 : SignedMeasure U5 →ₗ[ℝ] SignedMeasure U4 :=
  ∑ i : Fin 5, ((-1 : ℝ) ^ i.val) •
    pushforward (face4At i)

theorem boundary4_apply (ν : SignedMeasure U5) :
    boundary4 ν =
      ∑ i : Fin 5, ((-1 : ℝ) ^ i.val) • ν.map (face4At i) := by
  simp [boundary4, pushforward]

/-- A pointwise convenient measurability certificate for the five faces. -/
theorem measurable_face4At (i : Fin 5) : Measurable (face4At i) := by
  fin_cases i
  · exact continuous_face4_0.measurable
  · exact continuous_face4_1.measurable
  · exact continuous_face4_2.measurable
  · exact continuous_face4_3.measurable
  · exact continuous_face4_4.measurable

/-! The six-point locus is a closed Pfaffian hypersurface inside its affine
chart.  Each normalized deletion formula is nevertheless continuous on the
generic subtype because every displayed denominator is one of its defining
nonvanishing coordinates. -/

theorem continuous_face5_0_measure : Continuous face5_0 := by
  apply Continuous.subtype_mk
  apply continuous_coord5_mk
  · change Continuous fun q : U6 ↦ q.1.u * q.1.x / (q.1.v * q.1.w)
    exact ((continuous_coord6_u.comp continuous_subtype_val).mul
      (continuous_coord6_x.comp continuous_subtype_val)).div₀
      ((continuous_coord6_v.comp continuous_subtype_val).mul
        (continuous_coord6_w.comp continuous_subtype_val))
      (fun q ↦ mul_ne_zero q.2.v_ne q.2.w_ne)
  · change Continuous fun q : U6 ↦ q.1.u * q.1.t / (q.1.w * q.1.s)
    exact ((continuous_coord6_u.comp continuous_subtype_val).mul
      (continuous_coord6_t.comp continuous_subtype_val)).div₀
      ((continuous_coord6_w.comp continuous_subtype_val).mul
        (continuous_coord6_s.comp continuous_subtype_val))
      (fun q ↦ mul_ne_zero q.2.w_ne q.2.s_ne)
  · change Continuous fun q : U6 ↦ q.1.y / (q.1.v * q.1.w)
    exact (continuous_coord6_y.comp continuous_subtype_val).div₀
      ((continuous_coord6_v.comp continuous_subtype_val).mul
        (continuous_coord6_w.comp continuous_subtype_val))
      (fun q ↦ mul_ne_zero q.2.v_ne q.2.w_ne)
  · change Continuous fun q : U6 ↦ q.1.z / (q.1.w * q.1.s)
    exact (continuous_coord6_z.comp continuous_subtype_val).div₀
      ((continuous_coord6_w.comp continuous_subtype_val).mul
        (continuous_coord6_s.comp continuous_subtype_val))
      (fun q ↦ mul_ne_zero q.2.w_ne q.2.s_ne)
  · change Continuous fun q : U6 ↦
      q.1.r * q.1.u / (q.1.v * q.1.w * q.1.s)
    exact ((continuous_coord6_r.comp continuous_subtype_val).mul
      (continuous_coord6_u.comp continuous_subtype_val)).div₀
      (((continuous_coord6_v.comp continuous_subtype_val).mul
        (continuous_coord6_w.comp continuous_subtype_val)).mul
          (continuous_coord6_s.comp continuous_subtype_val))
      (fun q ↦ mul_ne_zero (mul_ne_zero q.2.v_ne q.2.w_ne) q.2.s_ne)

theorem continuous_face5_1_measure : Continuous face5_1 := by
  apply Continuous.subtype_mk
  apply continuous_coord5_mk <;>
    first
    | exact (continuous_coord6_x.comp continuous_subtype_val).div₀
        (continuous_coord6_w.comp continuous_subtype_val) (fun q ↦ q.2.w_ne)
    | exact (continuous_coord6_t.comp continuous_subtype_val).div₀
        (continuous_coord6_w.comp continuous_subtype_val) (fun q ↦ q.2.w_ne)
    | exact (continuous_coord6_y.comp continuous_subtype_val).div₀
        (continuous_coord6_w.comp continuous_subtype_val) (fun q ↦ q.2.w_ne)
    | exact (continuous_coord6_z.comp continuous_subtype_val).div₀
        (continuous_coord6_w.comp continuous_subtype_val) (fun q ↦ q.2.w_ne)
    | exact (continuous_coord6_r.comp continuous_subtype_val).div₀
        (continuous_coord6_w.comp continuous_subtype_val) (fun q ↦ q.2.w_ne)

theorem continuous_face5_2_measure : Continuous face5_2 := by
  apply Continuous.subtype_mk
  apply continuous_coord5_mk <;>
    first
    | exact (continuous_coord6_v.comp continuous_subtype_val).div₀
        (continuous_coord6_u.comp continuous_subtype_val) (fun q ↦ q.2.u_ne)
    | exact (continuous_coord6_s.comp continuous_subtype_val).div₀
        (continuous_coord6_u.comp continuous_subtype_val) (fun q ↦ q.2.u_ne)
    | exact (continuous_coord6_y.comp continuous_subtype_val).div₀
        (continuous_coord6_u.comp continuous_subtype_val) (fun q ↦ q.2.u_ne)
    | exact (continuous_coord6_z.comp continuous_subtype_val).div₀
        (continuous_coord6_u.comp continuous_subtype_val) (fun q ↦ q.2.u_ne)
    | exact (continuous_coord6_r.comp continuous_subtype_val).div₀
        (continuous_coord6_u.comp continuous_subtype_val) (fun q ↦ q.2.u_ne)

theorem continuous_face5_3_measure : Continuous face5_3 := by
  apply Continuous.subtype_mk
  exact continuous_coord5_mk
    (continuous_coord6_v.comp continuous_subtype_val)
    (continuous_coord6_s.comp continuous_subtype_val)
    (continuous_coord6_x.comp continuous_subtype_val)
    (continuous_coord6_t.comp continuous_subtype_val)
    (continuous_coord6_r.comp continuous_subtype_val)

theorem continuous_face5_4_measure : Continuous face5_4 := by
  apply Continuous.subtype_mk
  exact continuous_coord5_mk
    (continuous_coord6_u.comp continuous_subtype_val)
    (continuous_coord6_s.comp continuous_subtype_val)
    (continuous_coord6_w.comp continuous_subtype_val)
    (continuous_coord6_t.comp continuous_subtype_val)
    (continuous_coord6_z.comp continuous_subtype_val)

theorem continuous_face5_5_measure : Continuous face5_5 := by
  apply Continuous.subtype_mk
  exact continuous_coord5_mk
    (continuous_coord6_u.comp continuous_subtype_val)
    (continuous_coord6_v.comp continuous_subtype_val)
    (continuous_coord6_w.comp continuous_subtype_val)
    (continuous_coord6_x.comp continuous_subtype_val)
    (continuous_coord6_y.comp continuous_subtype_val)

theorem measurable_face5At (i : Fin 6) : Measurable (face5At i) := by
  fin_cases i
  · exact continuous_face5_0_measure.measurable
  · exact continuous_face5_1_measure.measurable
  · exact continuous_face5_2_measure.measurable
  · exact continuous_face5_3_measure.measurable
  · exact continuous_face5_4_measure.measurable
  · exact continuous_face5_5_measure.measurable

/-- The six-term boundary from six-point to five-point coordinates. -/
def boundary5 : SignedMeasure U6 →ₗ[ℝ] SignedMeasure U5 :=
  ∑ i : Fin 6, ((-1 : ℝ) ^ i.val) • pushforward (face5At i)

theorem boundary5_apply (ν : SignedMeasure U6) :
    boundary5 ν =
      ∑ i : Fin 6, ((-1 : ℝ) ^ i.val) • ν.map (face5At i) := by
  simp [boundary5, pushforward]

theorem boundary4_expanded (ν : SignedMeasure U5) :
    boundary4 ν =
      ν.map face4_0 - ν.map face4_1 + ν.map face4_2 -
        ν.map face4_3 + ν.map face4_4 := by
  rw [boundary4_apply]
  simp [Fin.sum_univ_succ, face4At, neg_one_smul]
  norm_num [neg_one_smul]
  module

theorem boundary5_expanded (ν : SignedMeasure U6) :
    boundary5 ν =
      ν.map face5_0 - ν.map face5_1 + ν.map face5_2 -
        ν.map face5_3 + ν.map face5_4 - ν.map face5_5 := by
  rw [boundary5_apply]
  simp [Fin.sum_univ_succ, face5At, neg_one_smul]
  norm_num [neg_one_smul]
  module

theorem mass_boundary5_le (ν : SignedMeasure U6) :
    mass (boundary5 ν) ≤ 6 * mass ν := by
  classical
  rw [boundary5_apply]
  calc
    mass (∑ i : Fin 6, ((-1 : ℝ) ^ i.val) • ν.map (face5At i)) ≤
        ∑ i : Fin 6, mass (((-1 : ℝ) ^ i.val) • ν.map (face5At i)) := by
      induction (Finset.univ : Finset (Fin 6)) using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          exact (mass_add_le _ _).trans (add_le_add_right ih _)
    _ ≤ ∑ _i : Fin 6, mass ν := by
      apply Finset.sum_le_sum
      intro i _
      rw [mass_smul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact mass_map_le ν (measurable_face5At i)
    _ = 6 * mass ν := by simp

/-- Consecutive coordinate measure boundaries cancel. -/
theorem boundary4_boundary5 (ν : SignedMeasure U6) :
    boundary4 (boundary5 ν) = 0 := by
  rw [boundary5_expanded]
  simp only [map_sub, map_add]
  simp_rw [boundary4_expanded]
  simp_rw [map_map _ continuous_face5_0_measure.measurable
    continuous_face4_0.measurable,
    map_map _ continuous_face5_0_measure.measurable
      continuous_face4_1.measurable,
    map_map _ continuous_face5_0_measure.measurable
      continuous_face4_2.measurable,
    map_map _ continuous_face5_0_measure.measurable
      continuous_face4_3.measurable,
    map_map _ continuous_face5_0_measure.measurable
      continuous_face4_4.measurable,
    map_map _ continuous_face5_1_measure.measurable
      continuous_face4_0.measurable,
    map_map _ continuous_face5_1_measure.measurable
      continuous_face4_1.measurable,
    map_map _ continuous_face5_1_measure.measurable
      continuous_face4_2.measurable,
    map_map _ continuous_face5_1_measure.measurable
      continuous_face4_3.measurable,
    map_map _ continuous_face5_1_measure.measurable
      continuous_face4_4.measurable,
    map_map _ continuous_face5_2_measure.measurable
      continuous_face4_0.measurable,
    map_map _ continuous_face5_2_measure.measurable
      continuous_face4_1.measurable,
    map_map _ continuous_face5_2_measure.measurable
      continuous_face4_2.measurable,
    map_map _ continuous_face5_2_measure.measurable
      continuous_face4_3.measurable,
    map_map _ continuous_face5_2_measure.measurable
      continuous_face4_4.measurable,
    map_map _ continuous_face5_3_measure.measurable
      continuous_face4_0.measurable,
    map_map _ continuous_face5_3_measure.measurable
      continuous_face4_1.measurable,
    map_map _ continuous_face5_3_measure.measurable
      continuous_face4_2.measurable,
    map_map _ continuous_face5_3_measure.measurable
      continuous_face4_3.measurable,
    map_map _ continuous_face5_3_measure.measurable
      continuous_face4_4.measurable,
    map_map _ continuous_face5_4_measure.measurable
      continuous_face4_0.measurable,
    map_map _ continuous_face5_4_measure.measurable
      continuous_face4_1.measurable,
    map_map _ continuous_face5_4_measure.measurable
      continuous_face4_2.measurable,
    map_map _ continuous_face5_4_measure.measurable
      continuous_face4_3.measurable,
    map_map _ continuous_face5_4_measure.measurable
      continuous_face4_4.measurable,
    map_map _ continuous_face5_5_measure.measurable
      continuous_face4_0.measurable,
    map_map _ continuous_face5_5_measure.measurable
      continuous_face4_1.measurable,
    map_map _ continuous_face5_5_measure.measurable
      continuous_face4_2.measurable,
    map_map _ continuous_face5_5_measure.measurable
      continuous_face4_3.measurable,
    map_map _ continuous_face5_5_measure.measurable
      continuous_face4_4.measurable]
  have h01 : face4_0 ∘ face5_1 = face4_0 ∘ face5_0 :=
    funext face4_0_face5_1
  have h02 : face4_0 ∘ face5_2 = face4_1 ∘ face5_0 :=
    funext face4_0_face5_2
  have h03 : face4_0 ∘ face5_3 = face4_2 ∘ face5_0 :=
    funext face4_0_face5_3
  have h04 : face4_0 ∘ face5_4 = face4_3 ∘ face5_0 :=
    funext face4_0_face5_4
  have h05 : face4_0 ∘ face5_5 = face4_4 ∘ face5_0 :=
    funext face4_0_face5_5
  have h12 : face4_1 ∘ face5_2 = face4_1 ∘ face5_1 :=
    funext face4_1_face5_2
  have h13 : face4_1 ∘ face5_3 = face4_2 ∘ face5_1 :=
    funext face4_1_face5_3
  have h14 : face4_1 ∘ face5_4 = face4_3 ∘ face5_1 :=
    funext face4_1_face5_4
  have h15 : face4_1 ∘ face5_5 = face4_4 ∘ face5_1 :=
    funext face4_1_face5_5
  have h23 : face4_2 ∘ face5_3 = face4_2 ∘ face5_2 :=
    funext face4_2_face5_3
  have h24 : face4_2 ∘ face5_4 = face4_3 ∘ face5_2 :=
    funext face4_2_face5_4
  have h25 : face4_2 ∘ face5_5 = face4_4 ∘ face5_2 :=
    funext face4_2_face5_5
  have h34 : face4_3 ∘ face5_4 = face4_3 ∘ face5_3 :=
    funext face4_3_face5_4
  have h35 : face4_3 ∘ face5_5 = face4_4 ∘ face5_3 :=
    funext face4_3_face5_5
  have h45 : face4_4 ∘ face5_5 = face4_4 ∘ face5_4 :=
    funext face4_4_face5_5
  rw [h01, h02, h03, h04, h05, h12, h13, h14, h15, h23, h24,
    h25, h34, h35, h45]
  abel

theorem mass_boundary4_le (ν : SignedMeasure U5) :
    mass (boundary4 ν) ≤ 5 * mass ν := by
  classical
  rw [boundary4_apply]
  calc
    mass (∑ i : Fin 5, ((-1 : ℝ) ^ i.val) • ν.map (face4At i)) ≤
        ∑ i : Fin 5, mass (((-1 : ℝ) ^ i.val) • ν.map (face4At i)) := by
      induction (Finset.univ : Finset (Fin 5)) using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          exact (mass_add_le _ _).trans (add_le_add_right ih _)
    _ ≤ ∑ _i : Fin 5, mass ν := by
      apply Finset.sum_le_sum
      intro i _
      rw [mass_smul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact mass_map_le ν (measurable_face4At i)
    _ = 5 * mass ν := by simp

/-- Absolute continuity is preserved by the five-term boundary whenever its
face maps are nonsingular for the chosen reference measures. -/
theorem boundary4_isAbsolutelyContinuous {μ4 : Measure U4}
    {μ5 : Measure U5} (hfaces : Face4QuasiMeasurePreserving μ4 μ5)
    {ν : SignedMeasure U5} (hν : IsAbsolutelyContinuous ν μ5) :
    IsAbsolutelyContinuous (boundary4 ν) μ4 := by
  rw [boundary4_apply]
  apply IsAbsolutelyContinuous.finsetSum Finset.univ
  intro i _
  exact (hν.map (hfaces.at i)).smul ((-1 : ℝ) ^ i.val)

/-- The analogous absolute-continuity statement for the six-term boundary. -/
theorem boundary5_isAbsolutelyContinuous {μ5 : Measure U5}
    {μ6 : Measure U6} (hfaces : Face5QuasiMeasurePreserving μ5 μ6)
    {ν : SignedMeasure U6} (hν : IsAbsolutelyContinuous ν μ6) :
    IsAbsolutelyContinuous (boundary5 ν) μ5 := by
  rw [boundary5_apply]
  apply IsAbsolutelyContinuous.finsetSum Finset.univ
  intro i _
  exact (hν.map (hfaces.at i)).smul ((-1 : ℝ) ^ i.val)

/-! ### Alternating projections -/

/-- The elementary finite-group reindexing identity behind both alternating
projections. -/
theorem signedSum_mulRight {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℝ M]
    (F : Equiv.Perm (Fin n) → M) (τ : Equiv.Perm (Fin n)) :
    (∑ σ : Equiv.Perm (Fin n), permSign ℝ σ • F (σ * τ)) =
      permSign ℝ τ • ∑ σ : Equiv.Perm (Fin n), permSign ℝ σ • F σ := by
  classical
  have hcoeff (σ : Equiv.Perm (Fin n)) :
      permSign ℝ σ = permSign ℝ τ * permSign ℝ (σ * τ) := by
    rw [permSign_mul]
    symm
    calc
      permSign ℝ τ * (permSign ℝ σ * permSign ℝ τ) =
          permSign ℝ σ * (permSign ℝ τ * permSign ℝ τ) := by ring
      _ = permSign ℝ σ := by rw [permSign_sq, mul_one]
  calc
    (∑ σ, permSign ℝ σ • F (σ * τ)) =
        ∑ σ, permSign ℝ τ • (permSign ℝ (σ * τ) • F (σ * τ)) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [smul_smul, ← hcoeff]
    _ = permSign ℝ τ •
        ∑ σ, permSign ℝ (σ * τ) • F (σ * τ) := by
      rw [Finset.smul_sum]
    _ = permSign ℝ τ •
        ∑ σ, permSign ℝ σ • F σ := by
      have hsum := Equiv.sum_comp (Equiv.mulRight τ)
        (fun σ ↦ permSign ℝ σ • F σ)
      simpa using congrArg (fun x ↦ permSign ℝ τ • x) hsum

theorem signedSum_mulLeft {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℝ M]
    (F : Equiv.Perm (Fin n) → M) (τ : Equiv.Perm (Fin n)) :
    (∑ σ : Equiv.Perm (Fin n), permSign ℝ σ • F (τ * σ)) =
      permSign ℝ τ • ∑ σ : Equiv.Perm (Fin n), permSign ℝ σ • F σ := by
  classical
  have hcoeff (σ : Equiv.Perm (Fin n)) :
      permSign ℝ σ = permSign ℝ τ * permSign ℝ (τ * σ) := by
    rw [permSign_mul]
    symm
    calc
      permSign ℝ τ * (permSign ℝ τ * permSign ℝ σ) =
          (permSign ℝ τ * permSign ℝ τ) * permSign ℝ σ := by ring
      _ = permSign ℝ σ := by rw [permSign_sq, one_mul]
  calc
    (∑ σ, permSign ℝ σ • F (τ * σ)) =
        ∑ σ, permSign ℝ τ • (permSign ℝ (τ * σ) • F (τ * σ)) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [smul_smul, ← hcoeff]
    _ = permSign ℝ τ •
        ∑ σ, permSign ℝ (τ * σ) • F (τ * σ) := by
      rw [Finset.smul_sum]
    _ = permSign ℝ τ •
        ∑ σ, permSign ℝ σ • F σ := by
      have hsum := Equiv.sum_comp (Equiv.mulLeft τ)
        (fun σ ↦ permSign ℝ σ • F σ)
      simpa using congrArg (fun x ↦ permSign ℝ τ • x) hsum

/-- Alternation of signed measures on the normalized five-point chart. -/
def alternation4 : SignedMeasure U5 →ₗ[ℝ] SignedMeasure U5 :=
  (1 / (Nat.factorial 5 : ℝ)) •
    ∑ σ : Equiv.Perm (Fin 5),
      permSign ℝ σ • pushforward (permute5 σ)

theorem alternation4_apply (ν : SignedMeasure U5) :
    alternation4 ν =
      (1 / (Nat.factorial 5 : ℝ)) •
        ∑ σ : Equiv.Perm (Fin 5),
          permSign ℝ σ • ν.map (permute5 σ) := by
  simp [alternation4, pushforward]

/-- Alternation of signed measures on the normalized four-point chart. -/
def alternation3 : SignedMeasure U4 →ₗ[ℝ] SignedMeasure U4 :=
  (1 / (Nat.factorial 4 : ℝ)) •
    ∑ σ : Equiv.Perm (Fin 4),
      permSign ℝ σ • pushforward (permute4 σ)

theorem alternation3_apply (ν : SignedMeasure U4) :
    alternation3 ν =
      (1 / (Nat.factorial 4 : ℝ)) •
        ∑ σ : Equiv.Perm (Fin 4),
          permSign ℝ σ • ν.map (permute4 σ) := by
  simp [alternation3, pushforward]

def IsAlternating4 (ν : SignedMeasure U5) : Prop :=
  ∀ σ : Equiv.Perm (Fin 5),
    ν.map (permute5 σ) = permSign ℝ σ • ν

def IsAlternating3 (ν : SignedMeasure U4) : Prop :=
  ∀ σ : Equiv.Perm (Fin 4),
    ν.map (permute4 σ) = permSign ℝ σ • ν

theorem alternation4_covariant (ν : SignedMeasure U5)
    (τ : Equiv.Perm (Fin 5)) :
    (alternation4 ν).map (permute5 τ) =
      permSign ℝ τ • alternation4 ν := by
  classical
  rw [alternation4_apply, VectorMeasure.map_smul]
  rw [map_fintype_sum]
  simp only [VectorMeasure.map_smul]
  have hcomp (σ : Equiv.Perm (Fin 5)) :
      permute5 τ ∘ permute5 σ = permute5 (σ * τ) :=
    funext fun q ↦ permute5_mul σ τ q
  simp_rw [map_map _ (measurable_permute5 _) (measurable_permute5 _), hcomp]
  rw [signedSum_mulRight
    (F := fun ρ ↦ ν.map (permute5 ρ)) τ]
  module

theorem alternation3_covariant (ν : SignedMeasure U4)
    (τ : Equiv.Perm (Fin 4)) :
    (alternation3 ν).map (permute4 τ) =
      permSign ℝ τ • alternation3 ν := by
  classical
  rw [alternation3_apply, VectorMeasure.map_smul]
  rw [map_fintype_sum]
  simp only [VectorMeasure.map_smul]
  have hcomp (σ : Equiv.Perm (Fin 4)) :
      permute4 τ ∘ permute4 σ = permute4 (σ * τ) :=
    funext fun q ↦ permute4_mul σ τ q
  simp_rw [map_map _ (measurable_permute4 _) (measurable_permute4 _), hcomp]
  rw [signedSum_mulRight
    (F := fun ρ ↦ ν.map (permute4 ρ)) τ]
  module

/-- Alternating averaging absorbs a permutation applied before the average. -/
theorem alternation4_map_permute (ν : SignedMeasure U5)
    (τ : Equiv.Perm (Fin 5)) :
    alternation4 (ν.map (permute5 τ)) =
      permSign ℝ τ • alternation4 ν := by
  classical
  rw [alternation4_apply, alternation4_apply]
  have hcomp (σ : Equiv.Perm (Fin 5)) :
      permute5 σ ∘ permute5 τ = permute5 (τ * σ) :=
    funext fun q ↦ permute5_mul τ σ q
  simp_rw [map_map _ (measurable_permute5 _) (measurable_permute5 _), hcomp]
  rw [signedSum_mulLeft
    (F := fun ρ ↦ ν.map (permute5 ρ)) τ]
  module

theorem alternation3_map_permute (ν : SignedMeasure U4)
    (τ : Equiv.Perm (Fin 4)) :
    alternation3 (ν.map (permute4 τ)) =
      permSign ℝ τ • alternation3 ν := by
  classical
  rw [alternation3_apply, alternation3_apply]
  have hcomp (σ : Equiv.Perm (Fin 4)) :
      permute4 σ ∘ permute4 τ = permute4 (τ * σ) :=
    funext fun q ↦ permute4_mul τ σ q
  simp_rw [map_map _ (measurable_permute4 _) (measurable_permute4 _), hcomp]
  rw [signedSum_mulLeft
    (F := fun ρ ↦ ν.map (permute4 ρ)) τ]
  module

theorem alternation4_isAlternating (ν : SignedMeasure U5) :
    IsAlternating4 (alternation4 ν) :=
  alternation4_covariant ν

theorem alternation3_isAlternating (ν : SignedMeasure U4) :
    IsAlternating3 (alternation3 ν) :=
  alternation3_covariant ν

theorem alternation4_isAbsolutelyContinuous {μ5 : Measure U5}
    (hperm : ∀ σ : Equiv.Perm (Fin 5),
      Measure.QuasiMeasurePreserving (permute5 σ) μ5 μ5)
    {ν : SignedMeasure U5} (hν : IsAbsolutelyContinuous ν μ5) :
    IsAbsolutelyContinuous (alternation4 ν) μ5 := by
  rw [alternation4_apply]
  apply IsAbsolutelyContinuous.smul
  apply IsAbsolutelyContinuous.finsetSum Finset.univ
  intro σ _
  exact (hν.map (hperm σ)).smul (permSign ℝ σ)

theorem alternation3_isAbsolutelyContinuous {μ4 : Measure U4}
    (hperm : ∀ σ : Equiv.Perm (Fin 4),
      Measure.QuasiMeasurePreserving (permute4 σ) μ4 μ4)
    {ν : SignedMeasure U4} (hν : IsAbsolutelyContinuous ν μ4) :
    IsAbsolutelyContinuous (alternation3 ν) μ4 := by
  rw [alternation3_apply]
  apply IsAbsolutelyContinuous.smul
  apply IsAbsolutelyContinuous.finsetSum Finset.univ
  intro σ _
  exact (hν.map (hperm σ)).smul (permSign ℝ σ)

/-- The simplicial boundary of an alternating five-point measure is an
alternating four-point measure.  For each deleted vertex we extend the given
four-point permutation by fixing that vertex. -/
theorem boundary4_preserves_alternating {ν : SignedMeasure U5}
    (hν : IsAlternating4 ν) : IsAlternating3 (boundary4 ν) := by
  classical
  intro τ
  have hterm (i : Fin 5) :
      (ν.map (face4At i)).map (permute4 τ) =
        permSign ℝ τ • ν.map (face4At i) := by
    let σ : Equiv.Perm (Fin 5) := extendPermAt i τ
    have hcomp : permute4 τ ∘ face4At i = face4At i ∘ permute5 σ := by
      funext q
      have hface := face4At_permute5 σ i q
      simpa [σ] using hface.symm
    rw [map_map _ (measurable_face4At i) (measurable_permute4 τ), hcomp,
      ← map_map _ (measurable_permute5 σ) (measurable_face4At i), hν σ,
      VectorMeasure.map_smul, permSign_extendPermAt]
  rw [boundary4_apply, map_fintype_sum]
  simp only [VectorMeasure.map_smul]
  simp_rw [hterm]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  module

/-- After alternating the target, reindexing a five-point measure before
taking its boundary contributes precisely the sign of the reindexing. -/
theorem alternation3_boundary4_map_permute (ν : SignedMeasure U5)
    (σ : Equiv.Perm (Fin 5)) :
    alternation3 (boundary4 (ν.map (permute5 σ))) =
      permSign ℝ σ • alternation3 (boundary4 ν) := by
  classical
  have hterm (i : Fin 5) :
      alternation3 ((ν.map (permute5 σ)).map (face4At i)) =
        permSign ℝ (deletePerm σ i) •
          alternation3 (ν.map (face4At (σ i))) := by
    have hcomp : face4At i ∘ permute5 σ =
        permute4 (deletePerm σ i) ∘ face4At (σ i) :=
      funext fun q ↦ face4At_permute5 σ i q
    rw [map_map _ (measurable_permute5 σ) (measurable_face4At i), hcomp,
      ← map_map _ (measurable_face4At (σ i))
        (measurable_permute4 (deletePerm σ i)),
      alternation3_map_permute]
  rw [boundary4_apply, boundary4_apply]
  simp only [map_sum, LinearMap.map_smul]
  simp_rw [hterm]
  calc
    (∑ i : Fin 5, ((-1 : ℝ) ^ i.val) •
        (permSign ℝ (deletePerm σ i) •
          alternation3 (ν.map (face4At (σ i))))) =
        ∑ i : Fin 5, permSign ℝ σ •
          (((-1 : ℝ) ^ (σ i).val) •
            alternation3 (ν.map (face4At (σ i)))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul, smul_smul, deletePerm_incidence_sign_cast]
      ring_nf
    _ = permSign ℝ σ •
        ∑ i : Fin 5, ((-1 : ℝ) ^ (σ i).val) •
          alternation3 (ν.map (face4At (σ i))) := by
      rw [Finset.smul_sum]
    _ = permSign ℝ σ •
        ∑ i : Fin 5, ((-1 : ℝ) ^ i.val) •
          alternation3 (ν.map (face4At i)) := by
      congr 1
      simpa using Equiv.sum_comp σ
        (fun i : Fin 5 ↦ ((-1 : ℝ) ^ i.val) •
          alternation3 (ν.map (face4At i)))

theorem alternation4_fixed {ν : SignedMeasure U5} (hν : IsAlternating4 ν) :
    alternation4 ν = ν := by
  classical
  rw [alternation4_apply]
  calc
    (1 / (Nat.factorial 5 : ℝ)) •
        (∑ σ : Equiv.Perm (Fin 5),
          permSign ℝ σ • ν.map (permute5 σ)) =
        (1 / (Nat.factorial 5 : ℝ)) •
          ∑ _σ : Equiv.Perm (Fin 5), ν := by
      congr 1
      apply Finset.sum_congr rfl
      intro σ _
      rw [hν σ, smul_smul, permSign_sq, one_smul]
    _ = ν := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin]
      norm_num
      module

theorem alternation3_fixed {ν : SignedMeasure U4} (hν : IsAlternating3 ν) :
    alternation3 ν = ν := by
  classical
  rw [alternation3_apply]
  calc
    (1 / (Nat.factorial 4 : ℝ)) •
        (∑ σ : Equiv.Perm (Fin 4),
          permSign ℝ σ • ν.map (permute4 σ)) =
        (1 / (Nat.factorial 4 : ℝ)) •
          ∑ _σ : Equiv.Perm (Fin 4), ν := by
      congr 1
      apply Finset.sum_congr rfl
      intro σ _
      rw [hν σ, smul_smul, permSign_sq, one_smul]
    _ = ν := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin]
      norm_num
      module

/-- The coordinate boundary commutes with alternating projection. -/
theorem boundary4_alternation4 (ν : SignedMeasure U5) :
    boundary4 (alternation4 ν) = alternation3 (boundary4 ν) := by
  classical
  have hfixed :
      alternation3 (boundary4 (alternation4 ν)) =
        boundary4 (alternation4 ν) :=
    alternation3_fixed
      (boundary4_preserves_alternating (alternation4_isAlternating ν))
  calc
    boundary4 (alternation4 ν) =
        alternation3 (boundary4 (alternation4 ν)) := hfixed.symm
    _ = (1 / (Nat.factorial 5 : ℝ)) •
        ∑ σ : Equiv.Perm (Fin 5), permSign ℝ σ •
          alternation3 (boundary4 (ν.map (permute5 σ))) := by
      rw [alternation4_apply]
      simp only [LinearMap.map_smul, map_sum]
    _ = (1 / (Nat.factorial 5 : ℝ)) •
        ∑ _σ : Equiv.Perm (Fin 5),
          alternation3 (boundary4 ν) := by
      congr 1
      apply Finset.sum_congr rfl
      intro σ _
      rw [alternation3_boundary4_map_permute, smul_smul,
        permSign_sq, one_smul]
    _ = alternation3 (boundary4 ν) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin]
      norm_num
      module

@[simp]
theorem alternation4_idempotent (ν : SignedMeasure U5) :
    alternation4 (alternation4 ν) = alternation4 ν :=
  alternation4_fixed (alternation4_isAlternating ν)

@[simp]
theorem alternation3_idempotent (ν : SignedMeasure U4) :
    alternation3 (alternation3 ν) = alternation3 ν :=
  alternation3_fixed (alternation3_isAlternating ν)

theorem abs_permSign_real {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    |permSign ℝ σ| = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    simp [permSign, h]

theorem mass_alternation4_le (ν : SignedMeasure U5) :
    mass (alternation4 ν) ≤ mass ν := by
  classical
  rw [alternation4_apply, mass_smul]
  norm_num [abs_of_nonneg]
  calc
    (1 / 120 : ℝ) * mass
        (∑ σ : Equiv.Perm (Fin 5),
          permSign ℝ σ • ν.map (permute5 σ)) ≤
        (1 / 120 : ℝ) *
          ∑ σ : Equiv.Perm (Fin 5),
            mass (permSign ℝ σ • ν.map (permute5 σ)) := by
      exact mul_le_mul_of_nonneg_left
        (mass_finset_sum_le Finset.univ
          (fun σ : Equiv.Perm (Fin 5) ↦
            permSign ℝ σ • ν.map (permute5 σ))) (by norm_num)
    _ ≤ (1 / 120 : ℝ) *
        ∑ _σ : Equiv.Perm (Fin 5), mass ν := by
      gcongr with σ
      rw [mass_smul, abs_permSign_real, one_mul]
      exact mass_map_le ν (measurable_permute5 σ)
    _ = mass ν := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin]
      norm_num
      ring

theorem mass_alternation3_le (ν : SignedMeasure U4) :
    mass (alternation3 ν) ≤ mass ν := by
  classical
  rw [alternation3_apply, mass_smul]
  norm_num [abs_of_nonneg]
  calc
    (1 / 24 : ℝ) * mass
        (∑ σ : Equiv.Perm (Fin 4),
          permSign ℝ σ • ν.map (permute4 σ)) ≤
        (1 / 24 : ℝ) *
          ∑ σ : Equiv.Perm (Fin 4),
            mass (permSign ℝ σ • ν.map (permute4 σ)) := by
      exact mul_le_mul_of_nonneg_left
        (mass_finset_sum_le Finset.univ
          (fun σ : Equiv.Perm (Fin 4) ↦
            permSign ℝ σ • ν.map (permute4 σ))) (by norm_num)
    _ ≤ (1 / 24 : ℝ) *
        ∑ _σ : Equiv.Perm (Fin 4), mass ν := by
      gcongr with σ
      rw [mass_smul, abs_permSign_real, one_mul]
      exact mass_map_le ν (measurable_permute4 σ)
    _ = mass ν := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin]
      norm_num
      ring

/-! ### Dirac realization of orbit chains -/

/-- The unit real Dirac vector measure, regarded as a signed measure. -/
def signedDirac (x : X) : SignedMeasure X := VectorMeasure.dirac x 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E]

theorem integrable_signedDirac [MeasurableSingletonClass X]
    (f : X → E) (x : X) : (signedDirac x).Integrable f := by
  simpa [signedDirac, VectorMeasure.Integrable] using
    (MeasureTheory.integrable_dirac (a := x) (f := f) (by simp))

@[simp]
theorem integral_signedDirac [MeasurableSingletonClass X]
    (f : X → E) (x : X) :
    (∫ᵛ y, f y ∂<•(signedDirac x)) = f x := by
  simp [signedDirac]

@[simp]
theorem map_signedDirac (x : X) (f : X → Y) (hf : Measurable f) :
    (signedDirac x).map f = signedDirac (f x) := by
  classical
  ext s hs
  have hpre : MeasurableSet (f ⁻¹' s) := hf hs
  rw [VectorMeasure.map_apply _ hf hs]
  change (if MeasurableSet (f ⁻¹' s) ∧ x ∈ f ⁻¹' s then 1 else 0) =
    if MeasurableSet s ∧ f x ∈ s then 1 else 0
  by_cases hx : f x ∈ s <;> simp [hpre, hs, hx]

@[simp]
theorem mass_signedDirac (x : X) : mass (signedDirac x) = 1 := by
  simp [mass, signedDirac]

/-- Pointwise alternation on the normalized five-point chart. -/
def IsAlternatingFunction5 (f : U5 → E) : Prop :=
  ∀ σ : Equiv.Perm (Fin 5), ∀ q : U5,
    f (permute5 σ q) = permSign ℝ σ • f q

/-- Pointwise alternation on the normalized four-point chart. -/
def IsAlternatingFunction4 (f : U4 → E) : Prop :=
  ∀ σ : Equiv.Perm (Fin 4), ∀ q : U4,
    f (permute4 σ q) = permSign ℝ σ • f q

theorem reducedR_isAlternatingFunction5 :
    IsAlternatingFunction5
      (fun q : U5 ↦ AffineCocycle.reducedR (matrix5 q.1)) := by
  intro σ q
  change AffineCocycle.reducedR (matrix5 (permute5 σ q).1) =
    permSign ℝ σ • AffineCocycle.reducedR (matrix5 q.1)
  rw [reducedR_permute5]
  simp [permSign, Complex.real_smul]

/-- Alternated Dirac measure attached to a generic five-point orbit. -/
def diracConfig5 (x : OrbitChain.GenericConfig 5) : SignedMeasure U5 :=
  alternation4 (signedDirac (orbitCoord5 x))

/-- Alternated Dirac measure attached to a generic four-point orbit. -/
def diracConfig4 (x : OrbitChain.GenericConfig 4) : SignedMeasure U4 :=
  alternation3 (signedDirac (orbitCoord4 x))

/-- Integrating an alternating function against the alternated Dirac chain
recovers its value at the orbit coordinate. -/
theorem integral_diracConfig5 (f : U5 → E)
    (hf : IsAlternatingFunction5 f)
    (x : OrbitChain.GenericConfig 5) :
    (∫ᵛ q, f q ∂<•(diracConfig5 x)) = f (orbitCoord5 x) := by
  rw [diracConfig5, alternation4_apply]
  simp_rw [map_signedDirac _ _ (measurable_permute5 _)]
  rw [VectorMeasure.integral_smul_vectorMeasure]
  rw [VectorMeasure.integral_finsetSum_vectorMeasure]
  · simp_rw [VectorMeasure.integral_smul_vectorMeasure,
      integral_signedDirac]
    calc
      (1 / 120 : ℝ) •
          ∑ σ : Equiv.Perm (Fin 5),
            permSign ℝ σ • f (permute5 σ (orbitCoord5 x)) =
          (1 / 120 : ℝ) •
            ∑ _σ : Equiv.Perm (Fin 5), f (orbitCoord5 x) := by
        congr 1
        apply Finset.sum_congr rfl
        intro σ _
        rw [hf σ, smul_smul, permSign_sq, one_smul]
      _ = f (orbitCoord5 x) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
          Fintype.card_fin]
        rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
        norm_num
  · intro σ _
    exact (integrable_signedDirac f _).smul_vectorMeasure _

theorem integral_diracConfig4 (f : U4 → E)
    (hf : IsAlternatingFunction4 f)
    (x : OrbitChain.GenericConfig 4) :
    (∫ᵛ q, f q ∂<•(diracConfig4 x)) = f (orbitCoord4 x) := by
  rw [diracConfig4, alternation3_apply]
  simp_rw [map_signedDirac _ _ (measurable_permute4 _)]
  rw [VectorMeasure.integral_smul_vectorMeasure]
  rw [VectorMeasure.integral_finsetSum_vectorMeasure]
  · simp_rw [VectorMeasure.integral_smul_vectorMeasure,
      integral_signedDirac]
    calc
      (1 / 24 : ℝ) •
          ∑ σ : Equiv.Perm (Fin 4),
            permSign ℝ σ • f (permute4 σ (orbitCoord4 x)) =
          (1 / 24 : ℝ) •
            ∑ _σ : Equiv.Perm (Fin 4), f (orbitCoord4 x) := by
        congr 1
        apply Finset.sum_congr rfl
        intro σ _
        rw [hf σ, smul_smul, permSign_sq, one_smul]
      _ = f (orbitCoord4 x) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
          Fintype.card_fin]
        rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
        norm_num
  · intro σ _
    exact (integrable_signedDirac f _).smul_vectorMeasure _

theorem integrable_diracConfig5 (f : U5 → E)
    (x : OrbitChain.GenericConfig 5) :
    (diracConfig5 x).Integrable f := by
  rw [diracConfig5, alternation4_apply]
  apply VectorMeasure.Integrable.smul_vectorMeasure
  apply VectorMeasure.Integrable.finsetSum_vectorMeasure
  intro σ _
  rw [map_signedDirac _ _ (measurable_permute5 σ)]
  exact (integrable_signedDirac f _).smul_vectorMeasure _

theorem integrable_diracConfig4 (f : U4 → E)
    (x : OrbitChain.GenericConfig 4) :
    (diracConfig4 x).Integrable f := by
  rw [diracConfig4, alternation3_apply]
  apply VectorMeasure.Integrable.smul_vectorMeasure
  apply VectorMeasure.Integrable.finsetSum_vectorMeasure
  intro σ _
  rw [map_signedDirac _ _ (measurable_permute4 σ)]
  exact (integrable_signedDirac f _).smul_vectorMeasure _

@[simp]
theorem diracConfig5_smulGeneric (g : SymplecticGroup)
    (x : OrbitChain.GenericConfig 5) :
    diracConfig5 (OrbitChain.smulGeneric g x) = diracConfig5 x := by
  simp [diracConfig5]

@[simp]
theorem diracConfig4_smulGeneric (g : SymplecticGroup)
    (x : OrbitChain.GenericConfig 4) :
    diracConfig4 (OrbitChain.smulGeneric g x) = diracConfig4 x := by
  simp [diracConfig4]

theorem diracConfig5_permuteGeneric (σ : Equiv.Perm (Fin 5))
    (x : OrbitChain.GenericConfig 5) :
    diracConfig5 (OrbitChain.permuteGeneric σ x) =
      permSign ℝ σ • diracConfig5 x := by
  rw [diracConfig5, orbitCoord5_permuteGeneric]
  rw [← map_signedDirac _ _ (measurable_permute5 σ),
    alternation4_map_permute]
  rfl

theorem diracConfig4_permuteGeneric (σ : Equiv.Perm (Fin 4))
    (x : OrbitChain.GenericConfig 4) :
    diracConfig4 (OrbitChain.permuteGeneric σ x) =
      permSign ℝ σ • diracConfig4 x := by
  rw [diracConfig4, orbitCoord4_permuteGeneric]
  rw [← map_signedDirac _ _ (measurable_permute4 σ),
    alternation3_map_permute]
  rfl

theorem mass_diracConfig5_le_one (x : OrbitChain.GenericConfig 5) :
    mass (diracConfig5 x) ≤ 1 := by
  exact (mass_alternation4_le _).trans_eq (mass_signedDirac _)

theorem mass_diracConfig4_le_one (x : OrbitChain.GenericConfig 4) :
    mass (diracConfig4 x) ≤ 1 := by
  exact (mass_alternation3_le _).trans_eq (mass_signedDirac _)

theorem boundary4_signedDirac (q : U5) :
    boundary4 (signedDirac q) =
      ∑ i : Fin 5, ((-1 : ℝ) ^ i.val) •
        signedDirac (face4At i q) := by
  rw [boundary4_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_signedDirac _ _ (measurable_face4At i)]

/-- The alternated Dirac assignment commutes with the simplicial boundary on
each generic generator. -/
theorem boundary4_diracConfig5 (x : OrbitChain.GenericConfig 5) :
    boundary4 (diracConfig5 x) =
      ∑ i : Fin 5, ((-1 : ℝ) ^ i.val) •
        diracConfig4 (OrbitChain.face i x) := by
  rw [diracConfig5, boundary4_alternation4, boundary4_signedDirac]
  simp only [map_sum, LinearMap.map_smul, diracConfig4]
  apply Finset.sum_congr rfl
  intro i _
  rw [orbitCoord4_face]

/-- Linear extension of the Dirac assignment before imposing orbit
relations. -/
def rawDirac5 : OrbitChain.Raw ℝ 5 →ₗ[ℝ] SignedMeasure U5 :=
  Finsupp.linearCombination ℝ diracConfig5

def rawDirac4 : OrbitChain.Raw ℝ 4 →ₗ[ℝ] SignedMeasure U4 :=
  Finsupp.linearCombination ℝ diracConfig4

@[simp]
theorem rawDirac5_generator (x : OrbitChain.GenericConfig 5) :
    rawDirac5 (OrbitChain.generator x) = diracConfig5 x := by
  simp [rawDirac5, OrbitChain.generator]

@[simp]
theorem rawDirac4_generator (x : OrbitChain.GenericConfig 4) :
    rawDirac4 (OrbitChain.generator x) = diracConfig4 x := by
  simp [rawDirac4, OrbitChain.generator]

theorem rawDirac5_apply (c : OrbitChain.Raw ℝ 5) :
    rawDirac5 c =
      ∑ x ∈ c.support, c x • diracConfig5 x := by
  rw [rawDirac5, Finsupp.linearCombination_apply]
  rfl

theorem rawDirac4_apply (c : OrbitChain.Raw ℝ 4) :
    rawDirac4 c =
      ∑ x ∈ c.support, c x • diracConfig4 x := by
  rw [rawDirac4, Finsupp.linearCombination_apply]
  rfl

/-- The raw Dirac realization does not increase coefficient mass. -/
theorem mass_rawDirac5_le (c : OrbitChain.Raw ℝ 5) :
    mass (rawDirac5 c) ≤ OrbitChain.rawMass c := by
  rw [rawDirac5_apply, OrbitChain.rawMass]
  calc
    mass (∑ x ∈ c.support, c x • diracConfig5 x) ≤
        ∑ x ∈ c.support, mass (c x • diracConfig5 x) :=
      mass_finset_sum_le c.support
        (fun x ↦ c x • diracConfig5 x)
    _ ≤ ∑ x ∈ c.support, |c x| := by
      gcongr with x hx
      rw [mass_smul]
      exact mul_le_of_le_one_right (abs_nonneg _) (mass_diracConfig5_le_one x)

/-- The four-point raw Dirac realization does not increase coefficient mass. -/
theorem mass_rawDirac4_le (c : OrbitChain.Raw ℝ 4) :
    mass (rawDirac4 c) ≤ OrbitChain.rawMass c := by
  rw [rawDirac4_apply, OrbitChain.rawMass]
  calc
    mass (∑ x ∈ c.support, c x • diracConfig4 x) ≤
        ∑ x ∈ c.support, mass (c x • diracConfig4 x) :=
      mass_finset_sum_le c.support
        (fun x ↦ c x • diracConfig4 x)
    _ ≤ ∑ x ∈ c.support, |c x| := by
      gcongr with x hx
      rw [mass_smul]
      exact mul_le_of_le_one_right (abs_nonneg _) (mass_diracConfig4_le_one x)

theorem integrable_rawDirac5 (f : U5 → E)
    (c : OrbitChain.Raw ℝ 5) :
    (rawDirac5 c).Integrable f := by
  rw [rawDirac5_apply]
  apply VectorMeasure.Integrable.finsetSum_vectorMeasure
  intro x _
  exact (integrable_diracConfig5 f x).smul_vectorMeasure _

theorem integrable_rawDirac4 (f : U4 → E)
    (c : OrbitChain.Raw ℝ 4) :
    (rawDirac4 c).Integrable f := by
  rw [rawDirac4_apply]
  apply VectorMeasure.Integrable.finsetSum_vectorMeasure
  intro x _
  exact (integrable_diracConfig4 f x).smul_vectorMeasure _

theorem integral_rawDirac5 (f : U5 → E)
    (hf : IsAlternatingFunction5 f) (c : OrbitChain.Raw ℝ 5) :
    (∫ᵛ q, f q ∂<•(rawDirac5 c)) =
      ∑ x ∈ c.support, c x • f (orbitCoord5 x) := by
  rw [rawDirac5_apply]
  rw [VectorMeasure.integral_finsetSum_vectorMeasure]
  · simp_rw [VectorMeasure.integral_smul_vectorMeasure,
      integral_diracConfig5 f hf]
  · intro x _
    exact (integrable_diracConfig5 f x).smul_vectorMeasure _

theorem integral_rawDirac4 (f : U4 → E)
    (hf : IsAlternatingFunction4 f) (c : OrbitChain.Raw ℝ 4) :
    (∫ᵛ q, f q ∂<•(rawDirac4 c)) =
      ∑ x ∈ c.support, c x • f (orbitCoord4 x) := by
  rw [rawDirac4_apply]
  rw [VectorMeasure.integral_finsetSum_vectorMeasure]
  · simp_rw [VectorMeasure.integral_smul_vectorMeasure,
      integral_diracConfig4 f hf]
  · intro x _
    exact (integrable_diracConfig4 f x).smul_vectorMeasure _

/-! ### Evaluation of alternating functions on orbit chains -/

def rawEvaluation5 (f : U5 → E) :
    OrbitChain.Raw ℝ 5 →ₗ[ℝ] E :=
  Finsupp.linearCombination ℝ (fun x ↦ f (orbitCoord5 x))

def rawEvaluation4 (f : U4 → E) :
    OrbitChain.Raw ℝ 4 →ₗ[ℝ] E :=
  Finsupp.linearCombination ℝ (fun x ↦ f (orbitCoord4 x))

@[simp]
theorem rawEvaluation5_generator (f : U5 → E)
    (x : OrbitChain.GenericConfig 5) :
    rawEvaluation5 f (OrbitChain.generator x) = f (orbitCoord5 x) := by
  simp [rawEvaluation5, OrbitChain.generator]

@[simp]
theorem rawEvaluation4_generator (f : U4 → E)
    (x : OrbitChain.GenericConfig 4) :
    rawEvaluation4 f (OrbitChain.generator x) = f (orbitCoord4 x) := by
  simp [rawEvaluation4, OrbitChain.generator]

theorem relations5_le_rawEvaluation5_ker (f : U5 → E)
    (hf : IsAlternatingFunction5 f) :
    OrbitChain.relations ℝ 5 ≤ LinearMap.ker (rawEvaluation5 f) := by
  rw [OrbitChain.relations, Submodule.span_le]
  intro c hc
  rcases hc with hc | hc
  · rcases hc with ⟨g, x, rfl⟩
    change rawEvaluation5 f (OrbitChain.groupRelation ℝ g x) = 0
    rw [OrbitChain.groupRelation, map_sub, rawEvaluation5_generator,
      rawEvaluation5_generator, orbitCoord5_smulGeneric, sub_self]
  · rcases hc with ⟨σ, x, rfl⟩
    change rawEvaluation5 f (OrbitChain.permutationRelation ℝ σ x) = 0
    rw [OrbitChain.permutationRelation, map_sub, map_smul,
      rawEvaluation5_generator, rawEvaluation5_generator,
      orbitCoord5_permuteGeneric, hf σ, sub_self]

theorem relations4_le_rawEvaluation4_ker (f : U4 → E)
    (hf : IsAlternatingFunction4 f) :
    OrbitChain.relations ℝ 4 ≤ LinearMap.ker (rawEvaluation4 f) := by
  rw [OrbitChain.relations, Submodule.span_le]
  intro c hc
  rcases hc with hc | hc
  · rcases hc with ⟨g, x, rfl⟩
    change rawEvaluation4 f (OrbitChain.groupRelation ℝ g x) = 0
    rw [OrbitChain.groupRelation, map_sub, rawEvaluation4_generator,
      rawEvaluation4_generator, orbitCoord4_smulGeneric, sub_self]
  · rcases hc with ⟨σ, x, rfl⟩
    change rawEvaluation4 f (OrbitChain.permutationRelation ℝ σ x) = 0
    rw [OrbitChain.permutationRelation, map_sub, map_smul,
      rawEvaluation4_generator, rawEvaluation4_generator,
      orbitCoord4_permuteGeneric, hf σ, sub_self]

def evaluation5 (f : U5 → E) (hf : IsAlternatingFunction5 f) :
    OrbitChain.Module ℝ 5 →ₗ[ℝ] E :=
  (OrbitChain.relations ℝ 5).liftQ (rawEvaluation5 f)
    (relations5_le_rawEvaluation5_ker f hf)

def evaluation4 (f : U4 → E) (hf : IsAlternatingFunction4 f) :
    OrbitChain.Module ℝ 4 →ₗ[ℝ] E :=
  (OrbitChain.relations ℝ 4).liftQ (rawEvaluation4 f)
    (relations4_le_rawEvaluation4_ker f hf)

@[simp]
theorem evaluation5_ofConfig (f : U5 → E)
    (hf : IsAlternatingFunction5 f) (x : OrbitChain.GenericConfig 5) :
    evaluation5 f hf (OrbitChain.ofConfig x) = f (orbitCoord5 x) := by
  simp [evaluation5, OrbitChain.ofConfig]

@[simp]
theorem evaluation4_ofConfig (f : U4 → E)
    (hf : IsAlternatingFunction4 f) (x : OrbitChain.GenericConfig 4) :
    evaluation4 f hf (OrbitChain.ofConfig x) = f (orbitCoord4 x) := by
  simp [evaluation4, OrbitChain.ofConfig]

theorem relations5_le_rawDirac5_ker :
    OrbitChain.relations ℝ 5 ≤ LinearMap.ker rawDirac5 := by
  rw [OrbitChain.relations, Submodule.span_le]
  intro c hc
  rcases hc with hc | hc
  · rcases hc with ⟨g, x, rfl⟩
    change rawDirac5 (OrbitChain.groupRelation ℝ g x) = 0
    rw [OrbitChain.groupRelation, map_sub, rawDirac5_generator,
      rawDirac5_generator, diracConfig5_smulGeneric, sub_self]
  · rcases hc with ⟨σ, x, rfl⟩
    change rawDirac5 (OrbitChain.permutationRelation ℝ σ x) = 0
    rw [OrbitChain.permutationRelation, map_sub, map_smul,
      rawDirac5_generator, rawDirac5_generator,
      diracConfig5_permuteGeneric, sub_self]

theorem relations4_le_rawDirac4_ker :
    OrbitChain.relations ℝ 4 ≤ LinearMap.ker rawDirac4 := by
  rw [OrbitChain.relations, Submodule.span_le]
  intro c hc
  rcases hc with hc | hc
  · rcases hc with ⟨g, x, rfl⟩
    change rawDirac4 (OrbitChain.groupRelation ℝ g x) = 0
    rw [OrbitChain.groupRelation, map_sub, rawDirac4_generator,
      rawDirac4_generator, diracConfig4_smulGeneric, sub_self]
  · rcases hc with ⟨σ, x, rfl⟩
    change rawDirac4 (OrbitChain.permutationRelation ℝ σ x) = 0
    rw [OrbitChain.permutationRelation, map_sub, map_smul,
      rawDirac4_generator, rawDirac4_generator,
      diracConfig4_permuteGeneric, sub_self]

/-- The well-defined Dirac map from five-point orbit chains. -/
def diracMap5 : OrbitChain.Module ℝ 5 →ₗ[ℝ] SignedMeasure U5 :=
  (OrbitChain.relations ℝ 5).liftQ rawDirac5 relations5_le_rawDirac5_ker

/-- The well-defined Dirac map from four-point orbit chains. -/
def diracMap4 : OrbitChain.Module ℝ 4 →ₗ[ℝ] SignedMeasure U4 :=
  (OrbitChain.relations ℝ 4).liftQ rawDirac4 relations4_le_rawDirac4_ker

@[simp]
theorem diracMap5_ofConfig (x : OrbitChain.GenericConfig 5) :
    diracMap5 (OrbitChain.ofConfig x) = diracConfig5 x := by
  simp [diracMap5, OrbitChain.ofConfig]

@[simp]
theorem diracMap4_ofConfig (x : OrbitChain.GenericConfig 4) :
    diracMap4 (OrbitChain.ofConfig x) = diracConfig4 x := by
  simp [diracMap4, OrbitChain.ofConfig]

theorem integrable_diracMap5 (f : U5 → E)
    (z : OrbitChain.Module ℝ 5) :
    (diracMap5 z).Integrable f := by
  obtain ⟨c, rfl⟩ := (OrbitChain.relations ℝ 5).mkQ_surjective z
  change (rawDirac5 c).Integrable f
  exact integrable_rawDirac5 f c

theorem integrable_diracMap4 (f : U4 → E)
    (z : OrbitChain.Module ℝ 4) :
    (diracMap4 z).Integrable f := by
  obtain ⟨c, rfl⟩ := (OrbitChain.relations ℝ 4).mkQ_surjective z
  change (rawDirac4 c).Integrable f
  exact integrable_rawDirac4 f c

/-- Analytic integration against the Dirac realization agrees exactly with
the algebraic orbit-chain pairing. -/
theorem integral_diracMap5_eq_evaluation5 (f : U5 → E)
    (hf : IsAlternatingFunction5 f) (z : OrbitChain.Module ℝ 5) :
    (∫ᵛ q, f q ∂<•(diracMap5 z)) = evaluation5 f hf z := by
  obtain ⟨c, rfl⟩ := (OrbitChain.relations ℝ 5).mkQ_surjective z
  change (∫ᵛ q, f q ∂<•(rawDirac5 c)) = rawEvaluation5 f c
  rw [integral_rawDirac5 f hf]
  rw [rawEvaluation5, Finsupp.linearCombination_apply]
  rfl

theorem integral_diracMap4_eq_evaluation4 (f : U4 → E)
    (hf : IsAlternatingFunction4 f) (z : OrbitChain.Module ℝ 4) :
    (∫ᵛ q, f q ∂<•(diracMap4 z)) = evaluation4 f hf z := by
  obtain ⟨c, rfl⟩ := (OrbitChain.relations ℝ 4).mkQ_surjective z
  change (∫ᵛ q, f q ∂<•(rawDirac4 c)) = rawEvaluation4 f c
  rw [integral_rawDirac4 f hf]
  rw [rawEvaluation4, Finsupp.linearCombination_apply]
  rfl

theorem diracMap_boundary_ofConfig (x : OrbitChain.GenericConfig 5) :
    boundary4 (diracMap5 (OrbitChain.ofConfig x)) =
      diracMap4 (OrbitChain.boundary ℝ 4 (OrbitChain.ofConfig x)) := by
  rw [diracMap5_ofConfig, boundary4_diracConfig5,
    OrbitChain.boundary_ofConfig]
  simp only [map_sum, LinearMap.map_smul, diracMap4_ofConfig]

/-- The Dirac realization is a chain map from orbit chains to signed measure
chains. -/
theorem diracMap_boundary (z : OrbitChain.Module ℝ 5) :
    boundary4 (diracMap5 z) =
      diracMap4 (OrbitChain.boundary ℝ 4 z) := by
  obtain ⟨c, rfl⟩ := (OrbitChain.relations ℝ 5).mkQ_surjective z
  have hraw : boundary4.comp rawDirac5 =
      diracMap4.comp
        ((OrbitChain.relations ℝ 4).mkQ.comp
          (OrbitChain.rawBoundary ℝ 4)) := by
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    rw [show Finsupp.single x a =
        a • OrbitChain.generator (R := ℝ) x by
      ext y
      simp [OrbitChain.generator]]
    simp only [map_smul]
    congr 1
    rw [rawDirac5_generator, OrbitChain.rawBoundary_generator,
      boundary4_diracConfig5]
    simp only [OrbitChain.boundaryGenerator, map_sum, LinearMap.map_smul,
      Submodule.mkQ_apply]
    apply Finset.sum_congr rfl
    intro i _
    change ((-1 : ℝ) ^ i.val) • diracConfig4 (OrbitChain.face i x) =
      ((-1 : ℝ) ^ i.val) •
        diracMap4 (OrbitChain.ofConfig (OrbitChain.face i x))
    rw [diracMap4_ofConfig]
  change boundary4 (rawDirac5 c) =
    diracMap4 ((OrbitChain.relations ℝ 4).mkQ
      (OrbitChain.rawBoundary ℝ 4 c))
  exact LinearMap.congr_fun hraw c

/-- The quotient Dirac realization is nonexpanding for the quotient
coefficient seminorm and total variation. -/
theorem mass_diracMap5_le_quotientL1 (z : OrbitChain.Module ℝ 5) :
    mass (diracMap5 z) ≤ OrbitChain.quotientL1 z := by
  apply le_csInf (OrbitChain.presentationMasses_nonempty z)
  rintro r ⟨c, hc, rfl⟩
  rw [← hc]
  change mass (rawDirac5 c) ≤ OrbitChain.rawMass c
  exact mass_rawDirac5_le c

theorem mass_diracMap4_le_quotientL1 (z : OrbitChain.Module ℝ 4) :
    mass (diracMap4 z) ≤ OrbitChain.quotientL1 z := by
  apply le_csInf (OrbitChain.presentationMasses_nonempty z)
  rintro r ⟨c, hc, rfl⟩
  rw [← hc]
  change mass (rawDirac4 c) ≤ OrbitChain.rawMass c
  exact mass_rawDirac4_le c

/-! ### Stokes and separation -/

/-- Stokes' formula for a finite measurable primitive on a five-point signed
measure.  The hypotheses list exactly the five pullback integrability
conditions; no pointwise evaluation of an a.e. class is used. -/
theorem stokes_boundary4 (ν : SignedMeasure U5) (f : U4 → ℝ)
    (hf : StronglyMeasurable f)
    (hface : ∀ i : Fin 5,
      ν.Integrable (f ∘ face4At i)) :
    ν.Integrable (D f) ∧
      (boundary4 ν).Integrable f ∧
      (∫ᵛ q, D f q ∂<•ν) =
        ∫ᵛ z, f z ∂<•(boundary4 ν) := by
  have h0 : ν.Integrable (f ∘ face4_0) := hface 0
  have h1 : ν.Integrable (f ∘ face4_1) := hface 1
  have h2 : ν.Integrable (f ∘ face4_2) := hface 2
  have h3 : ν.Integrable (f ∘ face4_3) := hface 3
  have h4 : ν.Integrable (f ∘ face4_4) := hface 4
  have h01 := h0.sub h1
  have h012 := h01.add h2
  have h0123 := h012.sub h3
  have hsum := h0123.add h4
  have hD : ν.Integrable (D f) := by
    change ν.Integrable (fun q ↦
      f (face4_0 q) - f (face4_1 q) + f (face4_2 q) -
        f (face4_3 q) + f (face4_4 q))
    exact hsum
  have m0 : (ν.map face4_0).Integrable f :=
    VectorMeasure.Integrable.map hf.aestronglyMeasurable h0
  have m1 : (ν.map face4_1).Integrable f :=
    VectorMeasure.Integrable.map hf.aestronglyMeasurable h1
  have m2 : (ν.map face4_2).Integrable f :=
    VectorMeasure.Integrable.map hf.aestronglyMeasurable h2
  have m3 : (ν.map face4_3).Integrable f :=
    VectorMeasure.Integrable.map hf.aestronglyMeasurable h3
  have m4 : (ν.map face4_4).Integrable f :=
    VectorMeasure.Integrable.map hf.aestronglyMeasurable h4
  have m01 := m0.sub_vectorMeasure m1
  have m012 := m01.add_vectorMeasure m2
  have m0123 := m012.sub_vectorMeasure m3
  have msum := m0123.add_vectorMeasure m4
  have hboundary : (boundary4 ν).Integrable f := by
    rw [boundary4_expanded]
    exact msum
  refine ⟨hD, hboundary, ?_⟩
  change (∫ᵛ q,
      ((f ∘ face4_0) - (f ∘ face4_1) + (f ∘ face4_2) -
        (f ∘ face4_3) + (f ∘ face4_4)) q ∂<•ν) = _
  rw [VectorMeasure.integral_add h0123 h4,
    VectorMeasure.integral_sub h012 h3,
    VectorMeasure.integral_add h01 h2,
    VectorMeasure.integral_sub h0 h1]
  rw [boundary4_expanded]
  rw [VectorMeasure.integral_add_vectorMeasure m0123 m4,
    VectorMeasure.integral_sub_vectorMeasure m012 m3,
    VectorMeasure.integral_add_vectorMeasure m01 m2,
    VectorMeasure.integral_sub_vectorMeasure m0 m1]
  rw [VectorMeasure.integral_map continuous_face4_0.measurable
      hf.aestronglyMeasurable h0,
    VectorMeasure.integral_map continuous_face4_1.measurable
      hf.aestronglyMeasurable h1,
    VectorMeasure.integral_map continuous_face4_2.measurable
      hf.aestronglyMeasurable h2,
    VectorMeasure.integral_map continuous_face4_3.measurable
      hf.aestronglyMeasurable h3,
    VectorMeasure.integral_map continuous_face4_4.measurable
      hf.aestronglyMeasurable h4]
  rfl

theorem stokes_boundary4_of_cycle (ν : SignedMeasure U5) (f : U4 → ℝ)
    (hf : StronglyMeasurable f)
    (hface : ∀ i : Fin 5, ν.Integrable (f ∘ face4At i))
    (hcycle : boundary4 ν = 0) :
    (∫ᵛ q, D f q ∂<•ν) = 0 := by
  obtain ⟨_, _, hstokes⟩ := stokes_boundary4 ν f hf hface
  rw [hstokes, hcycle, VectorMeasure.integral_zero_vectorMeasure]

/-- An equality holding for the reference measure also holds under integration
against every absolutely continuous signed chain. -/
theorem integral_congr_ae_of_isAbsolutelyContinuous
    {μ : Measure X} {ν : SignedMeasure X}
    (hν : IsAbsolutelyContinuous ν μ) {f g : X → ℝ}
    (hfg : f =ᵐ[μ] g) :
    (∫ᵛ x, f x ∂<•ν) = ∫ᵛ x, g x ∂<•ν :=
  VectorMeasure.integral_congr_ae (hν.ae_le hfg)

/-- Pairing a uniformly bounded function with a signed chain is bounded by
the total-variation mass. -/
theorem abs_integral_le_mass (ν : SignedMeasure X) (f : X → ℝ) {C : ℝ}
    (hbound : ∀ᵐ x ∂ν.variation, |f x| ≤ C) :
    |∫ᵛ x, f x ∂•ν| ≤ C * mass ν := by
  simpa only [Real.norm_eq_abs, mass, ContinuousLinearMap.opNorm_lsmul,
    mul_one] using
    (VectorMeasure.norm_integral_le_of_norm_le_const
      (μ := ν) (B := ContinuousLinearMap.lsmul ℝ ℝ)
      (by simpa only [Real.norm_eq_abs] using hbound))

/-- For real signed measures the two scalar-multiplication conventions for
the vector-measure integral coincide. -/
theorem integral_flip_eq_integral (ν : SignedMeasure X) (f : X → ℝ) :
    (∫ᵛ x, f x ∂<•ν) = ∫ᵛ x, f x ∂•ν := by
  have hpair : (ContinuousLinearMap.lsmul ℝ ℝ).flip =
      ContinuousLinearMap.lsmul ℝ ℝ := by
    ext a b
    simp [mul_comm]
  rw [hpair]

theorem abs_integral_flip_le_mass (ν : SignedMeasure X) (f : X → ℝ)
    {C : ℝ} (hbound : ∀ᵐ x ∂ν.variation, |f x| ≤ C) :
    |∫ᵛ x, f x ∂<•ν| ≤ C * mass ν := by
  rw [integral_flip_eq_integral]
  exact abs_integral_le_mass ν f hbound

/-- A bounded Borel test family separates finite signed measures.  Indicator
functions are already enough, and they are bounded by one. -/
theorem signedMeasure_ext_of_integral_eq
    (ν η : SignedMeasure X)
    (h : ∀ g : X → ℝ, StronglyMeasurable g →
      (∀ x, |g x| ≤ 1) →
      (∫ᵛ x, g x ∂<•ν) = ∫ᵛ x, g x ∂<•η) :
    ν = η := by
  ext s hs
  let g : X → ℝ := s.indicator (fun _ ↦ 1)
  have hg : StronglyMeasurable g :=
    stronglyMeasurable_const.indicator hs
  have hbound : ∀ x, |g x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ s <;> simp [g, hx]
  have heq := h g hg hbound
  simpa [g, VectorMeasure.integral_indicator_const, hs] using heq

end
end MeasureChain

end Sp4
