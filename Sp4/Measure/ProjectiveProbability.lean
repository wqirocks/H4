import Sp4.Cohomology.ExternalInputs
import Sp4.Cohomology.ProjectiveCoordinates
import Sp4.Cohomology.Stabilizers
import Sp4.Cohomology.MeasurableRows
import Sp4.Symplectic.AnalyticGeneric
import Mathlib.LinearAlgebra.Vandermonde

/-!
# A probability representative on projective space and its conull orbit strata

The standard affine chart is equipped with independent complex Gaussian
coordinates and pushed forward to projective three-space.  Mityagin's
analytic-zero-set theorem then shows that transverse pairs, strong triples,
and generic configurations of at least four points are conull.  The explicit
transitivity and stabilizer calculations are supplied by `Stabilizers` and
`ProjectiveCoordinates`.
-/

namespace Sp4.ProjectiveProbability

open MeasureTheory
open scoped LinearAlgebra.Projectivization Matrix BigOperators

noncomputable section

abbrev AffineCoordinates := Fin 3 → ℂ

def affineVector (z : AffineCoordinates) : SymplecticVector :=
  ![1, z 0, z 1, z 2]

theorem affineVector_ne_zero (z : AffineCoordinates) : affineVector z ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simpa [affineVector] using h0

def affinePoint (z : AffineCoordinates) : ProjectivePoint :=
  Projectivization.mk ℂ (affineVector z) (affineVector_ne_zero z)

theorem measurable_affinePoint : Measurable affinePoint := by
  change Measurable (fun z => Quotient.mk''
    (⟨affineVector z, affineVector_ne_zero z⟩ :
      {v : SymplecticVector // v ≠ 0}))
  apply measurable_quotient_mk''.comp
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro i
  fin_cases i <;> simp [affineVector] <;> measurability

/-- Scale-invariant condition selecting the standard affine chart. -/
def InAffineChart : ProjectivePoint → Prop :=
  Projectivization.lift
    (fun v : {v : SymplecticVector // v ≠ 0} => v.1 0 ≠ 0)
    (by
      intro a b t hab
      have ht : t ≠ 0 := by
        intro ht
        apply a.2
        rw [hab, ht, zero_smul]
      apply propext
      change a.1 0 ≠ 0 ↔ b.1 0 ≠ 0
      rw [hab]
      simp [ht])

theorem inAffineChart_mk (v : SymplecticVector) (hv : v ≠ 0) :
    InAffineChart (Projectivization.mk ℂ v hv) ↔ v 0 ≠ 0 := by
  rfl

theorem measurableSet_inAffineChart :
    MeasurableSet {p : ProjectivePoint | InAffineChart p} := by
  rw [measurableSet_projective_iff]
  change MeasurableSet
    {v : {v : SymplecticVector // v ≠ 0} | v.1 0 ≠ 0}
  change MeasurableSet
    ((fun v : {v : SymplecticVector // v ≠ 0} => v.1 0) ⁻¹'
      ({0} : Set ℂ)ᶜ)
  exact (isClosed_singleton.isOpen_compl.measurableSet).preimage
    ((measurable_pi_apply 0).comp measurable_subtype_coe)

/-- Coordinates on the standard chart, extended by zero off the chart. -/
def affineCoord : ProjectivePoint → AffineCoordinates :=
  Projectivization.lift
    (fun v i => v.1 i.succ / v.1 0)
    (by
      intro a b t hab
      funext i
      by_cases ht : t = 0
      · exfalso
        apply a.2
        rw [hab, ht, zero_smul]
      · by_cases hb0 : b.1 0 = 0
        · simp [hab, hb0]
        · change a.1 i.succ / a.1 0 = b.1 i.succ / b.1 0
          rw [hab]
          field_simp [ht, hb0]
          change (t * b.1 i.succ) * b.1 0 =
            (t * b.1 0) * b.1 i.succ
          ring)

theorem measurable_affineCoord : Measurable affineCoord := by
  rw [measurable_from_projective]
  apply measurable_pi_lambda
  intro i
  exact ((measurable_pi_apply i.succ).comp measurable_subtype_coe).div
    ((measurable_pi_apply 0).comp measurable_subtype_coe)

@[simp] theorem affineCoord_affinePoint (z : AffineCoordinates) :
    affineCoord (affinePoint z) = z := by
  funext i
  fin_cases i <;> simp [affineCoord, affinePoint, affineVector]

theorem affinePoint_affineCoord_of_chart (p : ProjectivePoint)
    (hp : InAffineChart p) : affinePoint (affineCoord p) = p := by
  induction p using Projectivization.ind with
  | h v hv =>
      rw [inAffineChart_mk] at hp
      rw [affinePoint, Projectivization.mk_eq_mk_iff']
      refine ⟨(v 0)⁻¹, ?_⟩
      funext i
      fin_cases i <;>
        simp [affineCoord, affineVector, hp, div_eq_mul_inv] <;> ring

theorem range_affinePoint :
    Set.range affinePoint = {p : ProjectivePoint | InAffineChart p} := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    exact (inAffineChart_mk _ _).2 (by simp [affineVector])
  · intro hp
    exact ⟨affineCoord p, affinePoint_affineCoord_of_chart p hp⟩

theorem measurableEmbedding_affinePoint : MeasurableEmbedding affinePoint := by
  apply MeasurableEmbedding.of_measurable_inverse
    measurable_affinePoint
  · rw [range_affinePoint]
    exact measurableSet_inAffineChart
  · exact measurable_affineCoord
  · exact affineCoord_affinePoint

def affineTuple (n : ℕ) (z : Fin n → AffineCoordinates) :
    ProjectiveConfig n := fun i => affinePoint (z i)

theorem measurable_affineTuple (n : ℕ) : Measurable (affineTuple n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_affinePoint.comp (measurable_pi_apply i)

def affineTupleCoord (n : ℕ) (x : ProjectiveConfig n) :
    Fin n → AffineCoordinates := fun i => affineCoord (x i)

theorem measurable_affineTupleCoord (n : ℕ) :
    Measurable (affineTupleCoord n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_affineCoord.comp (measurable_pi_apply i)

@[simp] theorem affineTupleCoord_affineTuple (n : ℕ)
    (z : Fin n → AffineCoordinates) :
    affineTupleCoord n (affineTuple n z) = z := by
  funext i
  exact affineCoord_affinePoint (z i)

theorem range_affineTuple (n : ℕ) :
    Set.range (affineTuple n) =
      {x : ProjectiveConfig n | ∀ i, InAffineChart (x i)} := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩ i
    exact (inAffineChart_mk _ _).2 (by simp [affineTuple, affineVector])
  · intro hx
    refine ⟨affineTupleCoord n x, funext fun i => ?_⟩
    exact affinePoint_affineCoord_of_chart (x i) (hx i)

theorem measurableSet_range_affineTuple (n : ℕ) :
    MeasurableSet (Set.range (affineTuple n)) := by
  rw [range_affineTuple]
  rw [show {x : ProjectiveConfig n | ∀ i, InAffineChart (x i)} =
      ⋂ i, {x : ProjectiveConfig n | InAffineChart (x i)} by
    ext x
    simp]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_inAffineChart.preimage (measurable_pi_apply i)

theorem measurableEmbedding_affineTuple (n : ℕ) :
    MeasurableEmbedding (affineTuple n) := by
  apply MeasurableEmbedding.of_measurable_inverse
    (measurable_affineTuple n) (measurableSet_range_affineTuple n)
    (measurable_affineTupleCoord n)
  exact affineTupleCoord_affineTuple n

def measureProjective : Measure ProjectivePoint :=
  Measure.map affinePoint (standardComplexGaussianPi 3)

instance : IsProbabilityMeasure measureProjective :=
  Measure.isProbabilityMeasure_map measurable_affinePoint.aemeasurable

theorem tupleMeasure_measureProjective (n : ℕ) :
    MeasurableRows.tupleMeasure measureProjective n =
      Measure.map (affineTuple n)
        (Measure.pi fun _ : Fin n => standardComplexGaussianPi 3) := by
  rw [MeasurableRows.tupleMeasure, measureProjective]
  exact (Measure.pi_map_pi (fun _ : Fin n =>
    measurable_affinePoint.aemeasurable)).symm

/-! A single explicit affine configuration witnessing nontriviality of all
genericity equations. -/

def powerVector (t : ℂ) : SymplecticVector := ![1, t, t ^ 2, t ^ 3]

theorem powerVectors_linearIndependent (t : Fin 4 → ℂ)
    (ht : Function.Injective t) :
    LinearIndependent ℂ (fun i => powerVector (t i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hc0 : c = 0 :=
    Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero ht (by
      intro j
      have hcoord := congrFun hc j
      fin_cases j <;> simpa [powerVector] using hcoord)
  exact congrFun hc0 i

/-- A coordinate permutation and nonzero rescaling taking ordinary powers
to the symplectic rational normal curve. -/
def powersToMoment : SymplecticVector ≃ₗ[ℂ] SymplecticVector where
  toFun v := ![v 0, v 3, v 1, -3 * v 2]
  invFun v := ![v 0, v 2, -(v 3) / 3, v 1]
  left_inv v := by
    funext i
    fin_cases i <;> simp <;> ring
  right_inv v := by
    funext i
    fin_cases i <;> simp <;> ring
  map_add' v w := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> simp <;> ring

def momentVector (t : ℂ) : SymplecticVector :=
  ![1, t ^ 3, t, -3 * t ^ 2]

@[simp] theorem powersToMoment_powerVector (t : ℂ) :
    powersToMoment (powerVector t) = momentVector t := by
  funext i
  fin_cases i <;> simp [powersToMoment, powerVector, momentVector]

theorem momentVectors_linearIndependent (t : Fin 4 → ℂ)
    (ht : Function.Injective t) :
    LinearIndependent ℂ (fun i => momentVector (t i)) := by
  have h := (powerVectors_linearIndependent t ht).map'
    powersToMoment.toLinearMap powersToMoment.ker
  simpa [Function.comp_def] using h

def momentCoord (t : ℂ) : AffineCoordinates := ![t ^ 3, t, -3 * t ^ 2]

@[simp] theorem affineVector_momentCoord (t : ℂ) :
    affineVector (momentCoord t) = momentVector t := by
  funext i
  fin_cases i <;> rfl

theorem omega_momentVector (s t : ℂ) :
    omega (momentVector s) (momentVector t) = (t - s) ^ 3 := by
  simp [omega_apply, momentVector]
  ring

def momentTuple (n : ℕ) : Fin n → AffineCoordinates :=
  fun i => momentCoord (i.val : ℂ)

theorem momentTuple_generic {n : ℕ} (h4 : 4 ≤ n) :
    IsGeneric (affineTuple n (momentTuple n)) := by
  constructor
  · intro i j hij
    change Transverse (affinePoint (momentTuple n i))
      (affinePoint (momentTuple n j))
    unfold affinePoint
    simp only [momentTuple]
    rw [transverse_mk_iff,
      affineVector_momentCoord, affineVector_momentCoord,
      omega_momentVector]
    apply pow_ne_zero
    exact sub_ne_zero.mpr (by
      exact_mod_cast Fin.val_ne_of_ne (Ne.symm hij))
  · intro e he
    let t : Fin 4 → ℂ := fun k => ((e k).val : ℂ)
    have ht : Function.Injective t := by
      intro i j hij
      apply he
      apply Fin.ext
      change ((e i).val : ℂ) = ((e j).val : ℂ) at hij
      exact_mod_cast hij
    have hli : LinearIndependent ℂ
        (fun k => momentVector (t k)) :=
      momentVectors_linearIndependent t ht
    have hspan : Submodule.span ℂ
        (Set.range fun k => momentVector (t k)) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank (by simp [finrank_symplecticVector])
    rw [← hspan, Submodule.span_range_eq_iSup]
    congr 1

def affineConfigFamily (n : ℕ) (h4 : 4 ≤ n) :
    AnalyticConfigFamily (Fin n → AffineCoordinates) n where
  vec z i := affineVector (z i)
  analytic := by
    intro i z _hz
    have hid : AnalyticAt ℂ
        (fun x : Fin n → AffineCoordinates => x) z := analyticAt_id
    have hi : AnalyticAt ℂ (fun x : Fin n → AffineCoordinates => x i) z :=
      analyticAt_pi_iff.mp hid i
    have hcoord (k : Fin 3) :
        AnalyticAt ℂ (fun x : Fin n → AffineCoordinates => x i k) z :=
      analyticAt_pi_iff.mp hi k
    apply analyticAt_pi_iff.mpr
    intro k
    fin_cases k
    · simpa [affineVector] using (analyticAt_const :
        AnalyticAt ℂ (fun _ : Fin n → AffineCoordinates => (1 : ℂ)) z)
    · simpa [affineVector] using hcoord 0
    · simpa [affineVector] using hcoord 1
    · simpa [affineVector] using hcoord 2
  four_le := h4

theorem affineConfigFamily_good_moment {n : ℕ} (h4 : 4 ≤ n) :
    (affineConfigFamily n h4).Good (momentTuple n) := by
  exact (affineConfigFamily n h4).good_of_projectivized_generic
    (fun i => affineVector_ne_zero _)
    (by
      change IsGeneric (affineTuple n (momentTuple n))
      exact momentTuple_generic h4)

def sourceMeasure (n : ℕ) : Measure (Fin n → AffineCoordinates) :=
  Measure.pi fun _ : Fin n ↦ standardComplexGaussianPi 3

instance (n : ℕ) : IsProbabilityMeasure (sourceMeasure n) := by
  unfold sourceMeasure
  infer_instance

theorem affineConfigFamily_condition_zero {n : ℕ} (h4 : 4 ≤ n)
    (k : GenericConditionIndex n) :
    sourceMeasure n
      {z | (affineConfigFamily n h4).condition k z = 0} = 0 := by
  simpa [sourceMeasure] using
    (measure_zero_zeroSet_of_nontrivial_complex_analytic_piGaussian
      (fun _ : Fin n ↦ 3) ((affineConfigFamily n h4).condition k)
      ((affineConfigFamily n h4).condition_analytic k)
      ⟨momentTuple n, affineConfigFamily_good_moment h4 k⟩)

theorem ae_affineConfigFamily_good {n : ℕ} (h4 : 4 ≤ n) :
    ∀ᵐ z ∂sourceMeasure n, (affineConfigFamily n h4).Good z := by
  change ∀ᵐ z ∂sourceMeasure n,
    ∀ k, (affineConfigFamily n h4).condition k z ≠ 0
  rw [ae_all_iff]
  intro k
  rw [ae_iff]
  simpa only [not_ne_iff] using affineConfigFamily_condition_zero h4 k

theorem ae_affineTuple_generic {n : ℕ} (h4 : 4 ≤ n) :
    ∀ᵐ x ∂MeasurableRows.tupleMeasure measureProjective n,
      IsGeneric x := by
  rw [tupleMeasure_measureProjective]
  let F := affineConfigFamily n h4
  have hgoodOpen : IsOpen F.goodSet :=
    (F.goodSet_isOpen_dense ⟨momentTuple n,
      affineConfigFamily_good_moment h4⟩).1
  have himageMeasurable :
      MeasurableSet (affineTuple n '' F.goodSet) :=
    (measurableEmbedding_affineTuple n).measurableSet_image'
      hgoodOpen.measurableSet
  have himageAE :
      ∀ᵐ x ∂Measure.map (affineTuple n) (sourceMeasure n),
        x ∈ affineTuple n '' F.goodSet := by
    refine (ae_map_iff (measurable_affineTuple n).aemeasurable
      himageMeasurable).2 ?_
    filter_upwards [ae_affineConfigFamily_good h4] with z hz
    exact ⟨z, hz, rfl⟩
  filter_upwards [himageAE] with x hx
  rcases hx with ⟨z, hz, rfl⟩
  have hconfig : F.config z hz = affineTuple n z := by
    funext i
    rfl
  rw [← hconfig]
  exact F.config_generic hz

/-! ## The conull transverse-pair stratum -/

theorem affineVector_eval_analytic {n : ℕ} (i : Fin n) :
    AnalyticOnNhd ℂ
      (fun z : Fin n → AffineCoordinates => affineVector (z i)) Set.univ := by
  intro z _hz
  have hid : AnalyticAt ℂ
      (fun x : Fin n → AffineCoordinates => x) z := analyticAt_id
  have hi : AnalyticAt ℂ (fun x : Fin n → AffineCoordinates => x i) z :=
    analyticAt_pi_iff.mp hid i
  have hcoord (k : Fin 3) :
      AnalyticAt ℂ (fun x : Fin n → AffineCoordinates => x i k) z :=
    analyticAt_pi_iff.mp hi k
  apply analyticAt_pi_iff.mpr
  intro k
  fin_cases k
  · simpa [affineVector] using (analyticAt_const :
      AnalyticAt ℂ (fun _ : Fin n → AffineCoordinates => (1 : ℂ)) z)
  · simpa [affineVector] using hcoord 0
  · simpa [affineVector] using hcoord 1
  · simpa [affineVector] using hcoord 2

def affinePairing {n : ℕ} (i j : Fin n)
    (z : Fin n → AffineCoordinates) : ℂ :=
  omega (affineVector (z i)) (affineVector (z j))

theorem affinePairing_analytic {n : ℕ} (i j : Fin n) :
    AnalyticOnNhd ℂ (affinePairing i j) Set.univ := by
  intro z _hz
  have hcoord (v : Fin n) (k : Fin 4) :
      AnalyticAt ℂ (fun x : Fin n → AffineCoordinates =>
        affineVector (x v) k) z :=
    analyticAt_pi_iff.mp (affineVector_eval_analytic v z (Set.mem_univ z)) k
  rw [show affinePairing i j = fun x =>
      affineVector (x i) 0 * affineVector (x j) 1 -
        affineVector (x i) 1 * affineVector (x j) 0 +
        affineVector (x i) 2 * affineVector (x j) 3 -
        affineVector (x i) 3 * affineVector (x j) 2 by
    funext x
    exact omega_apply _ _]
  exact ((((hcoord i 0).mul (hcoord j 1)).sub
    ((hcoord i 1).mul (hcoord j 0))).add
      ((hcoord i 2).mul (hcoord j 3))).sub
        ((hcoord i 3).mul (hcoord j 2))

def pairCondition (z : Fin 2 → AffineCoordinates) : ℂ :=
  affinePairing 0 1 z

theorem pairCondition_analytic :
    AnalyticOnNhd ℂ pairCondition Set.univ := by
  unfold pairCondition
  exact affinePairing_analytic (0 : Fin 2) 1

theorem pairCondition_moment_ne_zero : pairCondition (momentTuple 2) ≠ 0 := by
  unfold pairCondition affinePairing momentTuple
  rw [affineVector_momentCoord, affineVector_momentCoord,
    omega_momentVector]
  norm_num

theorem pairCondition_zero_measure :
    sourceMeasure 2 {z | pairCondition z = 0} = 0 := by
  simpa [sourceMeasure] using
    (measure_zero_zeroSet_of_nontrivial_complex_analytic_piGaussian
      (fun _ : Fin 2 ↦ 3) pairCondition pairCondition_analytic
      ⟨momentTuple 2, pairCondition_moment_ne_zero⟩)

theorem pairGoodSet_isOpen :
    IsOpen {z : Fin 2 → AffineCoordinates | pairCondition z ≠ 0} := by
  change IsOpen (pairCondition ⁻¹' ({0} : Set ℂ)ᶜ)
  exact isOpen_compl_singleton.preimage pairCondition_analytic.continuous

theorem ae_pairCondition_ne_zero :
    ∀ᵐ z ∂sourceMeasure 2, pairCondition z ≠ 0 := by
  rw [ae_iff]
  simpa only [not_ne_iff] using pairCondition_zero_measure

theorem ae_affinePair_transverse :
    ∀ᵐ x ∂MeasurableRows.tupleMeasure measureProjective 2,
      Transverse (x 0) (x 1) := by
  rw [tupleMeasure_measureProjective]
  let S := {z : Fin 2 → AffineCoordinates | pairCondition z ≠ 0}
  have himageMeasurable : MeasurableSet (affineTuple 2 '' S) :=
    (measurableEmbedding_affineTuple 2).measurableSet_image'
      pairGoodSet_isOpen.measurableSet
  have himageAE :
      ∀ᵐ x ∂Measure.map (affineTuple 2) (sourceMeasure 2),
        x ∈ affineTuple 2 '' S := by
    refine (ae_map_iff (measurable_affineTuple 2).aemeasurable
      himageMeasurable).2 ?_
    filter_upwards [ae_pairCondition_ne_zero] with z hz
    exact ⟨z, hz, rfl⟩
  filter_upwards [himageAE] with x hx
  rcases hx with ⟨z, hz, rfl⟩
  change Transverse (affinePoint (z 0)) (affinePoint (z 1))
  unfold affinePoint
  rw [transverse_mk_iff]
  exact hz

/-! ## The conull strong-triple stratum -/

def firstThreeLinear : SymplecticVector →ₗ[ℂ] AffineCoordinates where
  toFun v i := v i.castSucc
  map_add' v w := by
    funext i
    simp
  map_smul' c v := by
    funext i
    simp

def tripleMinor (z : Fin 3 → AffineCoordinates) : ℂ :=
  Matrix.det fun i j : Fin 3 => firstThreeLinear (affineVector (z j)) i

theorem tripleMinor_analytic :
    AnalyticOnNhd ℂ tripleMinor Set.univ := by
  intro z _hz
  rw [show tripleMinor = fun x =>
      ∑ σ : Equiv.Perm (Fin 3), Equiv.Perm.sign σ •
        ∏ i : Fin 3,
          firstThreeLinear (affineVector (x i)) (σ i) by
    funext x
    exact Matrix.det_apply _]
  simpa [firstThreeLinear] using
    (Finset.univ.analyticAt_fun_sum (c := z) (f := fun σ x =>
      Equiv.Perm.sign σ •
        ∏ i : Fin 3,
          firstThreeLinear (affineVector (x i)) (σ i)) (by
      intro σ _hσ
      apply AnalyticAt.const_smul
      simpa using
        (Finset.univ.analyticAt_fun_prod (c := z) (f := fun i x =>
          firstThreeLinear (affineVector (x i)) (σ i)) (by
          intro i _hi
          exact analyticAt_pi_iff.mp
            (affineVector_eval_analytic i z (Set.mem_univ z))
            (σ i).castSucc))))

abbrev TripleConditionIndex := OffDiagonalIndex 3 ⊕ Unit

def tripleCondition : TripleConditionIndex →
    (Fin 3 → AffineCoordinates) → ℂ
  | Sum.inl ij => affinePairing ij.1.1 ij.1.2
  | Sum.inr _ => tripleMinor

def tripleGoodSet : Set (Fin 3 → AffineCoordinates) :=
  {z | ∀ k : TripleConditionIndex, tripleCondition k z ≠ 0}

theorem tripleCondition_analytic (k : TripleConditionIndex) :
    AnalyticOnNhd ℂ (tripleCondition k) Set.univ := by
  rcases k with ij | u
  · exact affinePairing_analytic ij.1.1 ij.1.2
  · exact tripleMinor_analytic

theorem tripleMinor_moment_ne_zero : tripleMinor (momentTuple 3) ≠ 0 := by
  let A : Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
    firstThreeLinear (affineVector (momentTuple 3 j)) i
  have hcast : Fin.castSucc (2 : Fin 3) = (2 : Fin 4) := rfl
  change Matrix.det A ≠ 0
  rw [Matrix.det_fin_three]
  norm_num [A, firstThreeLinear, momentTuple, momentCoord, affineVector,
    hcast, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem tripleCondition_moment_ne_zero (k : TripleConditionIndex) :
    tripleCondition k (momentTuple 3) ≠ 0 := by
  rcases k with ij | u
  · change affinePairing ij.1.1 ij.1.2 (momentTuple 3) ≠ 0
    unfold affinePairing momentTuple
    rw [affineVector_momentCoord, affineVector_momentCoord,
      omega_momentVector]
    apply pow_ne_zero
    apply sub_ne_zero.mpr
    exact_mod_cast Fin.val_ne_of_ne (Ne.symm ij.2)
  · exact tripleMinor_moment_ne_zero

theorem tripleCondition_zero_measure (k : TripleConditionIndex) :
    sourceMeasure 3 {z | tripleCondition k z = 0} = 0 := by
  simpa [sourceMeasure] using
    (measure_zero_zeroSet_of_nontrivial_complex_analytic_piGaussian
      (fun _ : Fin 3 ↦ 3) (tripleCondition k)
      (tripleCondition_analytic k)
      ⟨momentTuple 3, tripleCondition_moment_ne_zero k⟩)

theorem tripleGoodSet_isOpen : IsOpen tripleGoodSet := by
  have hpiece (k : TripleConditionIndex) :
      IsOpen {z : Fin 3 → AffineCoordinates | tripleCondition k z ≠ 0} := by
    change IsOpen ((tripleCondition k) ⁻¹' ({0} : Set ℂ)ᶜ)
    exact isOpen_compl_singleton.preimage
      (tripleCondition_analytic k).continuous
  rw [show tripleGoodSet = ⋂ k : TripleConditionIndex,
      {z | tripleCondition k z ≠ 0} by
    ext z
    simp [tripleGoodSet]]
  exact isOpen_iInter_of_finite hpiece

theorem ae_tripleGood : ∀ᵐ z ∂sourceMeasure 3, z ∈ tripleGoodSet := by
  change ∀ᵐ z ∂sourceMeasure 3,
    ∀ k : TripleConditionIndex, tripleCondition k z ≠ 0
  rw [ae_all_iff]
  intro k
  rw [ae_iff]
  simpa only [not_ne_iff] using tripleCondition_zero_measure k

theorem affineTuple_strong_of_tripleGood
    {z : Fin 3 → AffineCoordinates} (hz : z ∈ tripleGoodSet) :
    TwoFree.IsStrongTriple (affineTuple 3 z) := by
  have hz' : ∀ k : TripleConditionIndex, tripleCondition k z ≠ 0 := hz
  have hdet :
      (Matrix.det fun i j : Fin 3 =>
        firstThreeLinear (affineVector (z j)) i) ≠ 0 :=
    hz' (Sum.inr ())
  have hcols : LinearIndependent ℂ
      (fun j : Fin 3 => firstThreeLinear (affineVector (z j))) := by
    change LinearIndependent ℂ (fun j : Fin 3 => fun i : Fin 3 =>
      firstThreeLinear (affineVector (z j)) i)
    exact Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hli : LinearIndependent ℂ
      (fun j : Fin 3 => affineVector (z j)) := by
    apply LinearIndependent.of_comp firstThreeLinear
    simpa [Function.comp_def] using hcols
  constructor
  · constructor
    · intro i j hij
      change Transverse (affinePoint (z i)) (affinePoint (z j))
      unfold affinePoint
      rw [transverse_mk_iff]
      exact hz' (Sum.inl ⟨(i, j), hij⟩)
    · intro e he
      have hcard := Fintype.card_le_of_injective e he
      norm_num at hcard
  · intro e he
    let u : ProjectiveLift (affineTuple 3 z) := {
      vec := fun i => affineVector (z i)
      ne_zero := fun i => affineVector_ne_zero (z i)
      projectivizes := fun i => rfl }
    have hlie : LinearIndependent ℂ (fun k => u.vec (e k)) := by
      exact hli.comp e he
    have heq : projectiveTripleSpan (affineTuple 3 z) e =
        Submodule.span ℂ (Set.range fun k => u.vec (e k)) := by
      rw [projectiveTripleSpan, Submodule.span_range_eq_iSup]
      congr 1
    rw [heq, finrank_span_eq_card hlie, Fintype.card_fin]

theorem ae_affineTriple_strong :
    ∀ᵐ x ∂MeasurableRows.tupleMeasure measureProjective 3,
      TwoFree.IsStrongTriple x := by
  rw [tupleMeasure_measureProjective]
  have himageMeasurable :
      MeasurableSet (affineTuple 3 '' tripleGoodSet) :=
    (measurableEmbedding_affineTuple 3).measurableSet_image'
      tripleGoodSet_isOpen.measurableSet
  have himageAE :
      ∀ᵐ x ∂Measure.map (affineTuple 3) (sourceMeasure 3),
        x ∈ affineTuple 3 '' tripleGoodSet := by
    refine (ae_map_iff (measurable_affineTuple 3).aemeasurable
      himageMeasurable).2 ?_
    filter_upwards [ae_tripleGood] with z hz
    exact ⟨z, hz, rfl⟩
  filter_upwards [himageAE] with x hx
  rcases hx with ⟨z, hz, rfl⟩
  exact affineTuple_strong_of_tripleGood hz

/-! ## Conull orbit conclusions -/

theorem projectivePoint_in_standardOrbit (x : ProjectivePoint) :
    ∃ g : SymplecticGroup, g • x = ProjectiveStabilizers.standardPair 0 :=
  ProjectiveStabilizers.projective_transitive x

theorem ae_pair_in_standardOrbit :
    ∀ᵐ x ∂MeasurableRows.tupleMeasure measureProjective 2,
      ∃ g : SymplecticGroup, g • x = ProjectiveStabilizers.standardPair := by
  filter_upwards [ae_affinePair_transverse] with x hx
  exact ProjectiveStabilizers.transversePair_transitive ⟨x, hx⟩

theorem ae_triple_in_standardOrbit :
    ∀ᵐ x ∂MeasurableRows.tupleMeasure measureProjective 3,
      ∃ g : SymplecticGroup, g • x = TwoFree.standardTriple := by
  filter_upwards [ae_affineTriple_strong] with x hx
  exact TwoFree.exists_smul_eq_standardTriple ⟨x, hx⟩

theorem ae_generic_stabilizer_is_center (n : ℕ) :
    ∀ᵐ x ∂MeasurableRows.tupleMeasure measureProjective (4 + n),
      ∀ g : SymplecticGroup, g • x = x →
        g = 1 ∨ g = centralNeg := by
  filter_upwards [ae_affineTuple_generic (n := 4 + n) (by omega)] with x hx
  intro g hg
  apply ProjectiveAction.generic_stabilizer g ⟨x, hx⟩
  apply Subtype.ext
  exact hg

end
end Sp4.ProjectiveProbability
