import Sp4.Cohomology.CochainAlternation
import Sp4.Measure.Permutation
import Sp4.Pfaffian.MeasurableRigidity

/-!
# Full vertex alternation on normalized Pfaffian cochains

The six rational symmetries of the four-point Pfaffian chart are the quotient
of the full vertex group `S₄` by its Klein four kernel.  We make that quotient
calculation explicit, define the full four- and five-vertex alternating
averages on `L⁰`, and prove directly that the five-term differential commutes
with them.  Thus this chain-map fact is internal finite combinatorics and is
not part of the Burger--Monod input.
-/

namespace Sp4
namespace Pfaffian

noncomputable section

open MeasureTheory OrbitChain
open scoped BigOperators

/-! ## The explicit quotient `S₄ → S₄/V₄` -/

/-- The four representatives of the Klein kernel of the action on normalized
four-point coordinates. -/
inductive KleinRep
  | identity
  | swap01_23
  | swap02_13
  | swap03_12
deriving DecidableEq

def kleinRepEquivFin : KleinRep ≃ Fin 4 where
  toFun
    | .identity => 0
    | .swap01_23 => 1
    | .swap02_13 => 2
    | .swap03_12 => 3
  invFun i := Fin.cases .identity
    (Fin.cases .swap01_23 (Fin.cases .swap02_13 (fun _ ↦ .swap03_12))) i
  left_inv k := by cases k <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype KleinRep :=
  Fintype.ofEquiv (Fin 4) kleinRepEquivFin.symm

/-- The corresponding even vertex permutations. -/
def kleinRepPerm : KleinRep → Equiv.Perm (Fin 4)
  | .identity => 1
  | .swap01_23 => permKlein01_23
  | .swap02_13 => permKlein02_13
  | .swap03_12 => permKlein03_12

/-- Chosen vertex-permutation representatives of the six coordinate
symmetries. -/
def coordSymmVertexPerm : CoordSymm → Equiv.Perm (Fin 4)
  | .identity => 1
  | .cyclic => permCyclic
  | .cyclicSq => permCyclicSq
  | .oddX => permOddX
  | .rho => permRho
  | .oddY => permOddY

/-- Multiply a Klein-kernel element by a chosen quotient representative. -/
def kleinCoordPerm (p : KleinRep × CoordSymm) : Equiv.Perm (Fin 4) :=
  kleinRepPerm p.1 * coordSymmVertexPerm p.2

private theorem kleinCoordPerm_bijective :
    Function.Bijective kleinCoordPerm := by
  decide

/-- Exact enumeration of all twenty-four vertex permutations. -/
def kleinCoordEquiv :
    KleinRep × CoordSymm ≃ Equiv.Perm (Fin 4) :=
  Equiv.ofBijective kleinCoordPerm kleinCoordPerm_bijective

/-- The quotient-coordinate symmetry represented by a vertex permutation. -/
def vertexCoordSymm (σ : Equiv.Perm (Fin 4)) : CoordSymm :=
  (kleinCoordEquiv.symm σ).2

@[simp]
theorem permute4_kleinRepPerm (k : KleinRep) (q : U4) :
    permute4 (kleinRepPerm k) q = q := by
  cases k
  · exact permute4_one q
  · apply Subtype.ext
    exact chi4_reindex4_permKlein01_23 q
  · apply Subtype.ext
    exact chi4_reindex4_permKlein02_13 q
  · apply Subtype.ext
    exact chi4_reindex4_permKlein03_12 q

@[simp]
theorem permSign_kleinRepPerm (k : KleinRep) :
    permSign ℝ (kleinRepPerm k) = 1 := by
  cases k <;>
    simp [kleinRepPerm, permSign, sign_permKlein01_23,
      sign_permKlein02_13, sign_permKlein03_12]

@[simp]
theorem permute4_coordSymmVertexPerm (s : CoordSymm) (q : U4) :
    permute4 (coordSymmVertexPerm s) q = coordSymmAct s q := by
  cases s
  · exact permute4_one q
  · apply Subtype.ext
    exact chi4_reindex4_permCyclic q
  · apply Subtype.ext
    exact chi4_reindex4_permCyclicSq q
  · apply Subtype.ext
    exact chi4_reindex4_permOddX q
  · apply Subtype.ext
    exact chi4_reindex4_permRho q
  · apply Subtype.ext
    exact chi4_reindex4_permOddY q

@[simp]
theorem permSign_coordSymmVertexPerm (s : CoordSymm) :
    permSign ℝ (coordSymmVertexPerm s) = coordSymmSign s := by
  cases s <;>
    simp [coordSymmVertexPerm, coordSymmSign, coordSymmPerm, permSign,
      sign_permCyclic, sign_permCyclicSq, sign_permOddX, sign_permRho,
      sign_permOddY, Equiv.Perm.sign_mul]

/-- Every vertex permutation acts through its six-element coordinate
quotient. -/
theorem permute4_eq_coordSymmAct (σ : Equiv.Perm (Fin 4)) (q : U4) :
    permute4 σ q = coordSymmAct (vertexCoordSymm σ) q := by
  let p := kleinCoordEquiv.symm σ
  have hp : kleinCoordPerm p = σ := kleinCoordEquiv.apply_symm_apply σ
  rw [← hp]
  change permute4 (kleinRepPerm p.1 * coordSymmVertexPerm p.2) q = _
  rw [← permute4_mul, permute4_kleinRepPerm,
    permute4_coordSymmVertexPerm]
  have hback := kleinCoordEquiv.symm_apply_apply p
  change kleinCoordEquiv.symm (kleinCoordPerm p) = p at hback
  unfold vertexCoordSymm
  rw [hback]

/-- The quotient sign agrees with the ordinary sign of the vertex
permutation. -/
theorem permSign_eq_coordSymmSign (σ : Equiv.Perm (Fin 4)) :
    permSign ℝ σ = coordSymmSign (vertexCoordSymm σ) := by
  let p := kleinCoordEquiv.symm σ
  have hp : kleinCoordPerm p = σ := kleinCoordEquiv.apply_symm_apply σ
  rw [← hp]
  change permSign ℝ (kleinRepPerm p.1 * coordSymmVertexPerm p.2) = _
  rw [permSign_mul, permSign_kleinRepPerm, one_mul,
    permSign_coordSymmVertexPerm]
  have hback := kleinCoordEquiv.symm_apply_apply p
  change kleinCoordEquiv.symm (kleinCoordPerm p) = p at hback
  unfold vertexCoordSymm
  rw [hback]

/-- Every four-vertex permutation preserves the concrete smooth measure
class, because its coordinate action is one of the six already certified
rational diffeomorphisms. -/
theorem permute4_quasiMeasurePreserving (σ : Equiv.Perm (Fin 4)) :
    Measure.QuasiMeasurePreserving (permute4 σ) measureU4 measureU4 := by
  rw [show permute4 σ = coordSymmAct (vertexCoordSymm σ) by
    funext q
    exact permute4_eq_coordSymmAct σ q]
  exact coordSymmAct_quasiMeasurePreserving (vertexCoordSymm σ)

/-! ## Pointwise full alternation -/

/-- The normalized signed average over all four vertex permutations. -/
def fullAlternation4 (f : U4 → ℝ) (q : U4) : ℝ :=
  (Nat.factorial 4 : ℝ)⁻¹ *
    ∑ σ : Equiv.Perm (Fin 4), permSign ℝ σ * f (permute4 σ q)

/-- The normalized signed average over all five vertex permutations. -/
def fullAlternation5 (F : U5 → ℝ) (q : U5) : ℝ :=
  (Nat.factorial 5 : ℝ)⁻¹ *
    ∑ σ : Equiv.Perm (Fin 5), permSign ℝ σ * F (permute5 σ q)

/-- The four-vertex average transforms by the sign character. -/
theorem fullAlternation4_permute (f : U4 → ℝ)
    (τ : Equiv.Perm (Fin 4)) (q : U4) :
    fullAlternation4 f (permute4 τ q) =
      permSign ℝ τ * fullAlternation4 f q := by
  classical
  have hreindex := Fintype.sum_equiv (Equiv.mulLeft τ)
    (fun σ : Equiv.Perm (Fin 4) ↦
      permSign ℝ τ * permSign ℝ (τ * σ) * f (permute4 (τ * σ) q))
    (fun ρ : Equiv.Perm (Fin 4) ↦
      permSign ℝ τ * permSign ℝ ρ * f (permute4 ρ q))
    (fun _ ↦ rfl)
  have hsum :
      (∑ σ : Equiv.Perm (Fin 4),
        permSign ℝ σ * f (permute4 (τ * σ) q)) =
      permSign ℝ τ *
        ∑ ρ : Equiv.Perm (Fin 4),
          permSign ℝ ρ * f (permute4 ρ q) := by
    have hcancel (x : ℝ) :
        permSign ℝ τ * (permSign ℝ τ * x) = x := by
      rw [← mul_assoc, permSign_sq, one_mul]
    rw [Finset.mul_sum]
    simpa only [permSign_mul, mul_assoc, hcancel] using hreindex
  simp only [fullAlternation4, permute4_mul]
  rw [hsum]
  ring

/-- The five-vertex average transforms by the sign character. -/
theorem fullAlternation5_permute (F : U5 → ℝ)
    (τ : Equiv.Perm (Fin 5)) (q : U5) :
    fullAlternation5 F (permute5 τ q) =
      permSign ℝ τ * fullAlternation5 F q := by
  classical
  have hreindex := Fintype.sum_equiv (Equiv.mulLeft τ)
    (fun σ : Equiv.Perm (Fin 5) ↦
      permSign ℝ τ * permSign ℝ (τ * σ) * F (permute5 (τ * σ) q))
    (fun ρ : Equiv.Perm (Fin 5) ↦
      permSign ℝ τ * permSign ℝ ρ * F (permute5 ρ q))
    (fun _ ↦ rfl)
  have hsum :
      (∑ σ : Equiv.Perm (Fin 5),
        permSign ℝ σ * F (permute5 (τ * σ) q)) =
      permSign ℝ τ *
        ∑ ρ : Equiv.Perm (Fin 5),
          permSign ℝ ρ * F (permute5 ρ q) := by
    have hcancel (x : ℝ) :
        permSign ℝ τ * (permSign ℝ τ * x) = x := by
      rw [← mul_assoc, permSign_sq, one_mul]
    rw [Finset.mul_sum]
    simpa only [permSign_mul, mul_assoc, hcancel] using hreindex
  simp only [fullAlternation5, permute5_mul]
  rw [hsum]
  ring

/-- Full vertex alternation implies the five quotient-coordinate identities
used by the bounded-defect argument. -/
theorem pointAlt_fullAlternation4 (f : U4 → ℝ) :
    PointAlt (fullAlternation4 f) := by
  constructor
  · intro q
    simpa [coordSymmAct, coordSymmSign, coordSymmPerm] using
      fullAlternation4_permute f (coordSymmVertexPerm .cyclic) q
  · intro q
    simpa [coordSymmAct, coordSymmSign, coordSymmPerm] using
      fullAlternation4_permute f (coordSymmVertexPerm .cyclicSq) q
  · intro q
    simpa [coordSymmAct, coordSymmSign, coordSymmPerm] using
      fullAlternation4_permute f (coordSymmVertexPerm .oddX) q
  · intro q
    simpa [coordSymmAct, coordSymmSign, coordSymmPerm] using
      fullAlternation4_permute f (coordSymmVertexPerm .rho) q
  · intro q
    simpa [coordSymmAct, coordSymmSign, coordSymmPerm] using
      fullAlternation4_permute f (coordSymmVertexPerm .oddY) q

/-! ## Compatibility with the five-term differential -/

/-- At a fixed deleted source vertex, the five-vertex sum is reindexed by
the image vertex and the induced four-vertex permutation. -/
theorem sum_permutations_face4At (f : U4 → ℝ) (q : U5) (j : Fin 5) :
    (∑ σ : Equiv.Perm (Fin 5),
        permSign ℝ σ * ((-1 : ℝ) ^ j.val *
          f (face4At j (permute5 σ q)))) =
      ∑ p : Fin 5 × Equiv.Perm (Fin 4),
        (-1 : ℝ) ^ p.1.val * permSign ℝ p.2 *
          f (permute4 p.2 (face4At p.1 q)) := by
  classical
  refine Fintype.sum_equiv
    (CochainAlternation.decomposePermAt j) _ _ ?_
  intro σ
  rw [face4At_permute5]
  simp only [CochainAlternation.decomposePermAt_fst,
    CochainAlternation.decomposePermAt_snd]
  rw [CochainAlternation.deletePerm_incidence_sign_cast_cochain]
  ring

/-- The unnormalized five-vertex average of `D f` is five times `D` of the
unnormalized four-vertex average. -/
theorem fullAlternatingSum_D (f : U4 → ℝ) (q : U5) :
    (∑ σ : Equiv.Perm (Fin 5),
        permSign ℝ σ * D f (permute5 σ q)) =
      (5 : ℝ) * D
        (fun r ↦ ∑ τ : Equiv.Perm (Fin 4),
          permSign ℝ τ * f (permute4 τ r)) q := by
  classical
  calc
    (∑ σ : Equiv.Perm (Fin 5),
        permSign ℝ σ * D f (permute5 σ q)) =
        ∑ σ : Equiv.Perm (Fin 5),
          permSign ℝ σ *
            ∑ j : Fin 5, (-1 : ℝ) ^ j.val *
              f (face4At j (permute5 σ q)) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [D_eq_face_sum]
      simp only [faceSign]
    _ = ∑ σ : Equiv.Perm (Fin 5),
          ∑ j : Fin 5, permSign ℝ σ *
            ((-1 : ℝ) ^ j.val *
              f (face4At j (permute5 σ q))) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.mul_sum]
    _ = ∑ j : Fin 5, ∑ σ : Equiv.Perm (Fin 5),
          permSign ℝ σ * ((-1 : ℝ) ^ j.val *
            f (face4At j (permute5 σ q))) := by
      rw [Finset.sum_comm]
    _ = ∑ _j : Fin 5,
          ∑ p : Fin 5 × Equiv.Perm (Fin 4),
            (-1 : ℝ) ^ p.1.val * permSign ℝ p.2 *
              f (permute4 p.2 (face4At p.1 q)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact sum_permutations_face4At f q j
    _ = ∑ _j : Fin 5,
          D (fun r ↦ ∑ τ : Equiv.Perm (Fin 4),
            permSign ℝ τ * f (permute4 τ r)) q := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.sum_prod_type, D_eq_face_sum]
      simp only [faceSign]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      simp [mul_assoc]
    _ = (5 : ℝ) * D
        (fun r ↦ ∑ τ : Equiv.Perm (Fin 4),
          permSign ℝ τ * f (permute4 τ r)) q := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      norm_num
      ring

/-- The pointwise Pfaffian differential is real-linear in a constant
multiple. -/
theorem D_const_mul (c : ℝ) (f : U4 → ℝ) (q : U5) :
    D (fun r ↦ c * f r) q = c * D f q := by
  rw [D_eq_face_sum, D_eq_face_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Full normalized alternation commutes with the concrete five-term
Pfaffian differential. -/
theorem D_fullAlternation4 (f : U4 → ℝ) (q : U5) :
    D (fullAlternation4 f) q = fullAlternation5 (D f) q := by
  change
    D (fun r ↦ (Nat.factorial 4 : ℝ)⁻¹ *
      ∑ τ : Equiv.Perm (Fin 4),
        permSign ℝ τ * f (permute4 τ r)) q =
    (Nat.factorial 5 : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin 5),
        permSign ℝ σ * D f (permute5 σ q)
  rw [D_const_mul, fullAlternatingSum_D]
  norm_num [Nat.factorial]
  ring

/-! ## Full alternation on almost-everywhere classes -/

/-- Coefficients of the normalized four-vertex alternating average. -/
def fullAlternation4Coeff (σ : Equiv.Perm (Fin 4)) : ℝ :=
  (Nat.factorial 4 : ℝ)⁻¹ * permSign ℝ σ

/-- Coefficients of the normalized five-vertex alternating average. -/
def fullAlternation5Coeff (σ : Equiv.Perm (Fin 5)) : ℝ :=
  (Nat.factorial 5 : ℝ)⁻¹ * permSign ℝ σ

/-- Full four-vertex alternation on `L⁰(U₄)`. -/
noncomputable def FullAlt4 :
    L0 U4 measureU4 →ₗ[ℝ] L0 U4 measureU4 :=
  L0.weightedPullbackₗ permute4 permute4_quasiMeasurePreserving
    fullAlternation4Coeff

/-- Full five-vertex alternation on `L⁰(U₅)`. -/
noncomputable def FullAlt5 :
    L0 U5 measureU5 →ₗ[ℝ] L0 U5 measureU5 :=
  L0.weightedPullbackₗ permute5 permute5_quasiMeasurePreserving
    fullAlternation5Coeff

theorem coeFn_FullAlt4 (f : L0 U4 measureU4) :
    (FullAlt4 f : U4 → ℝ) =ᵐ[measureU4] fullAlternation4 f := by
  refine (L0.coeFn_weightedPullbackₗ permute4
    permute4_quasiMeasurePreserving fullAlternation4Coeff f).trans
      (Filter.Eventually.of_forall fun q ↦ ?_)
  simp only [fullAlternation4Coeff, fullAlternation4]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem coeFn_FullAlt5 (F : L0 U5 measureU5) :
    (FullAlt5 F : U5 → ℝ) =ᵐ[measureU5] fullAlternation5 F := by
  refine (L0.coeFn_weightedPullbackₗ permute5
    permute5_quasiMeasurePreserving fullAlternation5Coeff F).trans
      (Filter.Eventually.of_forall fun q ↦ ?_)
  simp only [fullAlternation5Coeff, fullAlternation5]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem fullAlternation4_ae_congr {f g : U4 → ℝ}
    (hfg : f =ᵐ[measureU4] g) :
    fullAlternation4 f =ᵐ[measureU4] fullAlternation4 g := by
  have hall : ∀ᵐ q ∂measureU4, ∀ σ : Equiv.Perm (Fin 4),
      f (permute4 σ q) = g (permute4 σ q) :=
    Filter.eventually_all.2 fun σ ↦
      (permute4_quasiMeasurePreserving σ).ae hfg
  filter_upwards [hall] with q hq
  simp only [fullAlternation4]
  apply congrArg ((Nat.factorial 4 : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro σ _
  rw [hq σ]

theorem fullAlternation5_ae_congr {F G : U5 → ℝ}
    (hFG : F =ᵐ[measureU5] G) :
    fullAlternation5 F =ᵐ[measureU5] fullAlternation5 G := by
  have hall : ∀ᵐ q ∂measureU5, ∀ σ : Equiv.Perm (Fin 5),
      F (permute5 σ q) = G (permute5 σ q) :=
    Filter.eventually_all.2 fun σ ↦
      (permute5_quasiMeasurePreserving σ).ae hFG
  filter_upwards [hall] with q hq
  simp only [fullAlternation5]
  apply congrArg ((Nat.factorial 5 : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro σ _
  rw [hq σ]

/-- The full four-vertex average is alternating for the six quotient
symmetries, hence is a valid input to the article's bounded-defect theorem. -/
theorem FullAlt4_coordinate_alternating (f : L0 U4 measureU4) :
    AEMeasurableAlternating concreteCoordSymmQuasiMeasurePreserving
      (FullAlt4 f) := by
  apply AEEqFun.ext
  have hfull := coeFn_FullAlt4 f
  have hfixed :
      coordinateAlt (fullAlternation4 f) =ᵐ[measureU4]
        fullAlternation4 f :=
    Filter.Eventually.of_forall fun q ↦
      congrFun (coordinateAlt_eq_self (pointAlt_fullAlternation4 f)) q
  exact (coeFn_Alt0 concreteCoordSymmQuasiMeasurePreserving
      (FullAlt4 f)).trans
    ((coordinateAlt_ae_congr concreteCoordSymmQuasiMeasurePreserving
      hfull).trans (hfixed.trans hfull.symm))

/-- Alternation of a five-point a.e. class under every normalized vertex
permutation. -/
def AEMeasurableAlternating5 (F : L0 U5 measureU5) : Prop :=
  ∀ σ : Equiv.Perm (Fin 5),
    L0.pullbackₗ (permute5 σ)
      (permute5_quasiMeasurePreserving σ) F =
        permSign ℝ σ • F

/-- A fully alternating five-point class is fixed by the normalized full
average. -/
theorem FullAlt5_fixed {F : L0 U5 measureU5}
    (hF : AEMeasurableAlternating5 F) : FullAlt5 F = F := by
  apply AEEqFun.ext
  have htransform (σ : Equiv.Perm (Fin 5)) :
      (fun q ↦ F (permute5 σ q)) =ᵐ[measureU5]
        fun q ↦ permSign ℝ σ * F q := by
    have hpull := L0.coe_pullbackₗ (permute5 σ)
      (permute5_quasiMeasurePreserving σ) F
    rw [hF σ] at hpull
    exact hpull.symm.trans (AEEqFun.coeFn_smul (permSign ℝ σ) F)
  have hall : ∀ᵐ q ∂measureU5, ∀ σ : Equiv.Perm (Fin 5),
      F (permute5 σ q) = permSign ℝ σ * F q :=
    Filter.eventually_all.2 htransform
  have hpoint : fullAlternation5 F =ᵐ[measureU5] F := by
    filter_upwards [hall] with q hq
    simp only [fullAlternation5]
    simp_rw [hq, ← mul_assoc, permSign_sq, one_mul]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin]
    norm_num [Nat.factorial]
    ring
  exact (coeFn_FullAlt5 F).trans hpoint

/-- The chain-map identity on the actual `L⁰` quotient spaces. -/
theorem D0_FullAlt4 (f : L0 U4 measureU4) :
    D0 concreteFace4QuasiMeasurePreserving (FullAlt4 f) =
      FullAlt5 (D0 concreteFace4QuasiMeasurePreserving f) := by
  apply AEEqFun.ext
  have hleft := coeFn_D0 concreteFace4QuasiMeasurePreserving (FullAlt4 f)
  have hfour := coeFn_FullAlt4 f
  have hDfour := D_ae_congr concreteFace4QuasiMeasurePreserving hfour
  have hpoint :
      D (fullAlternation4 f) =ᵐ[measureU5]
        fullAlternation5 (D f) :=
    Filter.Eventually.of_forall fun q ↦ D_fullAlternation4 f q
  have hDf := coeFn_D0 concreteFace4QuasiMeasurePreserving f
  have hfive := fullAlternation5_ae_congr hDf.symm
  have hright := coeFn_FullAlt5
    (D0 concreteFace4QuasiMeasurePreserving f)
  exact hleft.trans
    (hDfour.trans (hpoint.trans (hfive.trans hright.symm)))

/-- Internal replacement for the former `alternatedPrimitive` interface
field: alternating a measurable primitive preserves its differential. -/
theorem D0_FullAlt4_eq_of_alternating5
    (F : L0 U5 measureU5) (f : L0 U4 measureU4)
    (hF : AEMeasurableAlternating5 F)
    (hf : D0 concreteFace4QuasiMeasurePreserving f = F) :
    D0 concreteFace4QuasiMeasurePreserving (FullAlt4 f) = F := by
  rw [D0_FullAlt4, hf, FullAlt5_fixed hF]

end
end Pfaffian
end Sp4
