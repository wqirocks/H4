import Sp4.Cohomology.AffineCocycle
import Sp4.Pfaffian.Certificates
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Alternating orbit coinvariants and finite renormalization cycles. -/

namespace Sp4

open scoped BigOperators

namespace OrbitChain

noncomputable section

/-! ## Deleting an entry of a permuted tuple

The equivalence below is the order-preserving identification of `Fin n` with
the complement of one entry of `Fin (n+1)`.  Keeping this identification
explicit is what makes the incidence-sign calculation unambiguous. -/

/-- The order-preserving map into the complement of `i`. -/
def omitMap {n : ℕ} (i : Fin (n + 1)) :
    Fin n → {j : Fin (n + 1) // j ≠ i} :=
  fun j => ⟨i.succAbove j, Fin.succAbove_ne i j⟩

theorem omitMap_bijective {n : ℕ} (i : Fin (n + 1)) :
    Function.Bijective (omitMap i) := by
  constructor
  · intro a b hab
    exact Fin.succAbove_right_injective (congrArg Subtype.val hab)
  · rintro ⟨j, hj⟩
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hj
    exact ⟨k, Subtype.ext hk⟩

/-- `Fin n` identified with the complement of `i : Fin (n+1)`. -/
def omitEquiv {n : ℕ} (i : Fin (n + 1)) : Fin n ≃ {j : Fin (n + 1) // j ≠ i} :=
  Equiv.ofBijective (omitMap i) (omitMap_bijective i)

@[simp]
theorem omitEquiv_apply {n : ℕ} (i : Fin (n + 1)) (j : Fin n) :
    (omitEquiv i j).1 = i.succAbove j :=
  by
    change (omitMap i j).1 = i.succAbove j
    rfl

/-- A permutation carries the complement of `i` to the complement of `σ i`. -/
def complementEquiv {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    {j : Fin (n + 1) // j ≠ i} ≃ {j : Fin (n + 1) // j ≠ σ i} where
  toFun j := ⟨σ j.1, fun h => j.2 (σ.injective h)⟩
  invFun j := ⟨σ⁻¹ j.1, fun h => j.2 (by simpa using congrArg σ h)⟩
  left_inv j := by ext; simp
  right_inv j := by ext; simp

/-- The permutation induced after deleting position `i` and its image `σ i`. -/
def deletePerm {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    Equiv.Perm (Fin n) :=
  (omitEquiv i).trans ((complementEquiv σ i).trans (omitEquiv (σ i)).symm)

/-- Characterizing equation for the permutation induced by deletion. -/
theorem succAbove_deletePerm {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) (k : Fin n) :
    (σ i).succAbove (deletePerm σ i k) = σ (i.succAbove k) := by
  have h := (omitEquiv (σ i)).apply_symm_apply
    (complementEquiv σ i (omitEquiv i k))
  change (omitEquiv (σ i)
    ((omitEquiv (σ i)).symm
      (complementEquiv σ i (omitEquiv i k)))).1 = _
  exact congrArg Subtype.val h

/-- Extend a permutation of the complement of `i` by fixing `i`.  The
equivalence `finSuccEquiv'` identifies the distinguished point with `none` and
the ordered complement with `some`. -/
def extendPermAt {n : ℕ} (i : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' i).trans
    ((Equiv.optionCongr τ).trans (finSuccEquiv' i).symm)

@[simp]
theorem extendPermAt_fixed {n : ℕ} (i : Fin (n + 1))
    (τ : Equiv.Perm (Fin n)) : extendPermAt i τ i = i := by
  simp [extendPermAt, finSuccEquiv'_at, finSuccEquiv'_symm_none]

@[simp]
theorem extendPermAt_succAbove {n : ℕ} (i : Fin (n + 1))
    (τ : Equiv.Perm (Fin n)) (k : Fin n) :
    extendPermAt i τ (i.succAbove k) = i.succAbove (τ k) := by
  simp [extendPermAt, finSuccEquiv'_succAbove, finSuccEquiv'_symm_some]

@[simp]
theorem deletePerm_extendPermAt {n : ℕ} (i : Fin (n + 1))
    (τ : Equiv.Perm (Fin n)) : deletePerm (extendPermAt i τ) i = τ := by
  apply Equiv.ext
  intro k
  have h := succAbove_deletePerm (extendPermAt i τ) i k
  rw [extendPermAt_fixed, extendPermAt_succAbove] at h
  exact Fin.succAbove_right_injective h

/-- Deleting a permuted tuple is permutation of the corresponding deleted
tuple.  Our convention is `permute σ x = x ∘ σ`. -/
theorem delete_permute {X : Type*} {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1))
    (x : FinTuple X (n + 1)) :
    FinTuple.delete i (FinTuple.permute σ x) =
      FinTuple.permute (deletePerm σ i)
        (FinTuple.delete (σ i) x) := by
  funext k
  change x (σ (i.succAbove k)) = x ((σ i).succAbove (deletePerm σ i k))
  rw [succAbove_deletePerm]

/-- The minor of a permutation matrix is the permutation matrix of the
deletion-induced permutation. -/
theorem permMatrix_submatrix_delete {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    (σ.permMatrix ℤ).submatrix i.succAbove (σ i).succAbove =
      (deletePerm σ i).permMatrix ℤ := by
  ext a b
  simp only [Matrix.submatrix_apply, PEquiv.toMatrix_apply,
    Equiv.toPEquiv_apply]
  by_cases h : deletePerm σ i a = b
  · have hs : σ (i.succAbove a) = (σ i).succAbove b := by
      rw [← succAbove_deletePerm σ i a, h]
    simp [h, hs]
  · have hs : σ (i.succAbove a) ≠ (σ i).succAbove b := by
      intro hs
      apply h
      apply Fin.succAbove_right_injective
      rw [succAbove_deletePerm]
      exact hs
    simp [h, hs]

/-- Incidence signs are compatible with deleting an entry of a permutation.
This is the determinant/cofactor proof of the deletion--permutation sign
lemma requested in the article. -/
theorem deletePerm_incidence_sign {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    (-1 : ℤ) ^ (σ i).val * Equiv.Perm.sign (deletePerm σ i) =
      (-1 : ℤ) ^ i.val * Equiv.Perm.sign σ := by
  let P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := σ.permMatrix ℤ
  have hdet := Matrix.det_succ_row P i
  have hsum :
      (∑ j : Fin (n + 1),
        (-1 : ℤ) ^ (i.val + j.val) * P i j *
          Matrix.det (P.submatrix i.succAbove j.succAbove)) =
        (-1 : ℤ) ^ (i.val + (σ i).val) *
          Matrix.det (P.submatrix i.succAbove (σ i).succAbove) := by
    classical
    rw [Finset.sum_eq_single (σ i)]
    · simp [P]
    · intro j _ hj
      have hne : σ i ≠ j := Ne.symm hj
      simp [P, hne]
    · simp
  have hsign : Equiv.Perm.sign σ =
      (-1 : ℤ) ^ (i.val + (σ i).val) *
        Equiv.Perm.sign (deletePerm σ i) := by
    rw [Matrix.det_permutation] at hdet
    rw [hsum, permMatrix_submatrix_delete, Matrix.det_permutation] at hdet
    exact hdet
  have hsquare :
      (-1 : ℤ) ^ i.val * (-1 : ℤ) ^ i.val = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hsign, pow_add]
  calc
    (-1 : ℤ) ^ (σ i).val * Equiv.Perm.sign (deletePerm σ i) =
        ((-1 : ℤ) ^ i.val * (-1 : ℤ) ^ i.val) *
          ((-1 : ℤ) ^ (σ i).val * Equiv.Perm.sign (deletePerm σ i)) := by
            rw [hsquare, one_mul]
    _ = _ := by ring

/-- The same incidence identity in the form used when the boundary sum is
reindexed by `i ↦ σ i`. -/
theorem deletePerm_incidence_sign' {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    (-1 : ℤ) ^ i.val * Equiv.Perm.sign (deletePerm σ i) =
      (-1 : ℤ) ^ (σ i).val * Equiv.Perm.sign σ := by
  have h := deletePerm_incidence_sign σ i
  have hi : (-1 : ℤ) ^ i.val * (-1 : ℤ) ^ i.val = 1 := by
    rw [← mul_pow]
    norm_num
  have hj : (-1 : ℤ) ^ (σ i).val * (-1 : ℤ) ^ (σ i).val = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    (-1 : ℤ) ^ i.val * Equiv.Perm.sign (deletePerm σ i) =
        ((-1 : ℤ) ^ i.val * (-1 : ℤ) ^ (σ i).val) *
          ((-1 : ℤ) ^ (σ i).val *
            Equiv.Perm.sign (deletePerm σ i)) := by
      calc
        _ = 1 * ((-1 : ℤ) ^ i.val *
            Equiv.Perm.sign (deletePerm σ i)) := by rw [one_mul]
        _ = ((-1 : ℤ) ^ (σ i).val *
              (-1 : ℤ) ^ (σ i).val) *
            ((-1 : ℤ) ^ i.val *
              Equiv.Perm.sign (deletePerm σ i)) := by rw [hj]
        _ = _ := by ring
    _ = ((-1 : ℤ) ^ i.val * (-1 : ℤ) ^ (σ i).val) *
          ((-1 : ℤ) ^ i.val * Equiv.Perm.sign σ) := by rw [h]
    _ = (-1 : ℤ) ^ (σ i).val * Equiv.Perm.sign σ := by
      calc
        _ = ((-1 : ℤ) ^ i.val * (-1 : ℤ) ^ i.val) *
            ((-1 : ℤ) ^ (σ i).val * Equiv.Perm.sign σ) := by ring
        _ = _ := by rw [hi, one_mul]

/-! ## The raw generic configuration complex -/

/-- Generic ordered projective configurations. -/
abbrev GenericConfig (n : ℕ) := {x : ProjectiveConfig n // IsGeneric x}

/-- Delete a vertex of a generic configuration. -/
def face {n : ℕ} (i : Fin (n + 1)) (x : GenericConfig (n + 1)) :
    GenericConfig n :=
  ⟨FinTuple.delete i x.1, x.2.delete i⟩

/-- Permute the vertices of a generic configuration. -/
def permuteGeneric {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : GenericConfig n) :
    GenericConfig n := by
  refine ⟨FinTuple.permute σ x.1, ?_⟩
  constructor
  · intro i j hij
    exact x.2.pairwise_transverse (σ i) (σ j) (σ.injective.ne hij)
  · intro e he
    exact x.2.four_spans (σ ∘ e) (σ.injective.comp he)

/-- Apply a symplectic transformation to a generic configuration. -/
def smulGeneric {n : ℕ} (g : SymplecticGroup) (x : GenericConfig n) :
    GenericConfig n :=
  ⟨g • x.1, x.2.smul g⟩

@[simp]
theorem smulGeneric_one {n : ℕ} (x : GenericConfig n) :
    smulGeneric 1 x = x := by
  apply Subtype.ext
  simp [smulGeneric]

@[simp]
theorem smulGeneric_mul {n : ℕ} (g h : SymplecticGroup)
    (x : GenericConfig n) :
    smulGeneric (g * h) x = smulGeneric g (smulGeneric h x) := by
  apply Subtype.ext
  simp [smulGeneric, mul_smul]

/-- The symplectic action on generic configurations as a genuine typeclass
action.  Earlier files retain the named map `smulGeneric` so that all formulas
remain explicit. -/
instance genericConfigMulAction (n : ℕ) :
    MulAction SymplecticGroup (GenericConfig n) where
  smul := smulGeneric
  one_smul := smulGeneric_one
  mul_smul := smulGeneric_mul

@[simp]
theorem smul_generic_eq_smulGeneric {n : ℕ} (g : SymplecticGroup)
    (x : GenericConfig n) : g • x = smulGeneric g x :=
  rfl

@[simp]
theorem face_smulGeneric {n : ℕ} (i : Fin (n + 1))
    (g : SymplecticGroup) (x : GenericConfig (n + 1)) :
    face i (smulGeneric g x) = smulGeneric g (face i x) := by
  apply Subtype.ext
  rfl

theorem face_permuteGeneric {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (i : Fin (n + 1)) (x : GenericConfig (n + 1)) :
    face i (permuteGeneric σ x) =
      permuteGeneric (deletePerm σ i) (face (σ i) x) := by
  apply Subtype.ext
  exact delete_permute σ i x.1

/-- The free `R`-module on generic ordered configurations. -/
abbrev Raw (R : Type*) [Semiring R] (n : ℕ) := GenericConfig n →₀ R

/-- A basis generator of the raw configuration module. -/
def generator {R : Type*} [Semiring R] {n : ℕ} (x : GenericConfig n) : Raw R n :=
  Finsupp.single x 1

/-- The alternating boundary of one ordered configuration. -/
def boundaryGenerator (R : Type*) [CommRing R] {n : ℕ}
    (x : GenericConfig (n + 1)) : Raw R n :=
  ∑ i : Fin (n + 1), (-1 : R) ^ i.val • generator (face i x)

/-- Linear extension of the alternating boundary. -/
def rawBoundary (R : Type*) [CommRing R] (n : ℕ) :
    Raw R (n + 1) →ₗ[R] Raw R n :=
  Finsupp.linearCombination R (boundaryGenerator R)

@[simp]
theorem rawBoundary_generator (R : Type*) [CommRing R] {n : ℕ}
    (x : GenericConfig (n + 1)) :
    rawBoundary R n (generator x) = boundaryGenerator R x := by
  simp [rawBoundary, generator]

theorem face_face {n : ℕ} (x : GenericConfig (n + 2))
    (i : Fin (n + 1)) (j : Fin (n + 2)) :
    face i (face j x) =
      face (i.predAbove j) (face (j.succAbove i) x) := by
  apply Subtype.ext
  exact FinTuple.delete_delete_swap x.1 i j

/-- The raw alternating boundary squares to zero. -/
theorem rawBoundary_sq (R : Type*) [CommRing R] (n : ℕ) :
    rawBoundary R n ∘ₗ rawBoundary R (n + 1) = 0 := by
  apply LinearMap.ext
  intro c
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add x a c hx hc ih =>
      simp only [LinearMap.comp_apply, map_add, ih, LinearMap.zero_apply, add_zero]
      rw [show Finsupp.single x a = a • generator x by
        ext y
        simp [generator]]
      rw [map_smul]
      suffices hgenerator :
          rawBoundary R n (rawBoundary R (n + 1) (generator x)) = 0 by
        rw [map_smul, hgenerator, smul_zero]
      simp only [rawBoundary_generator, boundaryGenerator, map_sum, map_smul]
      let swapPair : Fin (n + 2) × Fin (n + 1) → Fin (n + 2) × Fin (n + 1) :=
        fun p => (p.1.succAbove p.2, p.2.predAbove p.1)
      have hzero :
          ∑ p : Fin (n + 2) × Fin (n + 1),
            ((-1 : R) ^ p.1.val * (-1 : R) ^ p.2.val) •
              generator (R := R) (face p.2 (face p.1 x)) = 0 := by
        classical
        apply Finset.sum_involution (s := Finset.univ)
          (fun p _ => swapPair p)
        · intro p _
          rcases p with ⟨j, i⟩
          have hsign := Fin.neg_one_pow_succAbove_add_predAbove
            (R := R) j i
          rw [face_face x i j]
          change _ +
            ((-1 : R) ^ (j.succAbove i).val *
              (-1 : R) ^ (i.predAbove j).val) • _ = 0
          rw [← pow_add, ← pow_add, hsign]
          module
        · intro p _ _
          exact fun h => Fin.succAbove_ne p.1 p.2 (congrArg Prod.fst h)
        · simp
        · rintro ⟨j, i⟩ _
          apply Prod.ext
          · exact Fin.succAbove_succAbove_predAbove j i
          · exact Fin.predAbove_predAbove_succAbove j i
      simp only [Finset.smul_sum, smul_smul]
      rw [← Fintype.sum_prod_type']
      exact hzero

/-! ## Alternating symplectic coinvariants -/

/-- The sign of a finite permutation, in the coefficient ring. -/
def permSign (R : Type*) [CommRing R] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) : R :=
  ((Equiv.Perm.sign σ : ℤ) : R)

@[simp]
theorem permSign_one (R : Type*) [CommRing R] {n : ℕ} :
    permSign R (1 : Equiv.Perm (Fin n)) = 1 := by
  simp [permSign]

@[simp]
theorem permSign_mul (R : Type*) [CommRing R] {n : ℕ}
    (σ τ : Equiv.Perm (Fin n)) :
    permSign R (σ * τ) = permSign R σ * permSign R τ := by
  simp [permSign, Equiv.Perm.sign_mul]

@[simp]
theorem permSign_sq (R : Type*) [CommRing R] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) : permSign R σ * permSign R σ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    simp [permSign, h]

/-- Extending by a fixed point does not change the permutation sign. -/
theorem permSign_extendPermAt (R : Type*) [CommRing R] {n : ℕ}
    (i : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    permSign R (extendPermAt i τ) = permSign R τ := by
  have h := deletePerm_incidence_sign (extendPermAt i τ) i
  rw [extendPermAt_fixed, deletePerm_extendPermAt] at h
  have hsign : Equiv.Perm.sign (extendPermAt i τ) = Equiv.Perm.sign τ := by
    have hn : (-1 : ℤ) ^ i.val ≠ 0 := pow_ne_zero _ (by norm_num)
    apply Units.ext
    exact (mul_left_cancel₀ hn h).symm
  simp [permSign, hsign]

theorem deletePerm_incidence_sign_cast (R : Type*) [CommRing R] {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    (-1 : R) ^ i.val * permSign R (deletePerm σ i) =
      (-1 : R) ^ (σ i).val * permSign R σ := by
  have h := congrArg (Int.castRingHom R) (deletePerm_incidence_sign' σ i)
  simpa [permSign] using h

/-- A symplectic coinvariant relation in the free configuration module. -/
def groupRelation (R : Type*) [CommRing R] {n : ℕ}
    (g : SymplecticGroup) (x : GenericConfig n) : Raw R n :=
  generator (smulGeneric g x) - generator x

/-- A signed permutation relation in the free configuration module. -/
def permutationRelation (R : Type*) [CommRing R] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : GenericConfig n) : Raw R n :=
  generator (permuteGeneric σ x) - permSign R σ • generator x

/-- The submodule generated by symplectic orbit relations and signed
permutation relations. -/
def relations (R : Type*) [CommRing R] (n : ℕ) : Submodule R (Raw R n) :=
  Submodule.span R
    ({c | ∃ (g : SymplecticGroup) (x : GenericConfig n),
        c = groupRelation R g x} ∪
      {c | ∃ (σ : Equiv.Perm (Fin n)) (x : GenericConfig n),
        c = permutationRelation R σ x})

theorem groupRelation_mem (R : Type*) [CommRing R] {n : ℕ}
    (g : SymplecticGroup) (x : GenericConfig n) :
    groupRelation R g x ∈ relations R n := by
  apply Submodule.subset_span
  left
  exact ⟨g, x, rfl⟩

theorem permutationRelation_mem (R : Type*) [CommRing R] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : GenericConfig n) :
    permutationRelation R σ x ∈ relations R n := by
  apply Submodule.subset_span
  right
  exact ⟨σ, x, rfl⟩

/-- Alternating symplectic orbit chains on generic `n`-tuples. -/
abbrev Module (R : Type*) [CommRing R] (n : ℕ) :=
  Raw R n ⧸ relations R n

/-- The class of one oriented generic configuration. -/
def ofConfig {R : Type*} [CommRing R] {n : ℕ}
    (x : GenericConfig n) : Module R n :=
  Submodule.Quotient.mk (generator x)

theorem ofConfig_smulGeneric {R : Type*} [CommRing R] {n : ℕ}
    (g : SymplecticGroup) (x : GenericConfig n) :
    ofConfig (R := R) (smulGeneric g x) = ofConfig (R := R) x := by
  apply (Submodule.Quotient.eq (relations R n)).2
  exact groupRelation_mem R g x

theorem ofConfig_permuteGeneric {R : Type*} [CommRing R] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : GenericConfig n) :
    ofConfig (R := R) (permuteGeneric σ x) =
      permSign R σ • ofConfig (R := R) x := by
  change Submodule.Quotient.mk (generator (R := R) (permuteGeneric σ x)) =
    Submodule.Quotient.mk (permSign R σ • generator (R := R) x)
  apply (Submodule.Quotient.eq (relations R n)).2
  exact permutationRelation_mem R σ x

/-- The boundary of a permuted generator, computed in the alternating orbit
quotient. -/
theorem quotient_boundary_permute {R : Type*} [CommRing R] {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (x : GenericConfig (n + 1)) :
    (∑ i : Fin (n + 1), (-1 : R) ^ i.val •
        ofConfig (R := R) (face i (permuteGeneric σ x))) =
      permSign R σ •
        ∑ j : Fin (n + 1), (-1 : R) ^ j.val •
          ofConfig (R := R) (face j x) := by
  simp_rw [face_permuteGeneric, ofConfig_permuteGeneric, smul_smul]
  calc
    (∑ i : Fin (n + 1),
        ((-1 : R) ^ i.val * permSign R (deletePerm σ i)) •
          ofConfig (R := R) (face (σ i) x)) =
        ∑ i : Fin (n + 1),
          ((-1 : R) ^ (σ i).val * permSign R σ) •
            ofConfig (R := R) (face (σ i) x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [deletePerm_incidence_sign_cast]
    _ = permSign R σ •
        ∑ i : Fin (n + 1), (-1 : R) ^ (σ i).val •
          ofConfig (R := R) (face (σ i) x) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul]
      congr 1
      ring
    _ = permSign R σ •
        ∑ j : Fin (n + 1), (-1 : R) ^ j.val •
          ofConfig (R := R) (face j x) := by
      congr 1
      exact Function.Bijective.sum_comp σ.bijective
        (fun j : Fin (n + 1) =>
          (-1 : R) ^ j.val • ofConfig (R := R) (face j x))

/-- The quotient projection after the raw boundary kills every orbit relation. -/
theorem relations_le_boundary_ker (R : Type*) [CommRing R] (n : ℕ) :
    relations R (n + 1) ≤
      LinearMap.ker ((relations R n).mkQ.comp (rawBoundary R n)) := by
  rw [relations, Submodule.span_le]
  intro c hc
  rcases hc with hc | hc
  · rcases hc with ⟨g, x, rfl⟩
    change (relations R n).mkQ
      (rawBoundary R n (groupRelation R g x)) = 0
    simp only [groupRelation, map_sub, rawBoundary_generator,
      boundaryGenerator, map_sum, map_smul, Submodule.mkQ_apply]
    simp_rw [face_smulGeneric]
    change (∑ i : Fin (n + 1), (-1 : R) ^ i.val •
      ofConfig (R := R) (smulGeneric g (face i x))) -
        ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
          ofConfig (R := R) (face i x) = 0
    simp_rw [ofConfig_smulGeneric]
    rw [sub_self]
  · rcases hc with ⟨σ, x, rfl⟩
    change (relations R n).mkQ
      (rawBoundary R n (permutationRelation R σ x)) = 0
    simp only [permutationRelation, map_sub, map_smul,
      rawBoundary_generator, boundaryGenerator, map_sum,
      Submodule.mkQ_apply]
    change (∑ i : Fin (n + 1), (-1 : R) ^ i.val •
      ofConfig (R := R) (face i (permuteGeneric σ x))) -
        permSign R σ •
          ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
            ofConfig (R := R) (face i x) = 0
    rw [quotient_boundary_permute, sub_self]

/-- Boundary on alternating symplectic orbit chains. -/
def boundary (R : Type*) [CommRing R] (n : ℕ) :
    Module R (n + 1) →ₗ[R] Module R n :=
  (relations R (n + 1)).liftQ
    ((relations R n).mkQ.comp (rawBoundary R n))
    (relations_le_boundary_ker R n)

@[simp]
theorem boundary_ofConfig (R : Type*) [CommRing R] {n : ℕ}
    (x : GenericConfig (n + 1)) :
    boundary R n (ofConfig (R := R) x) =
      ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
        ofConfig (R := R) (face i x) := by
  change (relations R n).mkQ (rawBoundary R n (generator x)) = _
  rw [rawBoundary_generator]
  simp [boundaryGenerator, ofConfig]

/-- The descended orbit-chain boundary squares to zero. -/
theorem boundary_sq (R : Type*) [CommRing R] (n : ℕ) :
    boundary R n ∘ₗ boundary R (n + 1) = 0 := by
  apply LinearMap.ext
  intro z
  obtain ⟨c, rfl⟩ := (relations R (n + 2)).mkQ_surjective z
  change (relations R n).mkQ
    (rawBoundary R n (rawBoundary R (n + 1) c)) = 0
  have h := LinearMap.congr_fun (rawBoundary_sq R n) c
  change rawBoundary R n (rawBoundary R (n + 1) c) = 0 at h
  rw [h, map_zero]

end

end OrbitChain

end Sp4
