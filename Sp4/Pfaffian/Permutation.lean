import Sp4.Chains.Normalized

/-!
# Normalized permutation maps

Vertex permutations act on Gram matrices by simultaneous reindexing.  This
file gives the resulting rational self-maps of the four- and five-point
normalized charts.  The five-point construction is deliberately derived from
diagonal normalization rather than from an unproved quotient choice.
-/

namespace Sp4
namespace Pfaffian

noncomputable section

open Matrix AffineCocycle OrbitChain

/-- Simultaneous row/column reindexing, in the tuple convention `x ↦ x ∘ σ`. -/
def reindexGram {n : ℕ} (σ : Equiv.Perm (Fin n))
    (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦ A (σ i) (σ j)

theorem reindexGram_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (σ τ : Equiv.Perm (Fin n)) :
    reindexGram (σ * τ) A = reindexGram τ (reindexGram σ A) := by
  rfl

@[simp]
theorem reindexGram_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    reindexGram 1 A = A := by
  rfl

theorem affineDifference_reindexGram {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (σ : Equiv.Perm (Fin n))
    (i j k l m : Fin n) :
    affineDifference (reindexGram σ A) i j k l m =
      affineDifference A (σ i) (σ j) (σ k) (σ l) (σ m) := by
  rfl

theorem rawTerm_reindexGram (A : Matrix (Fin 5) (Fin 5) ℂ)
    (σ τ : Equiv.Perm (Fin 5)) :
    rawTerm (reindexGram σ A) τ =
      permSign ℂ σ * rawTerm A (σ * τ) := by
  rw [rawTerm, affineDifference_reindexGram, rawTerm]
  change permSign ℂ τ * _ =
    permSign ℂ σ * (permSign ℂ (σ * τ) * _)
  rw [permSign_mul]
  change permSign ℂ τ * _ =
    permSign ℂ σ * (permSign ℂ σ * permSign ℂ τ * _)
  rw [← mul_assoc, ← mul_assoc, permSign_sq, one_mul]
  simp only [Equiv.Perm.mul_apply]

/-- The original 120-term average is alternating under reindexing. -/
theorem rawAlternationR_reindexGram
    (A : Matrix (Fin 5) (Fin 5) ℂ) (σ : Equiv.Perm (Fin 5)) :
    rawAlternationR (reindexGram σ A) =
      permSign ℂ σ * rawAlternationR A := by
  rw [rawAlternationR, rawAlternationR]
  simp_rw [rawTerm_reindexGram]
  rw [← Finset.mul_sum]
  have hsum := Equiv.sum_comp (Equiv.mulLeft σ) (fun τ ↦ rawTerm A τ)
  change (∑ τ : Equiv.Perm (Fin 5), rawTerm A (σ * τ)) =
    ∑ τ : Equiv.Perm (Fin 5), rawTerm A τ at hsum
  rw [hsum]
  ring

/-- The original 120-term average is invariant under rescaling each Gram
lift independently. -/
theorem rawAlternationR_diagonalCongruence
    (A : Matrix (Fin 5) (Fin 5) ℂ) (d : Fin 5 → ℂˣ) :
    rawAlternationR
        (Sp4.diagonalCongruence (fun i ↦ (d i : ℂ)) A) =
      rawAlternationR A := by
  rw [rawAlternationR, rawAlternationR]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [rawTerm, rawTerm]
  congr 1
  exact affineDifference_diagonalScale A (fun i ↦ (d i : ℂ))
    (fun i ↦ Units.ne_zero (d i)) (σ 0) (σ 1) (σ 2) (σ 3) (σ 4)

/-- Reindexing carries a diagonal congruence to the correspondingly reindexed
diagonal congruence. -/
theorem reindexGram_diagonalCongruence {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (A : Matrix (Fin n) (Fin n) ℂ)
    (d : Fin n → ℂ) :
    reindexGram σ (Sp4.diagonalCongruence d A) =
      Sp4.diagonalCongruence (fun i ↦ d (σ i)) (reindexGram σ A) := by
  rfl

/-- Simultaneous reindexing commutes with deletion, with the induced
permutation on the remaining vertices. -/
theorem deleteMatrix_reindexGram {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1))
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    deleteMatrix i (reindexGram σ A) =
      reindexGram (deletePerm σ i) (deleteMatrix (σ i) A) := by
  ext a b
  change A (σ (i.succAbove a)) (σ (i.succAbove b)) =
    A ((σ i).succAbove (deletePerm σ i a))
      ((σ i).succAbove (deletePerm σ i b))
  rw [succAbove_deletePerm, succAbove_deletePerm]

/-- Deleting a principal row and column from a diagonal congruence restricts
the diagonal factors to the surviving indices. -/
theorem deleteMatrix_diagonalCongruence {n : ℕ}
    (i : Fin (n + 1)) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (d : Fin (n + 1) → ℂ) :
    deleteMatrix i (Sp4.diagonalCongruence d A) =
      Sp4.diagonalCongruence (fun a ↦ d (i.succAbove a))
        (deleteMatrix i A) := by
  rfl

theorem isSkew_reindexGram {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : IsSkew A) (σ : Equiv.Perm (Fin n)) :
    IsSkew (reindexGram σ A) := by
  intro i j
  exact hA (σ i) (σ j)

theorem isAdmissibleGram_reindex {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsAdmissibleGram A)
    (σ : Equiv.Perm (Fin n)) : IsAdmissibleGram (reindexGram σ A) := by
  refine {
    skew := isSkew_reindexGram hA.skew σ
    rank_four := ?_
    offDiagonal_ne := ?_
    principal_four_ne := ?_ }
  · change (A.submatrix σ σ).rank = 4
    rw [Matrix.rank_submatrix]
    exact hA.rank_four
  · intro i j hij
    exact hA.offDiagonal_ne (σ i) (σ j) (σ.injective.ne hij)
  · intro e he
    change (A.submatrix (σ ∘ e) (σ ∘ e)).det ≠ 0
    exact hA.principal_four_ne (σ ∘ e) (σ.injective.comp he)

/-- The normalized value of an entry whose two indices are nonzero. -/
def normalizedEntry {n : ℕ} (A : Matrix (Fin (n + 3)) (Fin (n + 3)) ℂ)
    (i j : Fin (n + 3)) : ℂ :=
  A i j * A 0 1 * A 0 2 / (A 1 2 * A 0 i * A 0 j)

/-- Five affine coordinates extracted invariantly from a generic Gram matrix. -/
def chi5 (A : Matrix (Fin 5) (Fin 5) ℂ) : Coord5 :=
  ⟨normalizedEntry A 1 3, normalizedEntry A 1 4,
    normalizedEntry A 2 3, normalizedEntry A 2 4,
    normalizedEntry A 3 4⟩

@[simp]
theorem chi5_matrix5 (q : Coord5) : chi5 (matrix5 q) = q := by
  apply Coord5.ext <;> simp [chi5, normalizedEntry, matrix5]

/-- `chi5` is unchanged by a nonzero diagonal congruence. -/
theorem chi5_diagonalCongruence (A : Matrix (Fin 5) (Fin 5) ℂ)
    (d : Fin 5 → ℂˣ) (hoff : ∀ i j, i ≠ j → A i j ≠ 0) :
    chi5 (diagonalCongruence (fun i ↦ (d i : ℂ)) A) = chi5 A := by
  apply Coord5.ext <;>
    simp only [chi5, normalizedEntry, diagonalCongruence] <;>
    field_simp [Units.ne_zero, hoff 1 2 (by decide),
      hoff 0 1 (by decide), hoff 0 2 (by decide),
      hoff 0 3 (by decide), hoff 0 4 (by decide)] <;>
    ring

/-- A normalized skew five-by-five matrix is reconstructed from `chi5`. -/
theorem matrix5_chi5_of_normalized_skew
    (A : Matrix (Fin 5) (Fin 5) ℂ) (hA : IsSkew A)
    (hN : IsNormalized A) : matrix5 (chi5 A) = A := by
  have h00 : A 0 0 = 0 := CharZero.eq_neg_self_iff.mp (hA 0 0)
  have h11 : A 1 1 = 0 := CharZero.eq_neg_self_iff.mp (hA 1 1)
  have h22 : A 2 2 = 0 := CharZero.eq_neg_self_iff.mp (hA 2 2)
  have h33 : A 3 3 = 0 := CharZero.eq_neg_self_iff.mp (hA 3 3)
  have h44 : A 4 4 = 0 := CharZero.eq_neg_self_iff.mp (hA 4 4)
  have h01 : A 0 1 = 1 := hN.firstRow 1 (by decide)
  have h02 : A 0 2 = 1 := hN.firstRow 2 (by decide)
  have h03 : A 0 3 = 1 := hN.firstRow 3 (by decide)
  have h04 : A 0 4 = 1 := hN.firstRow 4 (by decide)
  have h12 : A 1 2 = 1 := hN.twelve
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix5, chi5, normalizedEntry, h00, h11, h22, h33, h44,
      h01, h02, h03, h04, h12, hA 0 1, hA 0 2, hA 0 3,
      hA 0 4, hA 1 2, hA 1 3, hA 1 4, hA 2 3, hA 2 4,
      hA 3 4]

/-- Normalizing any generic skew five-by-five matrix gives `matrix5 (chi5 A)`. -/
theorem exists_matrix5_chi5_diagonalCongruence
    (A : Matrix (Fin 5) (Fin 5) ℂ) (hA : IsSkew A)
    (hoff : ∀ i j, i ≠ j → A i j ≠ 0) :
    ∃ d : Fin 5 → ℂˣ,
      matrix5 (chi5 A) =
        diagonalCongruence (fun i ↦ (d i : ℂ)) A := by
  obtain ⟨d, hN⟩ := exists_normalized_diagonalCongruence A hoff
  let C := diagonalCongruence (fun i ↦ (d i : ℂ)) A
  have hCskew : IsSkew C := OrbitChain.isSkew_diagonalCongruence hA _
  have hchi : chi5 C = chi5 A := chi5_diagonalCongruence A d hoff
  refine ⟨d, ?_⟩
  calc
    matrix5 (chi5 A) = matrix5 (chi5 C) := congrArg matrix5 hchi.symm
    _ = C := matrix5_chi5_of_normalized_skew C hCskew hN

/-! ## Six-point normalization -/

/-- Nine affine coordinates extracted invariantly from a generic six-point
Gram matrix. -/
def chi6 (A : Matrix (Fin 6) (Fin 6) ℂ) : Coord6 :=
  ⟨normalizedEntry A 1 3, normalizedEntry A 1 4,
    normalizedEntry A 1 5, normalizedEntry A 2 3,
    normalizedEntry A 2 4, normalizedEntry A 2 5,
    normalizedEntry A 3 4, normalizedEntry A 3 5,
    normalizedEntry A 4 5⟩

@[simp]
theorem chi6_matrix6 (q : Coord6) : chi6 (matrix6 q) = q := by
  apply Coord6.ext <;> simp [chi6, normalizedEntry, matrix6]

/-- `chi6` is unchanged by a nonzero diagonal congruence. -/
theorem chi6_diagonalCongruence (A : Matrix (Fin 6) (Fin 6) ℂ)
    (d : Fin 6 → ℂˣ) (hoff : ∀ i j, i ≠ j → A i j ≠ 0) :
    chi6 (diagonalCongruence (fun i ↦ (d i : ℂ)) A) = chi6 A := by
  apply Coord6.ext <;>
    simp only [chi6, normalizedEntry, diagonalCongruence] <;>
    field_simp [Units.ne_zero, hoff 1 2 (by decide),
      hoff 0 1 (by decide), hoff 0 2 (by decide),
      hoff 0 3 (by decide), hoff 0 4 (by decide),
      hoff 0 5 (by decide)] <;>
    ring

/-- A normalized skew six-by-six matrix is reconstructed from `chi6`. -/
theorem matrix6_chi6_of_normalized_skew
    (A : Matrix (Fin 6) (Fin 6) ℂ) (hA : IsSkew A)
    (hN : IsNormalized A) : matrix6 (chi6 A) = A := by
  have h00 : A 0 0 = 0 := CharZero.eq_neg_self_iff.mp (hA 0 0)
  have h11 : A 1 1 = 0 := CharZero.eq_neg_self_iff.mp (hA 1 1)
  have h22 : A 2 2 = 0 := CharZero.eq_neg_self_iff.mp (hA 2 2)
  have h33 : A 3 3 = 0 := CharZero.eq_neg_self_iff.mp (hA 3 3)
  have h44 : A 4 4 = 0 := CharZero.eq_neg_self_iff.mp (hA 4 4)
  have h55 : A 5 5 = 0 := CharZero.eq_neg_self_iff.mp (hA 5 5)
  have h01 : A 0 1 = 1 := hN.firstRow 1 (by decide)
  have h02 : A 0 2 = 1 := hN.firstRow 2 (by decide)
  have h03 : A 0 3 = 1 := hN.firstRow 3 (by decide)
  have h04 : A 0 4 = 1 := hN.firstRow 4 (by decide)
  have h05 : A 0 5 = 1 := hN.firstRow 5 (by decide)
  have h12 : A 1 2 = 1 := hN.twelve
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix6, chi6, normalizedEntry, h00, h11, h22, h33, h44,
      h55, h01, h02, h03, h04, h05, h12, hA 0 1, hA 0 2,
      hA 0 3, hA 0 4, hA 0 5, hA 1 2, hA 1 3, hA 1 4,
      hA 1 5, hA 2 3, hA 2 4, hA 2 5, hA 3 4, hA 3 5,
      hA 4 5]

/-- Normalizing any generic skew six-by-six matrix gives `matrix6 (chi6 A)`. -/
theorem exists_matrix6_chi6_diagonalCongruence
    (A : Matrix (Fin 6) (Fin 6) ℂ) (hA : IsSkew A)
    (hoff : ∀ i j, i ≠ j → A i j ≠ 0) :
    ∃ d : Fin 6 → ℂˣ,
      matrix6 (chi6 A) =
        diagonalCongruence (fun i ↦ (d i : ℂ)) A := by
  obtain ⟨d, hN⟩ := exists_normalized_diagonalCongruence A hoff
  let C := diagonalCongruence (fun i ↦ (d i : ℂ)) A
  have hCskew : IsSkew C := OrbitChain.isSkew_diagonalCongruence hA _
  have hchi : chi6 C = chi6 A := chi6_diagonalCongruence A d hoff
  refine ⟨d, ?_⟩
  calc
    matrix6 (chi6 A) = matrix6 (chi6 C) := congrArg matrix6 hchi.symm
    _ = C := matrix6_chi6_of_normalized_skew C hCskew hN

/-- Diagonal congruence preserves admissibility. -/
theorem isAdmissibleGram_diagonalCongruence {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsAdmissibleGram A)
    (d : Fin n → ℂˣ) :
    IsAdmissibleGram (diagonalCongruence (fun i ↦ (d i : ℂ)) A) := by
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i ↦ (d i : ℂ))
  have hDinv : IsUnit D := by
    rw [Matrix.isUnit_iff_isUnit_det]
    apply isUnit_iff_ne_zero.mpr
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ Units.ne_zero _
  have hDdet : IsUnit D.det := (Matrix.isUnit_iff_isUnit_det D).mp hDinv
  refine {
    skew := OrbitChain.isSkew_diagonalCongruence hA.skew _
    rank_four := ?_
    offDiagonal_ne := ?_
    principal_four_ne := ?_ }
  · have hmatrix : Sp4.diagonalCongruence (fun i ↦ (d i : ℂ)) A = D * A * D := by
      ext i j
      change (d i : ℂ) * A i j * (d j : ℂ) = (D * A * D) i j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [hmatrix, Matrix.rank_mul_eq_left_of_isUnit_det D (D * A) hDdet,
      Matrix.rank_mul_eq_right_of_isUnit_det D A hDdet]
    exact hA.rank_four
  · intro i j hij
    exact mul_ne_zero (mul_ne_zero (Units.ne_zero _) (hA.offDiagonal_ne i j hij))
      (Units.ne_zero _)
  · intro e he
    have hsub :
        (Sp4.diagonalCongruence (fun i ↦ (d i : ℂ)) A).submatrix e e =
          Sp4.diagonalCongruence (fun i ↦ (d (e i) : ℂ)) (A.submatrix e e) := rfl
    rw [hsub]
    let E : Matrix (Fin 4) (Fin 4) ℂ :=
      Matrix.diagonal (fun i ↦ (d (e i) : ℂ))
    have hmatrix :
        Sp4.diagonalCongruence (fun i ↦ (d (e i) : ℂ)) (A.submatrix e e) =
          E * (A.submatrix e e) * E := by
      ext i j
      change (d (e i) : ℂ) * A (e i) (e j) * (d (e j) : ℂ) =
        (E * (A.submatrix e e) * E) i j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      rfl
    rw [hmatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero
      (mul_ne_zero
        (Finset.prod_ne_zero_iff.mpr fun i _ ↦ Units.ne_zero _)
        (hA.principal_four_ne e he))
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ Units.ne_zero _)

/-- Admissibility of a normalized matrix implies all defining `U5`
nonvanishing conditions. -/
theorem isU5_of_matrix5_isAdmissible (q : Coord5)
    (h : IsAdmissibleGram (matrix5 q)) : IsU5 q := by
  have hp (i : Fin 5) :
      pfaffian4 (principal4Of5 (matrix5 q) i) ≠ 0 := by
    have hdet := h.principal_four_ne i.succAbove Fin.succAbove_right_injective
    change (principal4Of5 (matrix5 q) i).det ≠ 0 at hdet
    have hskew : IsSkew (principal4Of5 (matrix5 q) i) := by
      intro a b
      exact h.skew (i.succAbove a) (i.succAbove b)
    rw [OrbitChain.det_skew_four_eq_pfaffian_sq _ hskew] at hdet
    exact fun hz ↦ hdet (by simp [hz])
  refine ⟨
    h.offDiagonal_ne 1 3 (by decide),
    h.offDiagonal_ne 1 4 (by decide),
    h.offDiagonal_ne 2 3 (by decide),
    h.offDiagonal_ne 2 4 (by decide),
    h.offDiagonal_ne 3 4 (by decide), ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hp 0
  · simpa using hp 1
  · simpa using hp 2
  · simpa using hp 3
  · simpa using hp 4

/-- Admissibility of a normalized six-by-six matrix implies the Pfaffian
hypersurface equation and every defining genericity condition of `U6`. -/
theorem isU6_of_matrix6_isAdmissible (q : Coord6)
    (h : IsAdmissibleGram (matrix6 q)) : IsU6 q := by
  have hbracket (i j k l : Fin 6)
      (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
      (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
      orderedBracket (matrix6 q) i j k l ≠ 0 := by
    let e : Fin 4 → Fin 6 := ![i, j, k, l]
    have he : Function.Injective e := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [e]
    have hdet := h.principal_four_ne e he
    have hskew : IsSkew ((matrix6 q).submatrix e e) := by
      intro a b
      exact h.skew (e a) (e b)
    rw [OrbitChain.det_skew_four_eq_pfaffian_sq _ hskew] at hdet
    change orderedBracket (matrix6 q) i j k l ^ 2 ≠ 0 at hdet
    exact fun hz ↦ hdet (by simp [hz])
  have hpi : pi6 q = 0 := by
    let e : Fin 4 → Fin 6 := fun i ↦ ⟨i, Nat.lt_trans i.2 (by omega)⟩
    have he : Function.Injective e := by
      intro i j hij
      apply Fin.ext
      simpa [e] using congrArg Fin.val hij
    obtain ⟨l, u, _hl, hu⟩ := h.exists_generic_realization e he
    have hpf : pfaffian6 (matrix6 q) = 0 := by
      rw [← hu]
      exact OrbitChain.pfaffian6_gram_eq_zero u.vec
    simpa using hpf
  refine ⟨
    h.offDiagonal_ne 1 3 (by decide),
    h.offDiagonal_ne 1 4 (by decide),
    h.offDiagonal_ne 1 5 (by decide),
    h.offDiagonal_ne 2 3 (by decide),
    h.offDiagonal_ne 2 4 (by decide),
    h.offDiagonal_ne 2 5 (by decide),
    h.offDiagonal_ne 3 4 (by decide),
    h.offDiagonal_ne 3 5 (by decide),
    h.offDiagonal_ne 4 5 (by decide), hpi, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [orderedBracket, matrix6, pf0123] using
      hbracket 0 1 2 3 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
  · simpa [orderedBracket, matrix6, pf0124] using
      hbracket 0 1 2 4 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
  · simpa [orderedBracket, matrix6, pf0125] using
      hbracket 0 1 2 5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
  · simpa [orderedBracket, matrix6, pf0134] using
      hbracket 0 1 3 4 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
  · simpa [orderedBracket, matrix6, pf0135] using
      hbracket 0 1 3 5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
  · simpa [orderedBracket, matrix6, pf0145] using
      hbracket 0 1 4 5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
  · simpa [orderedBracket, matrix6, pf0234] using
      hbracket 0 2 3 4 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
  · simpa [orderedBracket, matrix6, pf0235] using
      hbracket 0 2 3 5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
  · simpa [orderedBracket, matrix6, pf0245] using
      hbracket 0 2 4 5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
  · simpa [orderedBracket, matrix6, pf0345] using
      hbracket 0 3 4 5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
  · simpa [orderedBracket, matrix6, pf1234] using
      hbracket 1 2 3 4 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
  · simpa [orderedBracket, matrix6, pf1235] using
      hbracket 1 2 3 5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
  · simpa [orderedBracket, matrix6, pf1245] using
      hbracket 1 2 4 5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
  · simpa [orderedBracket, matrix6, pf1345] using
      hbracket 1 3 4 5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
  · simpa [orderedBracket, matrix6, pf2345] using
      hbracket 2 3 4 5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)

/-- The diagonal-congruence invariant of any admissible six-by-six Gram matrix
lies in the normalized Pfaffian chart. -/
theorem chi6_mem_of_isAdmissibleGram (A : Matrix (Fin 6) (Fin 6) ℂ)
    (hA : IsAdmissibleGram A) : IsU6 (chi6 A) := by
  let c := chi6 A
  obtain ⟨d, hd⟩ := exists_matrix6_chi6_diagonalCongruence
    A hA.skew hA.offDiagonal_ne
  exact isU6_of_matrix6_isAdmissible c
    (hd ▸ isAdmissibleGram_diagonalCongruence hA d)

/-- Reindexing a generic normalized six-point matrix again gives a point of
the normalized Pfaffian chart. -/
theorem chi6_reindex_mem (σ : Equiv.Perm (Fin 6)) (q : U6) :
    IsU6 (chi6 (reindexGram σ (matrix6 q.1))) :=
  chi6_mem_of_isAdmissibleGram _
    (isAdmissibleGram_reindex (OrbitChain.matrix6_isAdmissible q) σ)

/-- Taking the invariant five-point coordinate after deleting a row and column
from `matrix6` gives exactly the article's rational face map. -/
theorem chi5_deleteMatrix_matrix6 (q : U6) (i : Fin 6) :
    chi5 (deleteMatrix i (matrix6 q.1)) = (face5At i q).1 := by
  let B := deleteMatrix i (matrix6 q.1)
  have hBoff : ∀ a b : Fin 5, a ≠ b → B a b ≠ 0 := by
    intro a b hab
    exact (OrbitChain.matrix6_isAdmissible q).offDiagonal_ne _ _
      (Fin.succAbove_right_injective.ne hab)
  obtain ⟨d, hd⟩ := OrbitChain.exists_face5_diagonalCongruence q i
  calc
    chi5 B = chi5 (diagonalCongruence (fun a ↦ (d a : ℂ)) B) :=
      (chi5_diagonalCongruence B d hBoff).symm
    _ = chi5 (matrix5 (face5At i q).1) := congrArg chi5 hd.symm
    _ = (face5At i q).1 := chi5_matrix5 _

/-- The diagonal-congruence invariant of any admissible five-by-five Gram
matrix lies in the normalized chart. -/
theorem chi5_mem_of_isAdmissibleGram (A : Matrix (Fin 5) (Fin 5) ℂ)
    (hA : IsAdmissibleGram A) : IsU5 (chi5 A) := by
  let c := chi5 A
  obtain ⟨d, hd⟩ := exists_matrix5_chi5_diagonalCongruence A hA.skew
    hA.offDiagonal_ne
  exact isU5_of_matrix5_isAdmissible c
    (hd ▸ isAdmissibleGram_diagonalCongruence hA d)

/-- Reindexing a generic normalized five-point matrix again gives a point of
the normalized chart. -/
theorem chi5_reindex_mem (σ : Equiv.Perm (Fin 5)) (q : U5) :
    IsU5 (chi5 (reindexGram σ (matrix5 q.1))) := by
  let A := reindexGram σ (matrix5 q.1)
  let c := chi5 A
  have hA : IsAdmissibleGram A :=
    isAdmissibleGram_reindex (OrbitChain.matrix5_isAdmissible q) σ
  obtain ⟨d, hd⟩ := exists_matrix5_chi5_diagonalCongruence A hA.skew
    hA.offDiagonal_ne
  exact isU5_of_matrix5_isAdmissible c
    (hd ▸ isAdmissibleGram_diagonalCongruence hA d)

/-- The analogous chart-membership theorem in degree four. -/
theorem chi4_mem_of_isAdmissibleGram (A : Matrix (Fin 4) (Fin 4) ℂ)
    (hA : IsAdmissibleGram A) : IsU4 (chi4 A) := by
  let c := chi4 A
  obtain ⟨d, hd⟩ := OrbitChain.exists_matrix4_chi4_diagonalCongruence
    A hA.skew hA.offDiagonal_ne
  have hc : IsAdmissibleGram (matrix4 c) :=
    hd ▸ isAdmissibleGram_diagonalCongruence hA d
  exact ⟨hc.offDiagonal_ne 1 3 (by decide),
    hc.offDiagonal_ne 2 3 (by decide), by
      have hdet := hc.principal_four_ne id Function.injective_id
      simp only [Matrix.submatrix_id_id] at hdet
      rw [OrbitChain.det_skew_four_eq_pfaffian_sq _ hc.skew,
        pfaffian4_matrix4] at hdet
      change delta4 c ≠ 0
      exact fun hz ↦ hdet (by simp [hz])⟩

/-! ## Coordinates of arbitrary generic projective configurations -/

/-- Reindex the canonical lift of a projective configuration. -/
def permutedCanonicalLift {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : OrbitChain.GenericConfig n) :
    ProjectiveLift (OrbitChain.permuteGeneric σ x).1 where
  vec i := projectiveRepresentatives x.1 (σ i)
  ne_zero i := projectiveRepresentatives_ne_zero x.1 (σ i)
  projectivizes i := by
    change Projectivization.mk ℂ (projectiveRepresentatives x.1 (σ i)) _ =
      x.1 (σ i)
    exact (canonicalProjectiveLift x.1).projectivizes (σ i)

theorem gram_permutedCanonicalLift {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : OrbitChain.GenericConfig n) :
    gram (permutedCanonicalLift σ x).vec =
      reindexGram σ (projectiveGram x.1) := by
  rfl

/-- Apply a symplectic map to the canonical lift. -/
def smulCanonicalLift {n : ℕ} (g : SymplecticGroup)
    (x : OrbitChain.GenericConfig n) :
    ProjectiveLift (OrbitChain.smulGeneric g x).1 where
  vec i := g.1 (projectiveRepresentatives x.1 i)
  ne_zero i := by
    intro hzero
    apply projectiveRepresentatives_ne_zero x.1 i
    apply g.1.injective
    simpa using hzero
  projectivizes i := by
    change Projectivization.mk ℂ (g.1 (projectiveRepresentatives x.1 i)) _ =
      g.1 • x.1 i
    rw [← (canonicalProjectiveLift x.1).projectivizes i,
      Projectivization.smul_mk]
    rfl

theorem gram_smulCanonicalLift {n : ℕ} (g : SymplecticGroup)
    (x : OrbitChain.GenericConfig n) :
    gram (smulCanonicalLift g x).vec = projectiveGram x.1 := by
  ext i j
  exact SymplecticGroup.preserves g _ _

/-- Canonical representatives of a permuted projective tuple differ from the
literally permuted representatives only by nonzero diagonal scalars. -/
theorem projectiveGram_permute_diagonalCongruent {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (x : OrbitChain.GenericConfig n) :
    ∃ d : Fin n → ℂˣ,
      projectiveGram (OrbitChain.permuteGeneric σ x).1 =
        diagonalCongruence (fun i ↦ (d i : ℂ))
          (reindexGram σ (projectiveGram x.1)) := by
  obtain ⟨d, hd⟩ := (canonicalProjectiveLift
    (OrbitChain.permuteGeneric σ x).1).gram_diagonalCongruent
      (permutedCanonicalLift σ x)
  refine ⟨d, ?_⟩
  simpa [projectiveGram, canonicalProjectiveLift,
    gram_permutedCanonicalLift] using hd

/-- The same comparison for the symplectic action; preservation of the form
makes the second Gram matrix equal to the original one. -/
theorem projectiveGram_smul_diagonalCongruent {n : ℕ}
    (g : SymplecticGroup) (x : OrbitChain.GenericConfig n) :
    ∃ d : Fin n → ℂˣ,
      projectiveGram (OrbitChain.smulGeneric g x).1 =
        diagonalCongruence (fun i ↦ (d i : ℂ))
          (projectiveGram x.1) := by
  obtain ⟨d, hd⟩ := (canonicalProjectiveLift
    (OrbitChain.smulGeneric g x).1).gram_diagonalCongruent
      (smulCanonicalLift g x)
  refine ⟨d, ?_⟩
  simpa [projectiveGram, canonicalProjectiveLift,
    gram_smulCanonicalLift] using hd

/-- The normalized orbit coordinate of an arbitrary generic five-tuple. -/
def orbitCoord5 (x : OrbitChain.GenericConfig 5) : U5 :=
  ⟨chi5 (projectiveGram x.1),
    chi5_mem_of_isAdmissibleGram _
      (generic_projectiveGram_isAdmissible x.2 Fin.castSucc
        (Fin.castSucc_injective 4))⟩

/-- The normalized orbit coordinate of an arbitrary generic six-tuple. -/
def orbitCoord6 (x : OrbitChain.GenericConfig 6) : U6 :=
  ⟨chi6 (projectiveGram x.1),
    chi6_mem_of_isAdmissibleGram _
      (generic_projectiveGram_isAdmissible x.2
        (fun i ↦ ⟨i, Nat.lt_trans i.2 (by omega)⟩)
        (by
          intro i j hij
          apply Fin.ext
          simpa using congrArg Fin.val hij))⟩

/-- The normalized orbit coordinate of an arbitrary generic four-tuple. -/
def orbitCoord4 (x : OrbitChain.GenericConfig 4) : U4 :=
  ⟨chi4 (projectiveGram x.1),
    chi4_mem_of_isAdmissibleGram _
      (generic_projectiveGram_isAdmissible x.2 id Function.injective_id)⟩

@[simp]
theorem orbitCoord5_normalizedConfig5 (q : U5) :
    orbitCoord5 (OrbitChain.normalizedConfig5 q) = q := by
  apply Subtype.ext
  obtain ⟨d, hd⟩ :=
    ProjectiveLift.gram_diagonalCongruent
      (canonicalProjectiveLift (OrbitChain.normalizedConfig5 q).1)
      (OrbitChain.normalizedRealization5 q).lift
  have hd' : projectiveGram (OrbitChain.normalizedConfig5 q).1 =
      diagonalCongruence (fun i ↦ (d i : ℂ)) (matrix5 q.1) := by
    simpa [projectiveGram, canonicalProjectiveLift,
      (OrbitChain.normalizedRealization5 q).gram_eq] using hd
  change chi5 (projectiveGram (OrbitChain.normalizedConfig5 q).1) = q.1
  rw [hd', chi5_diagonalCongruence, chi5_matrix5]
  exact (OrbitChain.matrix5_isAdmissible q).offDiagonal_ne

@[simp]
theorem orbitCoord6_normalizedConfig6 (q : U6) :
    orbitCoord6 (OrbitChain.normalizedConfig6 q) = q := by
  apply Subtype.ext
  obtain ⟨d, hd⟩ :=
    ProjectiveLift.gram_diagonalCongruent
      (canonicalProjectiveLift (OrbitChain.normalizedConfig6 q).1)
      (OrbitChain.normalizedRealization6 q).lift
  have hd' : projectiveGram (OrbitChain.normalizedConfig6 q).1 =
      diagonalCongruence (fun i ↦ (d i : ℂ)) (matrix6 q.1) := by
    simpa [projectiveGram, canonicalProjectiveLift,
      (OrbitChain.normalizedRealization6 q).gram_eq] using hd
  change chi6 (projectiveGram (OrbitChain.normalizedConfig6 q).1) = q.1
  rw [hd', chi6_diagonalCongruence, chi6_matrix6]
  exact (OrbitChain.matrix6_isAdmissible q).offDiagonal_ne

@[simp]
theorem orbitCoord4_normalizedConfig4 (q : U4) :
    orbitCoord4 (OrbitChain.normalizedConfig4 q) = q := by
  apply Subtype.ext
  obtain ⟨d, hd⟩ :=
    ProjectiveLift.gram_diagonalCongruent
      (canonicalProjectiveLift (OrbitChain.normalizedConfig4 q).1)
      (OrbitChain.normalizedRealization4 q).lift
  have hd' : projectiveGram (OrbitChain.normalizedConfig4 q).1 =
      diagonalCongruence (fun i ↦ (d i : ℂ)) (matrix4 q.1) := by
    simpa [projectiveGram, canonicalProjectiveLift,
      (OrbitChain.normalizedRealization4 q).gram_eq] using hd
  change chi4 (projectiveGram (OrbitChain.normalizedConfig4 q).1) = q.1
  rw [hd', OrbitChain.chi4_diagonalCongruence, chi4_matrix4]
  · exact (OrbitChain.matrix4_isAdmissible q).offDiagonal_ne 1 2 (by decide)
  · exact (OrbitChain.matrix4_isAdmissible q).offDiagonal_ne 0 3 (by decide)

@[simp]
theorem orbitCoord5_smulGeneric (g : SymplecticGroup)
    (x : OrbitChain.GenericConfig 5) :
    orbitCoord5 (OrbitChain.smulGeneric g x) = orbitCoord5 x := by
  apply Subtype.ext
  obtain ⟨d, hd⟩ := projectiveGram_smul_diagonalCongruent g x
  change chi5 (projectiveGram (OrbitChain.smulGeneric g x).1) =
    chi5 (projectiveGram x.1)
  rw [hd, chi5_diagonalCongruence]
  exact (generic_projectiveGram_isAdmissible x.2 Fin.castSucc
    (Fin.castSucc_injective 4)).offDiagonal_ne

@[simp]
theorem orbitCoord6_smulGeneric (g : SymplecticGroup)
    (x : OrbitChain.GenericConfig 6) :
    orbitCoord6 (OrbitChain.smulGeneric g x) = orbitCoord6 x := by
  apply Subtype.ext
  obtain ⟨d, hd⟩ := projectiveGram_smul_diagonalCongruent g x
  change chi6 (projectiveGram (OrbitChain.smulGeneric g x).1) =
    chi6 (projectiveGram x.1)
  rw [hd, chi6_diagonalCongruence]
  exact (generic_projectiveGram_isAdmissible x.2
    (fun i ↦ ⟨i, Nat.lt_trans i.2 (by omega)⟩)
    (by
      intro i j hij
      apply Fin.ext
      simpa using congrArg Fin.val hij)).offDiagonal_ne

@[simp]
theorem orbitCoord4_smulGeneric (g : SymplecticGroup)
    (x : OrbitChain.GenericConfig 4) :
    orbitCoord4 (OrbitChain.smulGeneric g x) = orbitCoord4 x := by
  apply Subtype.ext
  obtain ⟨d, hd⟩ := projectiveGram_smul_diagonalCongruent g x
  change chi4 (projectiveGram (OrbitChain.smulGeneric g x).1) =
    chi4 (projectiveGram x.1)
  rw [hd, OrbitChain.chi4_diagonalCongruence]
  · exact x.2.pairwise_transverse 1 2 (by decide)
  · exact x.2.pairwise_transverse 0 3 (by decide)

/-- Every generic five-configuration is in the symplectic orbit of the chosen
normalized realization of its coordinate. -/
theorem exists_smul_normalizedConfig5_orbitCoord5
    (x : OrbitChain.GenericConfig 5) :
    ∃ g : SymplecticGroup,
      OrbitChain.smulGeneric g
        (OrbitChain.normalizedConfig5 (orbitCoord5 x)) = x := by
  let A := projectiveGram x.1
  have hA : IsAdmissibleGram A :=
    generic_projectiveGram_isAdmissible x.2 Fin.castSucc
      (Fin.castSucc_injective 4)
  obtain ⟨d, hd⟩ := exists_matrix5_chi5_diagonalCongruence
    A hA.skew hA.offDiagonal_ne
  obtain ⟨g, hg⟩ :=
    OrbitChain.exists_symplectic_smul_of_lift_gram_diagonalCongruent
      (OrbitChain.normalizedRealization5 (orbitCoord5 x)).config x.1
      (OrbitChain.normalizedRealization5 (orbitCoord5 x)).generic x.2
      (OrbitChain.normalizedRealization5 (orbitCoord5 x)).lift
      (canonicalProjectiveLift x.1)
      Fin.castSucc (Fin.castSucc_injective 4) d (by
        rw [(OrbitChain.normalizedRealization5 (orbitCoord5 x)).gram_eq]
        exact hd)
  exact ⟨g, Subtype.ext hg⟩

/-- Every generic four-configuration is in the orbit of the chosen normalized
realization of its coordinate. -/
theorem exists_smul_normalizedConfig4_orbitCoord4
    (x : OrbitChain.GenericConfig 4) :
    ∃ g : SymplecticGroup,
      OrbitChain.smulGeneric g
        (OrbitChain.normalizedConfig4 (orbitCoord4 x)) = x := by
  let A := projectiveGram x.1
  have hA : IsAdmissibleGram A :=
    generic_projectiveGram_isAdmissible x.2 id Function.injective_id
  obtain ⟨d, hd⟩ := OrbitChain.exists_matrix4_chi4_diagonalCongruence
    A hA.skew hA.offDiagonal_ne
  obtain ⟨g, hg⟩ :=
    OrbitChain.exists_symplectic_smul_of_lift_gram_diagonalCongruent
      (OrbitChain.normalizedRealization4 (orbitCoord4 x)).config x.1
      (OrbitChain.normalizedRealization4 (orbitCoord4 x)).generic x.2
      (OrbitChain.normalizedRealization4 (orbitCoord4 x)).lift
      (canonicalProjectiveLift x.1) id Function.injective_id d (by
        rw [(OrbitChain.normalizedRealization4 (orbitCoord4 x)).gram_eq]
        exact hd)
  exact ⟨g, Subtype.ext hg⟩

/-- Every generic six-configuration is in the symplectic orbit of the chosen
normalized realization of its coordinate. -/
theorem exists_smul_normalizedConfig6_orbitCoord6
    (x : OrbitChain.GenericConfig 6) :
    ∃ g : SymplecticGroup,
      OrbitChain.smulGeneric g
        (OrbitChain.normalizedConfig6 (orbitCoord6 x)) = x := by
  let A := projectiveGram x.1
  have hA : IsAdmissibleGram A :=
    generic_projectiveGram_isAdmissible x.2
      (fun i ↦ ⟨i, Nat.lt_trans i.2 (by omega)⟩)
      (by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij)
  obtain ⟨d, hd⟩ := exists_matrix6_chi6_diagonalCongruence
    A hA.skew hA.offDiagonal_ne
  obtain ⟨g, hg⟩ :=
    OrbitChain.exists_symplectic_smul_of_lift_gram_diagonalCongruent
      (OrbitChain.normalizedRealization6 (orbitCoord6 x)).config x.1
      (OrbitChain.normalizedRealization6 (orbitCoord6 x)).generic x.2
      (OrbitChain.normalizedRealization6 (orbitCoord6 x)).lift
      (canonicalProjectiveLift x.1)
      (fun i ↦ ⟨i, Nat.lt_trans i.2 (by omega)⟩)
      (by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij)
      d (by
        rw [(OrbitChain.normalizedRealization6 (orbitCoord6 x)).gram_eq]
        exact hd)
  exact ⟨g, Subtype.ext hg⟩

/-- Two generic five-configurations have the same normalized coordinate exactly
when they lie in the same symplectic orbit. -/
theorem orbitCoord5_eq_iff_exists_smul
    (x y : OrbitChain.GenericConfig 5) :
    orbitCoord5 x = orbitCoord5 y ↔
      ∃ g : SymplecticGroup, OrbitChain.smulGeneric g x = y := by
  constructor
  · intro hxy
    obtain ⟨gx, hgx⟩ := exists_smul_normalizedConfig5_orbitCoord5 x
    obtain ⟨gy, hgy⟩ := exists_smul_normalizedConfig5_orbitCoord5 y
    refine ⟨gy * gx⁻¹, ?_⟩
    rw [OrbitChain.smulGeneric_mul]
    have hgxi : OrbitChain.smulGeneric gx⁻¹ x =
        OrbitChain.normalizedConfig5 (orbitCoord5 x) := by
      rw [← hgx, ← OrbitChain.smulGeneric_mul]
      simp
    rw [hgxi, hxy, hgy]
  · rintro ⟨g, rfl⟩
    exact (orbitCoord5_smulGeneric g x).symm

/-- The corresponding orbit classification for four configurations. -/
theorem orbitCoord4_eq_iff_exists_smul
    (x y : OrbitChain.GenericConfig 4) :
    orbitCoord4 x = orbitCoord4 y ↔
      ∃ g : SymplecticGroup, OrbitChain.smulGeneric g x = y := by
  constructor
  · intro hxy
    obtain ⟨gx, hgx⟩ := exists_smul_normalizedConfig4_orbitCoord4 x
    obtain ⟨gy, hgy⟩ := exists_smul_normalizedConfig4_orbitCoord4 y
    refine ⟨gy * gx⁻¹, ?_⟩
    rw [OrbitChain.smulGeneric_mul]
    have hgxi : OrbitChain.smulGeneric gx⁻¹ x =
        OrbitChain.normalizedConfig4 (orbitCoord4 x) := by
      rw [← hgx, ← OrbitChain.smulGeneric_mul]
      simp
    rw [hgxi, hxy, hgy]
  · rintro ⟨g, rfl⟩
    exact (orbitCoord4_smulGeneric g x).symm

/-- The corresponding orbit classification for six configurations. -/
theorem orbitCoord6_eq_iff_exists_smul
    (x y : OrbitChain.GenericConfig 6) :
    orbitCoord6 x = orbitCoord6 y ↔
      ∃ g : SymplecticGroup, OrbitChain.smulGeneric g x = y := by
  constructor
  · intro hxy
    obtain ⟨gx, hgx⟩ := exists_smul_normalizedConfig6_orbitCoord6 x
    obtain ⟨gy, hgy⟩ := exists_smul_normalizedConfig6_orbitCoord6 y
    refine ⟨gy * gx⁻¹, ?_⟩
    rw [OrbitChain.smulGeneric_mul]
    have hgxi : OrbitChain.smulGeneric gx⁻¹ x =
        OrbitChain.normalizedConfig6 (orbitCoord6 x) := by
      rw [← hgx, ← OrbitChain.smulGeneric_mul]
      simp
    rw [hgxi, hxy, hgy]
  · rintro ⟨g, rfl⟩
    exact (orbitCoord6_smulGeneric g x).symm

/-- Delete one entry from the canonical lift. -/
def deletedCanonicalLift {n : ℕ} (i : Fin (n + 1))
    (x : OrbitChain.GenericConfig (n + 1)) :
    ProjectiveLift (OrbitChain.face i x).1 where
  vec k := projectiveRepresentatives x.1 (i.succAbove k)
  ne_zero k := projectiveRepresentatives_ne_zero x.1 (i.succAbove k)
  projectivizes k := by
    change Projectivization.mk ℂ
      (projectiveRepresentatives x.1 (i.succAbove k)) _ =
        x.1 (i.succAbove k)
    exact (canonicalProjectiveLift x.1).projectivizes (i.succAbove k)

theorem gram_deletedCanonicalLift {n : ℕ} (i : Fin (n + 1))
    (x : OrbitChain.GenericConfig (n + 1)) :
    gram (deletedCanonicalLift i x).vec =
      deleteMatrix i (projectiveGram x.1) := by
  rfl

theorem projectiveGram_face_diagonalCongruent {n : ℕ}
    (i : Fin (n + 1)) (x : OrbitChain.GenericConfig (n + 1)) :
    ∃ d : Fin n → ℂˣ,
      projectiveGram (OrbitChain.face i x).1 =
        diagonalCongruence (fun k ↦ (d k : ℂ))
          (deleteMatrix i (projectiveGram x.1)) := by
  obtain ⟨d, hd⟩ := (canonicalProjectiveLift
    (OrbitChain.face i x).1).gram_diagonalCongruent
      (deletedCanonicalLift i x)
  refine ⟨d, ?_⟩
  simpa [projectiveGram, canonicalProjectiveLift,
    gram_deletedCanonicalLift] using hd

/-- Normalized coordinates commute with deleting a vertex. -/
theorem orbitCoord4_face (i : Fin 5) (x : OrbitChain.GenericConfig 5) :
    orbitCoord4 (OrbitChain.face i x) = face4At i (orbitCoord5 x) := by
  apply Subtype.ext
  let A := projectiveGram x.1
  let B := deleteMatrix i A
  have hA : IsAdmissibleGram A :=
    generic_projectiveGram_isAdmissible x.2 Fin.castSucc
      (Fin.castSucc_injective 4)
  have hBoff : ∀ a b : Fin 4, a ≠ b → B a b ≠ 0 := by
    intro a b hab
    exact hA.offDiagonal_ne _ _ (Fin.succAbove_right_injective.ne hab)
  obtain ⟨d, hd⟩ := projectiveGram_face_diagonalCongruent i x
  obtain ⟨e, he⟩ := exists_matrix5_chi5_diagonalCongruence
    A hA.skew hA.offDiagonal_ne
  change chi4 (projectiveGram (OrbitChain.face i x).1) =
    (face4At i (orbitCoord5 x)).1
  rw [hd, OrbitChain.chi4_diagonalCongruence B d
    (hBoff 1 2 (by decide)) (hBoff 0 3 (by decide))]
  rw [← chi4_deleteMatrix_matrix5 (orbitCoord5 x) i]
  change chi4 B = chi4 (deleteMatrix i (matrix5 (chi5 A)))
  rw [he, deleteMatrix_diagonalCongruence,
    OrbitChain.chi4_diagonalCongruence B (fun a ↦ e (i.succAbove a))
      (hBoff 1 2 (by decide)) (hBoff 0 3 (by decide))]

/-- Six-to-five normalized coordinates commute with deleting a vertex. -/
theorem orbitCoord5_face (i : Fin 6) (x : OrbitChain.GenericConfig 6) :
    orbitCoord5 (OrbitChain.face i x) = face5At i (orbitCoord6 x) := by
  apply Subtype.ext
  let A := projectiveGram x.1
  let B := deleteMatrix i A
  have hA : IsAdmissibleGram A :=
    generic_projectiveGram_isAdmissible x.2
      (fun j ↦ ⟨j, Nat.lt_trans j.2 (by omega)⟩)
      (by
        intro j k hjk
        apply Fin.ext
        simpa using congrArg Fin.val hjk)
  have hBoff : ∀ a b : Fin 5, a ≠ b → B a b ≠ 0 := by
    intro a b hab
    exact hA.offDiagonal_ne _ _ (Fin.succAbove_right_injective.ne hab)
  obtain ⟨d, hd⟩ := projectiveGram_face_diagonalCongruent i x
  obtain ⟨e, he⟩ := exists_matrix6_chi6_diagonalCongruence
    A hA.skew hA.offDiagonal_ne
  change chi5 (projectiveGram (OrbitChain.face i x).1) =
    (face5At i (orbitCoord6 x)).1
  rw [hd, chi5_diagonalCongruence B d hBoff]
  rw [← chi5_deleteMatrix_matrix6 (orbitCoord6 x) i]
  change chi5 B = chi5 (deleteMatrix i (matrix6 (chi6 A)))
  rw [he, deleteMatrix_diagonalCongruence,
    chi5_diagonalCongruence B (fun a ↦ e (i.succAbove a)) hBoff]

 /-- The normalized six-point coordinate obtained after a vertex permutation. -/
def permute6 (σ : Equiv.Perm (Fin 6)) (q : U6) : U6 :=
  ⟨chi6 (reindexGram σ (matrix6 q.1)), chi6_reindex_mem σ q⟩

@[simp]
theorem permute6_val (σ : Equiv.Perm (Fin 6)) (q : U6) :
    (permute6 σ q).1 = chi6 (reindexGram σ (matrix6 q.1)) := rfl

/-- The normalized matrix representing a permuted six-point coordinate is
diagonally congruent to the reindexed original matrix. -/
theorem exists_matrix6_permute6_diagonalCongruence
    (σ : Equiv.Perm (Fin 6)) (q : U6) :
    ∃ d : Fin 6 → ℂˣ,
      matrix6 (permute6 σ q).1 =
        diagonalCongruence (fun i ↦ (d i : ℂ))
          (reindexGram σ (matrix6 q.1)) := by
  exact exists_matrix6_chi6_diagonalCongruence _
    (isAdmissibleGram_reindex (OrbitChain.matrix6_isAdmissible q) σ).skew
    (isAdmissibleGram_reindex
      (OrbitChain.matrix6_isAdmissible q) σ).offDiagonal_ne

@[simp]
theorem permute6_one (q : U6) : permute6 1 q = q := by
  apply Subtype.ext
  exact chi6_matrix6 q.1

/-- The maps `permute6` form the same right action as matrix reindexing. -/
theorem permute6_mul (σ τ : Equiv.Perm (Fin 6)) (q : U6) :
    permute6 τ (permute6 σ q) = permute6 (σ * τ) q := by
  apply Subtype.ext
  obtain ⟨d, hd⟩ := exists_matrix6_permute6_diagonalCongruence σ q
  change chi6 (reindexGram τ (matrix6 (permute6 σ q).1)) =
    chi6 (reindexGram (σ * τ) (matrix6 q.1))
  rw [hd, reindexGram_diagonalCongruence]
  let d' : Fin 6 → ℂˣ := fun i ↦ d (τ i)
  have hoff : ∀ i j, i ≠ j →
      reindexGram τ (reindexGram σ (matrix6 q.1)) i j ≠ 0 := by
    intro i j hij
    exact (OrbitChain.matrix6_isAdmissible q).offDiagonal_ne _ _
      (σ.injective.ne (τ.injective.ne hij))
  rw [show (fun i ↦ ((d (τ i) : ℂ))) = (fun i ↦ (d' i : ℂ)) by rfl,
    chi6_diagonalCongruence _ d' hoff]
  rw [reindexGram_mul]

/-- The normalized five-point coordinate obtained after a vertex permutation. -/
def permute5 (σ : Equiv.Perm (Fin 5)) (q : U5) : U5 :=
  ⟨chi5 (reindexGram σ (matrix5 q.1)), chi5_reindex_mem σ q⟩

@[simp]
theorem permute5_val (σ : Equiv.Perm (Fin 5)) (q : U5) :
    (permute5 σ q).1 = chi5 (reindexGram σ (matrix5 q.1)) := rfl

/-- The normalized matrix representing a permuted five-point coordinate is
diagonally congruent to the reindexed original matrix. -/
theorem exists_matrix5_permute5_diagonalCongruence
    (σ : Equiv.Perm (Fin 5)) (q : U5) :
    ∃ d : Fin 5 → ℂˣ,
      matrix5 (permute5 σ q).1 =
        Sp4.diagonalCongruence (fun i ↦ (d i : ℂ))
          (reindexGram σ (matrix5 q.1)) := by
  exact exists_matrix5_chi5_diagonalCongruence _
    (isAdmissibleGram_reindex (OrbitChain.matrix5_isAdmissible q) σ).skew
    (isAdmissibleGram_reindex (OrbitChain.matrix5_isAdmissible q) σ).offDiagonal_ne

/-- The normalized affine cocycle is alternating under every vertex
permutation.  This follows from the original 120-term definition, together
with invariance under the diagonal renormalization of Gram lifts. -/
theorem reducedR_permute5 (σ : Equiv.Perm (Fin 5)) (q : U5) :
    reducedR (matrix5 (permute5 σ q).1) =
      permSign ℂ σ * reducedR (matrix5 q.1) := by
  rw [← rawAlternationR_eq_reducedR (permute5 σ q),
    ← rawAlternationR_eq_reducedR q]
  obtain ⟨d, hd⟩ := exists_matrix5_permute5_diagonalCongruence σ q
  rw [hd, rawAlternationR_diagonalCongruence,
    rawAlternationR_reindexGram]

@[simp]
theorem permute5_one (q : U5) : permute5 1 q = q := by
  apply Subtype.ext
  exact chi5_matrix5 q.1

/-- The maps `permute5` form a right action: first `σ`, then `τ`, is
reindexing by `σ * τ`. -/
theorem permute5_mul (σ τ : Equiv.Perm (Fin 5)) (q : U5) :
    permute5 τ (permute5 σ q) = permute5 (σ * τ) q := by
  apply Subtype.ext
  obtain ⟨d, hd⟩ := exists_matrix5_permute5_diagonalCongruence σ q
  change chi5 (reindexGram τ (matrix5 (permute5 σ q).1)) =
    chi5 (reindexGram (σ * τ) (matrix5 q.1))
  rw [hd, reindexGram_diagonalCongruence]
  let d' : Fin 5 → ℂˣ := fun i ↦ d (τ i)
  have hoff : ∀ i j, i ≠ j →
      reindexGram τ (reindexGram σ (matrix5 q.1)) i j ≠ 0 := by
    intro i j hij
    exact (OrbitChain.matrix5_isAdmissible q).offDiagonal_ne _ _
      (σ.injective.ne (τ.injective.ne hij))
  rw [show (fun i ↦ ((d (τ i) : ℂ))) = (fun i ↦ (d' i : ℂ)) by rfl,
    chi5_diagonalCongruence _ d' hoff]
  rw [reindexGram_mul]

/-- Reindexing a four-point matrix gives a valid normalized coordinate. -/
theorem chi4_reindex_mem (σ : Equiv.Perm (Fin 4)) (q : U4) :
    IsU4 (chi4 (reindexGram σ (matrix4 q.1))) := by
  let A := reindexGram σ (matrix4 q.1)
  let c := chi4 A
  have hA : IsAdmissibleGram A :=
    isAdmissibleGram_reindex (OrbitChain.matrix4_isAdmissible q) σ
  obtain ⟨d, hd⟩ := OrbitChain.exists_matrix4_chi4_diagonalCongruence A hA.skew
    hA.offDiagonal_ne
  have hc : IsAdmissibleGram (matrix4 c) :=
    hd ▸ isAdmissibleGram_diagonalCongruence hA d
  exact ⟨hc.offDiagonal_ne 1 3 (by decide),
    hc.offDiagonal_ne 2 3 (by decide), by
      have hdet := hc.principal_four_ne id Function.injective_id
      simp only [Matrix.submatrix_id_id] at hdet
      rw [OrbitChain.det_skew_four_eq_pfaffian_sq _ hc.skew,
        pfaffian4_matrix4] at hdet
      change delta4 c ≠ 0
      exact fun hz ↦ hdet (by simp [hz])⟩

/-- The corresponding general four-point permutation map. -/
def permute4 (σ : Equiv.Perm (Fin 4)) (q : U4) : U4 :=
  ⟨chi4 (reindexGram σ (matrix4 q.1)), chi4_reindex_mem σ q⟩

@[simp]
theorem permute4_val (σ : Equiv.Perm (Fin 4)) (q : U4) :
    (permute4 σ q).1 = chi4 (reindexGram σ (matrix4 q.1)) := rfl

/-- The analogous normalized-matrix certificate in degree four. -/
theorem exists_matrix4_permute4_diagonalCongruence
    (σ : Equiv.Perm (Fin 4)) (q : U4) :
    ∃ d : Fin 4 → ℂˣ,
      matrix4 (permute4 σ q).1 =
        Sp4.diagonalCongruence (fun i ↦ (d i : ℂ))
          (reindexGram σ (matrix4 q.1)) := by
  exact OrbitChain.exists_matrix4_chi4_diagonalCongruence _
    (isAdmissibleGram_reindex (OrbitChain.matrix4_isAdmissible q) σ).skew
    (isAdmissibleGram_reindex (OrbitChain.matrix4_isAdmissible q) σ).offDiagonal_ne

@[simp]
theorem permute4_one (q : U4) : permute4 1 q = q := by
  apply Subtype.ext
  apply Coord4.ext <;> simp [permute4, reindexGram, chi4, matrix4]

/-- The four-point maps obey the same right-action convention. -/
theorem permute4_mul (σ τ : Equiv.Perm (Fin 4)) (q : U4) :
    permute4 τ (permute4 σ q) = permute4 (σ * τ) q := by
  apply Subtype.ext
  obtain ⟨d, hd⟩ := exists_matrix4_permute4_diagonalCongruence σ q
  change chi4 (reindexGram τ (matrix4 (permute4 σ q).1)) =
    chi4 (reindexGram (σ * τ) (matrix4 q.1))
  rw [hd, reindexGram_diagonalCongruence]
  let d' : Fin 4 → ℂˣ := fun i ↦ d (τ i)
  have hoff : ∀ i j, i ≠ j →
      reindexGram τ (reindexGram σ (matrix4 q.1)) i j ≠ 0 := by
    intro i j hij
    exact (OrbitChain.matrix4_isAdmissible q).offDiagonal_ne _ _
      (σ.injective.ne (τ.injective.ne hij))
  rw [show (fun i ↦ ((d (τ i) : ℂ))) = (fun i ↦ (d' i : ℂ)) by rfl,
    OrbitChain.chi4_diagonalCongruence _ d'
      (hoff 1 2 (by decide)) (hoff 0 3 (by decide))]
  rw [reindexGram_mul]

/-- Vertex permutation covariance of the six-point orbit coordinate. -/
theorem orbitCoord6_permuteGeneric (σ : Equiv.Perm (Fin 6))
    (x : OrbitChain.GenericConfig 6) :
    orbitCoord6 (OrbitChain.permuteGeneric σ x) =
      permute6 σ (orbitCoord6 x) := by
  apply Subtype.ext
  let A := projectiveGram x.1
  have hA : IsAdmissibleGram A :=
    generic_projectiveGram_isAdmissible x.2
      (fun i ↦ ⟨i, Nat.lt_trans i.2 (by omega)⟩)
      (by
        intro i j hij
        apply Fin.ext
        simpa using congrArg Fin.val hij)
  have hAσ : IsAdmissibleGram (reindexGram σ A) :=
    isAdmissibleGram_reindex hA σ
  obtain ⟨d, hd⟩ := projectiveGram_permute_diagonalCongruent σ x
  obtain ⟨e, he⟩ := exists_matrix6_chi6_diagonalCongruence
    A hA.skew hA.offDiagonal_ne
  change chi6 (projectiveGram (OrbitChain.permuteGeneric σ x).1) =
    chi6 (reindexGram σ (matrix6 (chi6 A)))
  rw [hd, chi6_diagonalCongruence _ d hAσ.offDiagonal_ne]
  rw [he, reindexGram_diagonalCongruence,
    chi6_diagonalCongruence _ (fun i ↦ e (σ i)) hAσ.offDiagonal_ne]

/-- Vertex permutation covariance of the five-point orbit coordinate. -/
theorem orbitCoord5_permuteGeneric (σ : Equiv.Perm (Fin 5))
    (x : OrbitChain.GenericConfig 5) :
    orbitCoord5 (OrbitChain.permuteGeneric σ x) =
      permute5 σ (orbitCoord5 x) := by
  apply Subtype.ext
  let A := projectiveGram x.1
  have hA : IsAdmissibleGram A :=
    generic_projectiveGram_isAdmissible x.2 Fin.castSucc
      (Fin.castSucc_injective 4)
  have hAσ : IsAdmissibleGram (reindexGram σ A) :=
    isAdmissibleGram_reindex hA σ
  obtain ⟨d, hd⟩ := projectiveGram_permute_diagonalCongruent σ x
  obtain ⟨e, he⟩ := exists_matrix5_chi5_diagonalCongruence
    A hA.skew hA.offDiagonal_ne
  change chi5 (projectiveGram (OrbitChain.permuteGeneric σ x).1) =
    chi5 (reindexGram σ (matrix5 (chi5 A)))
  rw [hd, chi5_diagonalCongruence _ d hAσ.offDiagonal_ne]
  rw [he, reindexGram_diagonalCongruence,
    chi5_diagonalCongruence _ (fun i ↦ e (σ i)) hAσ.offDiagonal_ne]

/-- Vertex permutation covariance in degree four. -/
theorem orbitCoord4_permuteGeneric (σ : Equiv.Perm (Fin 4))
    (x : OrbitChain.GenericConfig 4) :
    orbitCoord4 (OrbitChain.permuteGeneric σ x) =
      permute4 σ (orbitCoord4 x) := by
  apply Subtype.ext
  let A := projectiveGram x.1
  have hA : IsAdmissibleGram A :=
    generic_projectiveGram_isAdmissible x.2 id Function.injective_id
  have hAσ : IsAdmissibleGram (reindexGram σ A) :=
    isAdmissibleGram_reindex hA σ
  obtain ⟨d, hd⟩ := projectiveGram_permute_diagonalCongruent σ x
  obtain ⟨e, he⟩ := OrbitChain.exists_matrix4_chi4_diagonalCongruence
    A hA.skew hA.offDiagonal_ne
  change chi4 (projectiveGram (OrbitChain.permuteGeneric σ x).1) =
    chi4 (reindexGram σ (matrix4 (chi4 A)))
  rw [hd, OrbitChain.chi4_diagonalCongruence _ d
    (hAσ.offDiagonal_ne 1 2 (by decide))
    (hAσ.offDiagonal_ne 0 3 (by decide))]
  rw [he, reindexGram_diagonalCongruence,
    OrbitChain.chi4_diagonalCongruence _ (fun i ↦ e (σ i))
      (hAσ.offDiagonal_ne 1 2 (by decide))
      (hAσ.offDiagonal_ne 0 3 (by decide))]

/-- Permuting vertices and then deleting vertex `i` agrees with first deleting
`σ i` and applying the induced permutation to the remaining four vertices.
This is the coordinate form of the simplicial face--permutation identity. -/
theorem face4At_permute5 (σ : Equiv.Perm (Fin 5)) (i : Fin 5) (q : U5) :
    face4At i (permute5 σ q) =
      permute4 (deletePerm σ i) (face4At (σ i) q) := by
  apply Subtype.ext
  let A := matrix5 q.1
  let Aσ := reindexGram σ A
  let δ := deletePerm σ i
  obtain ⟨d, hd⟩ := exists_matrix5_permute5_diagonalCongruence σ q
  let di : Fin 4 → ℂˣ := fun a ↦ d (i.succAbove a)
  have hAσdel : ∀ a b : Fin 4, a ≠ b →
      deleteMatrix i Aσ a b ≠ 0 := by
    intro a b hab
    exact (OrbitChain.matrix5_isAdmissible q).offDiagonal_ne _ _
      (σ.injective.ne (Fin.succAbove_right_injective.ne hab))
  obtain ⟨e, he⟩ := OrbitChain.exists_face4_diagonalCongruence q (σ i)
  let eδ : Fin 4 → ℂˣ := fun a ↦ e (δ a)
  have hBoff : ∀ a b : Fin 4, a ≠ b →
      reindexGram δ (deleteMatrix (σ i) A) a b ≠ 0 := by
    intro a b hab
    exact (OrbitChain.matrix5_isAdmissible q).offDiagonal_ne _ _
      (Fin.succAbove_right_injective.ne (δ.injective.ne hab))
  calc
    (face4At i (permute5 σ q)).1 =
        chi4 (deleteMatrix i (matrix5 (permute5 σ q).1)) :=
      (OrbitChain.chi4_deleteMatrix_matrix5 (permute5 σ q) i).symm
    _ = chi4 (deleteMatrix i
        (Sp4.diagonalCongruence (fun a ↦ (d a : ℂ)) Aσ)) := by rw [hd]
    _ = chi4 (Sp4.diagonalCongruence (fun a ↦ (di a : ℂ))
        (deleteMatrix i Aσ)) := by rfl
    _ = chi4 (deleteMatrix i Aσ) :=
      OrbitChain.chi4_diagonalCongruence _ di
        (hAσdel 1 2 (by decide)) (hAσdel 0 3 (by decide))
    _ = chi4 (reindexGram δ (deleteMatrix (σ i) A)) := by
      rw [deleteMatrix_reindexGram]
    _ = chi4 (reindexGram δ (matrix4 (face4At (σ i) q).1)) := by
      rw [he, reindexGram_diagonalCongruence]
      exact (OrbitChain.chi4_diagonalCongruence _ eδ
        (hBoff 1 2 (by decide)) (hBoff 0 3 (by decide))).symm
    _ = (permute4 δ (face4At (σ i) q)).1 := rfl

/-- The six-point permutation maps and the rational five-point faces satisfy
the simplicial face--permutation identity. -/
theorem face5At_permute6 (σ : Equiv.Perm (Fin 6)) (i : Fin 6) (q : U6) :
    face5At i (permute6 σ q) =
      permute5 (deletePerm σ i) (face5At (σ i) q) := by
  let x := OrbitChain.normalizedConfig6 q
  calc
    face5At i (permute6 σ q) =
        face5At i (orbitCoord6 (OrbitChain.permuteGeneric σ x)) := by
      rw [orbitCoord6_permuteGeneric, orbitCoord6_normalizedConfig6]
    _ = orbitCoord5
        (OrbitChain.face i (OrbitChain.permuteGeneric σ x)) :=
      (orbitCoord5_face i _).symm
    _ = orbitCoord5
        (OrbitChain.permuteGeneric (deletePerm σ i)
          (OrbitChain.face (σ i) x)) := by
      rw [OrbitChain.face_permuteGeneric]
    _ = permute5 (deletePerm σ i)
        (orbitCoord5 (OrbitChain.face (σ i) x)) :=
      orbitCoord5_permuteGeneric _ _
    _ = permute5 (deletePerm σ i)
        (face5At (σ i) (orbitCoord6 x)) := by
      rw [orbitCoord5_face]
    _ = permute5 (deletePerm σ i) (face5At (σ i) q) := by
      rw [orbitCoord6_normalizedConfig6]

/-! ## Topological and measurable structure -/

theorem continuous_coord4_mk {X : Type*} [TopologicalSpace X]
    {f g : X → ℂ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x ↦ Coord4.mk (f x) (g x) := by
  change Continuous fun x ↦ coord4LinearIsometryEquivProd.symm (f x, g x)
  exact coord4LinearIsometryEquivProd.toContinuousLinearEquiv.symm.continuous.comp
    (hf.prodMk hg)

theorem continuous_coord5_mk {X : Type*} [TopologicalSpace X]
    {f₀ f₁ f₂ f₃ f₄ : X → ℂ}
    (h₀ : Continuous f₀) (h₁ : Continuous f₁) (h₂ : Continuous f₂)
    (h₃ : Continuous f₃) (h₄ : Continuous f₄) :
    Continuous fun x ↦ Coord5.mk (f₀ x) (f₁ x) (f₂ x) (f₃ x) (f₄ x) := by
  change Continuous fun x ↦ coord5LinearIsometryEquivFun.symm
    (![f₀ x, f₁ x, f₂ x, f₃ x, f₄ x])
  apply coord5LinearIsometryEquivFun.toContinuousLinearEquiv.symm.continuous.comp
  apply continuous_pi
  intro k
  fin_cases k <;> simpa

theorem continuous_matrix4_entry (i j : Fin 4) :
    Continuous fun q : U4 ↦ matrix4 q.1 i j := by
  have h : Continuous fun q : Coord4 ↦ matrix4 q i j := by
    fin_cases i <;> fin_cases j <;> simp [matrix4] <;> fun_prop
  exact (h.comp continuous_subtype_val).congr fun _ ↦ rfl

theorem continuous_matrix5_entry (i j : Fin 5) :
    Continuous fun q : U5 ↦ matrix5 q.1 i j := by
  have h : Continuous fun q : Coord5 ↦ matrix5 q i j := by
    fin_cases i <;> fin_cases j <;> simp [matrix5] <;> fun_prop
  exact (h.comp continuous_subtype_val).congr fun _ ↦ rfl

theorem continuous_principalPf5_matrix5 (k : Fin 5) :
    Continuous fun q : U5 ↦ principalPf5 (matrix5 q.1) k := by
  fin_cases k
  · exact (continuous_p0.comp continuous_subtype_val).congr
      (fun q ↦ by simp [Function.comp_def])
  · exact (continuous_p1.comp continuous_subtype_val).congr
      (fun q ↦ by simp [Function.comp_def])
  · exact (continuous_p2.comp continuous_subtype_val).congr
      (fun q ↦ by simp [Function.comp_def])
  · exact (continuous_p3.comp continuous_subtype_val).congr
      (fun q ↦ by simp [Function.comp_def])
  · exact (continuous_p4.comp continuous_subtype_val).congr
      (fun q ↦ by simp [Function.comp_def])

theorem principalPf5_matrix5_ne_zero (q : U5) (k : Fin 5) :
    principalPf5 (matrix5 q.1) k ≠ 0 := by
  fin_cases k
  · simpa using q.2.p0_ne
  · simpa using q.2.p1_ne
  · simpa using q.2.p2_ne
  · simpa using q.2.p3_ne
  · simpa using q.2.p4_ne

theorem continuous_complementaryPfProduct_matrix5
    (k i j : Fin 5) :
    Continuous fun q : U5 ↦
      complementaryPfProduct (matrix5 q.1) k i j := by
  apply continuous_finset_prod
  intro s _hs
  by_cases h : s = k ∨ s = i ∨ s = j
  · simpa [complementaryPfProduct, h] using
      (continuous_const : Continuous fun _q : U5 ↦ (1 : ℂ))
  · simpa [complementaryPfProduct, h] using
      continuous_principalPf5_matrix5 s

theorem complementaryPfProduct_matrix5_ne_zero
    (q : U5) (k i j : Fin 5) :
    complementaryPfProduct (matrix5 q.1) k i j ≠ 0 := by
  rw [complementaryPfProduct, Finset.prod_ne_zero_iff]
  intro s _hs
  by_cases h : s = k ∨ s = i ∨ s = j
  · simp [h]
  · simpa [h] using principalPf5_matrix5_ne_zero q s

theorem continuous_reducedTerm_matrix5
    (t : Fin 5 × Fin 5 × Fin 5) :
    Continuous fun q : U5 ↦ reducedTerm (matrix5 q.1) t := by
  let k := t.1
  let i := t.2.1
  let j := t.2.2
  apply ((((continuous_const.mul (continuous_matrix5_entry i k)).mul
    (continuous_matrix5_entry j k)).mul
      (continuous_principalPf5_matrix5 k)).div
        (continuous_complementaryPfProduct_matrix5 k i j))
  intro q
  exact complementaryPfProduct_matrix5_ne_zero q k i j

/-- The article's normalized thirty-term cocycle is continuous on the open
generic Pfaffian chart. -/
theorem continuous_reducedR_matrix5 :
    Continuous fun q : U5 ↦ reducedR (matrix5 q.1) := by
  apply continuous_const.mul
  apply continuous_finset_sum
  intro t _ht
  exact continuous_reducedTerm_matrix5 t

theorem continuous_normalizedEntry_reindex_matrix5
    (σ : Equiv.Perm (Fin 5)) (i j : Fin 5)
    (hi : i ≠ 0) (hj : j ≠ 0) :
    Continuous fun q : U5 ↦
      normalizedEntry (reindexGram σ (matrix5 q.1)) i j := by
  let hentry (a b : Fin 5) : Continuous fun q : U5 ↦
      reindexGram σ (matrix5 q.1) a b :=
    continuous_matrix5_entry (σ a) (σ b)
  apply (((hentry i j).mul (hentry 0 1)).mul (hentry 0 2)).div
    (((hentry 1 2).mul (hentry 0 i)).mul (hentry 0 j))
  intro q
  have hoff := (OrbitChain.matrix5_isAdmissible q).offDiagonal_ne
  exact mul_ne_zero
    (mul_ne_zero
      (hoff (σ 1) (σ 2) (σ.injective.ne (by decide)))
      (hoff (σ 0) (σ i) (σ.injective.ne hi.symm)))
    (hoff (σ 0) (σ j) (σ.injective.ne hj.symm))

theorem continuous_permute5 (σ : Equiv.Perm (Fin 5)) :
    Continuous (permute5 σ) := by
  apply Continuous.subtype_mk
  apply continuous_coord5_mk
  · exact continuous_normalizedEntry_reindex_matrix5 σ 1 3 (by decide) (by decide)
  · exact continuous_normalizedEntry_reindex_matrix5 σ 1 4 (by decide) (by decide)
  · exact continuous_normalizedEntry_reindex_matrix5 σ 2 3 (by decide) (by decide)
  · exact continuous_normalizedEntry_reindex_matrix5 σ 2 4 (by decide) (by decide)
  · exact continuous_normalizedEntry_reindex_matrix5 σ 3 4 (by decide) (by decide)

theorem continuous_chi4_reindex_matrix4 (σ : Equiv.Perm (Fin 4)) :
    Continuous fun q : U4 ↦ chi4 (reindexGram σ (matrix4 q.1)) := by
  let hentry (a b : Fin 4) : Continuous fun q : U4 ↦
      reindexGram σ (matrix4 q.1) a b :=
    continuous_matrix4_entry (σ a) (σ b)
  have hden : Continuous fun q : U4 ↦
      reindexGram σ (matrix4 q.1) 1 2 *
        reindexGram σ (matrix4 q.1) 0 3 :=
    (hentry 1 2).mul (hentry 0 3)
  have hden_ne : ∀ q : U4,
      reindexGram σ (matrix4 q.1) 1 2 *
        reindexGram σ (matrix4 q.1) 0 3 ≠ 0 := by
    intro q
    have hoff := (OrbitChain.matrix4_isAdmissible q).offDiagonal_ne
    exact mul_ne_zero
      (hoff (σ 1) (σ 2) (σ.injective.ne (by decide)))
      (hoff (σ 0) (σ 3) (σ.injective.ne (by decide)))
  apply continuous_coord4_mk
  · exact ((hentry 1 3).mul (hentry 0 2)).div hden hden_ne
  · exact ((hentry 2 3).mul (hentry 0 1)).div hden hden_ne

theorem continuous_permute4 (σ : Equiv.Perm (Fin 4)) :
    Continuous (permute4 σ) :=
  Continuous.subtype_mk (continuous_chi4_reindex_matrix4 σ) _

theorem measurable_permute5 (σ : Equiv.Perm (Fin 5)) :
    Measurable (permute5 σ) := (continuous_permute5 σ).measurable

theorem measurable_permute4 (σ : Equiv.Perm (Fin 4)) :
    Measurable (permute4 σ) := (continuous_permute4 σ).measurable

end
end Pfaffian
end Sp4
