import Sp4.Chains.Norm
import Sp4.Cohomology.AffineCocycleIdentity
import Sp4.Correspondence.Word

/-!
# Normalized Pfaffian charts as genuine orbit chains

This file closes the gap between the rational `U4`/`U5` coordinate models and
generic projective configurations.  The rank-four condition is proved inside
Lean: for the five-by-five skew matrix we exhibit its Pfaffian-cofactor kernel
vector and combine rank-nullity with a nonsingular principal minor.
-/

namespace Sp4

open scoped BigOperators Matrix

namespace OrbitChain

noncomputable section

open Pfaffian AffineCocycle

set_option maxRecDepth 100000 in
/-- The determinant of a four-by-four skew matrix is the square of its
Pfaffian. -/
theorem det_skew_four_eq_pfaffian_sq
    (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : IsSkew A) :
    A.det = pfaffian4 A ^ 2 := by
  have h00 : A 0 0 = 0 := by
    exact CharZero.eq_neg_self_iff.mp (hA 0 0)
  have h11 : A 1 1 = 0 := by
    exact CharZero.eq_neg_self_iff.mp (hA 1 1)
  have h22 : A 2 2 = 0 := by
    exact CharZero.eq_neg_self_iff.mp (hA 2 2)
  have h33 : A 3 3 = 0 := by
    exact CharZero.eq_neg_self_iff.mp (hA 3 3)
  have hmatrix : A =
      !![0, A 0 1, A 0 2, A 0 3;
         -A 0 1, 0, A 1 2, A 1 3;
         -A 0 2, -A 1 2, 0, A 2 3;
         -A 0 3, -A 1 3, -A 2 3, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [h00, h11, h22, h33, hA 0 1, hA 0 2, hA 0 3,
        hA 1 2, hA 1 3, hA 2 3]
  rw [hmatrix]
  rw [Matrix.det_succ_row _ 0]
  simp [Matrix.det_fin_three, Fin.sum_univ_succ, Fin.succAbove, pfaffian4]
  ring

/-- The Pfaffian-cofactor vector in the kernel of the normalized five-point
matrix. -/
def matrix5Kernel (q : Coord5) : Fin 5 → ℂ :=
  ![p0 q, -p1 q, p2 q, -p3 q, p4 q]

theorem matrix5_mulVec_matrix5Kernel (q : Coord5) :
    matrix5 q *ᵥ matrix5Kernel q = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, matrix5Kernel, matrix5,
      p0, p1, p2, p3, p4, Fin.sum_univ_succ] <;>
    ring

/-- The explicit kernel vector forces the five-point matrix to have rank at
most four. -/
theorem matrix5_rank_le_four (q : U5) : (matrix5 q.1).rank ≤ 4 := by
  let k : Fin 5 → ℂ := matrix5Kernel q.1
  have hk_mem : k ∈ LinearMap.ker (matrix5 q.1).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact matrix5_mulVec_matrix5Kernel q.1
  have hk_ne : k ≠ 0 := by
    intro h
    have h4 := congr_fun h 4
    change p4 q.1 = 0 at h4
    exact q.2.p4_ne h4
  have hker : (LinearMap.ker (matrix5 q.1).mulVecLin) ≠ ⊥ := by
    intro hbot
    have : k ∈ (⊥ : Submodule ℂ (Fin 5 → ℂ)) := hbot ▸ hk_mem
    exact hk_ne (by simpa using this)
  have hone : 1 ≤ Module.finrank ℂ
      (LinearMap.ker (matrix5 q.1).mulVecLin) :=
    Submodule.one_le_finrank_iff.mpr hker
  have hnull := LinearMap.finrank_range_add_finrank_ker
    (matrix5 q.1).mulVecLin
  have hnull' : (matrix5 q.1).rank +
      Module.finrank ℂ (LinearMap.ker (matrix5 q.1).mulVecLin) = 5 := by
    simpa [Matrix.rank] using hnull
  omega

/-! For six points the Pfaffian hypersurface supplies two independent kernel
vectors.  Writing them down explicitly avoids importing a general theorem on
the even rank of alternating matrices. -/

/-- Pfaffian-cofactor kernel vector obtained by deleting the zeroth row. -/
def matrix6Kernel0 (q : Coord6) : Fin 6 → ℂ :=
  ![0, pf2345 q, -pf1345 q, pf1245 q, -pf1235 q, pf1234 q]

/-- Pfaffian-cofactor kernel vector obtained by deleting the first row. -/
def matrix6Kernel1 (q : Coord6) : Fin 6 → ℂ :=
  ![pf2345 q, 0, -pf0345 q, pf0245 q, -pf0235 q, pf0234 q]

theorem matrix6_mulVec_matrix6Kernel0 (q : U6) :
    matrix6 q.1 *ᵥ matrix6Kernel0 q.1 = 0 := by
  have hpi := q.2.pi_zero
  simp only [pi6] at hpi
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, matrix6Kernel0, matrix6,
      pf1234, pf1235, pf1245, pf1345, pf2345,
      Fin.sum_univ_succ]
  · linear_combination hpi
  all_goals ring

theorem matrix6_mulVec_matrix6Kernel1 (q : U6) :
    matrix6 q.1 *ᵥ matrix6Kernel1 q.1 = 0 := by
  have hpi := q.2.pi_zero
  simp only [pi6] at hpi
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, matrix6Kernel1, matrix6,
      pf0234, pf0235, pf0245, pf0345, pf2345,
      Fin.sum_univ_succ]
  · ring
  · linear_combination -hpi
  all_goals ring

/-- The two Pfaffian-cofactor vectors are independent because the complementary
four-point Pfaffian `pf2345` is nonzero on `U6`. -/
theorem matrix6_kernel_linearIndependent (q : U6) :
    LinearIndependent ℂ (fun i : Fin 2 ↦
      if i = 0 then matrix6Kernel0 q.1 else matrix6Kernel1 q.1) := by
  rw [linearIndependent_fin2]
  constructor
  · intro h
    have h0 := congr_fun h 0
    simpa [matrix6Kernel1] using q.2.pf2345_ne h0
  · intro a h
    have h1 := congr_fun h 1
    have hzero : (0 : ℂ) = pf2345 q.1 := by
      simpa [matrix6Kernel0, matrix6Kernel1] using h1
    exact q.2.pf2345_ne hzero.symm

/-- The Pfaffian equation forces the normalized six-point matrix to have rank
at most four. -/
theorem matrix6_rank_le_four (q : U6) : (matrix6 q.1).rank ≤ 4 := by
  let K := LinearMap.ker (matrix6 q.1).mulVecLin
  let v : Fin 2 → K := fun i ↦
    if hi : i = 0 then
      ⟨matrix6Kernel0 q.1, by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        exact matrix6_mulVec_matrix6Kernel0 q⟩
    else
      ⟨matrix6Kernel1 q.1, by
        rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
        exact matrix6_mulVec_matrix6Kernel1 q⟩
  have hv : LinearIndependent ℂ v := by
    rw [linearIndependent_fin2]
    constructor
    · intro h
      have h0 := congrArg (fun z : K ↦ (z : Fin 6 → ℂ) 0) h
      apply q.2.pf2345_ne
      simpa [v, matrix6Kernel1] using h0
    · intro a h
      have h1 := congrArg (fun z : K ↦ (z : Fin 6 → ℂ) 1) h
      have hzero : (0 : ℂ) = pf2345 q.1 := by
        simpa [v, matrix6Kernel0, matrix6Kernel1] using h1
      exact q.2.pf2345_ne hzero.symm
  have htwo : 2 ≤ Module.finrank ℂ K := by
    simpa using hv.fintype_card_le_finrank
  have hnull := LinearMap.finrank_range_add_finrank_ker
    (matrix6 q.1).mulVecLin
  have hnull' : (matrix6 q.1).rank + Module.finrank ℂ K = 6 := by
    simpa [Matrix.rank, K] using hnull
  omega

theorem matrix4_isSkew (q : Coord4) : IsSkew (matrix4 q) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [matrix4]

/-- Every point of `U4` is an admissible normalized Gram matrix. -/
theorem matrix4_isAdmissible (q : U4) : IsAdmissibleGram (matrix4 q.1) := by
  have hskew : IsSkew (matrix4 q.1) := matrix4_isSkew q.1
  have hdet : (matrix4 q.1).det ≠ 0 := by
    rw [det_skew_four_eq_pfaffian_sq _ hskew, pfaffian4_matrix4]
    exact pow_ne_zero 2 q.2.delta_ne
  have hrank : (matrix4 q.1).rank = 4 := by
    simpa using Matrix.rank_of_det_ne_zero hdet
  refine {
    skew := hskew
    rank_four := hrank
    offDiagonal_ne := ?_
    principal_four_ne := ?_ }
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [matrix4, q.2.x_ne, q.2.y_ne]
  · intro e he
    let σ : Equiv.Perm (Fin 4) :=
      Equiv.ofBijective e ⟨he, Finite.injective_iff_surjective.mp he⟩
    have hp := pfaffian4_reindex (matrix4 q.1) hskew σ
    have hpf : pfaffian4 ((matrix4 q.1).submatrix e e) ≠ 0 := by
      change pfaffian4 (reindexMatrix4 (matrix4 q.1) σ) ≠ 0
      rw [hp, pfaffian4_matrix4]
      exact mul_ne_zero (by simp) q.2.delta_ne
    rw [det_skew_four_eq_pfaffian_sq]
    · exact pow_ne_zero 2 hpf
    · intro i j
      exact hskew (e i) (e j)

/-- Every point of `U5` is an admissible rank-four Gram matrix. -/
theorem matrix5_isAdmissible (q : U5) : IsAdmissibleGram (matrix5 q.1) := by
  have hskew : IsSkew (matrix5 q.1) := AffineCocycle.matrix5_isSkew q.1
  have hprincipal : ∀ (e : Fin 4 → Fin 5), Function.Injective e →
      ((matrix5 q.1).submatrix e e).det ≠ 0 := by
    intro e he
    have hsubskew : IsSkew ((matrix5 q.1).submatrix e e) := by
      intro i j
      exact hskew (e i) (e j)
    rw [det_skew_four_eq_pfaffian_sq _ hsubskew]
    apply pow_ne_zero 2
    change orderedBracket (matrix5 q.1) (e 0) (e 1) (e 2) (e 3) ≠ 0
    exact orderedBracket_matrix5_ne_zero q _ _ _ _
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  have hlower : 4 ≤ (matrix5 q.1).rank := by
    have hdet := hprincipal Fin.castSucc (Fin.castSucc_injective 4)
    have h := Matrix.rank_submatrix_le (matrix5 q.1) Fin.castSucc Fin.castSucc
    rw [Matrix.rank_of_det_ne_zero hdet] at h
    simpa using h
  refine {
    skew := hskew
    rank_four := Nat.le_antisymm (matrix5_rank_le_four q) hlower
    offDiagonal_ne := ?_
    principal_four_ne := hprincipal }
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [matrix5, q.2.u_ne, q.2.v_ne, q.2.w_ne,
      q.2.x_ne, q.2.y_ne]

/-- Six vectors in the four-dimensional symplectic space have vanishing
six-by-six Pfaffian Gram determinant. -/
theorem pfaffian6_gram_eq_zero (v : Fin 6 → SymplecticVector) :
    pfaffian6 (gram v) = 0 := by
  set_option maxHeartbeats 4000000 in
    simp [pfaffian6, gram, omega_apply]
    ring

/-- Every point of the normalized six-point Pfaffian hypersurface is an
admissible rank-four Gram matrix. -/
theorem matrix6_isAdmissible (q : U6) : IsAdmissibleGram (matrix6 q.1) := by
  have hskew : IsSkew (matrix6 q.1) := AffineCocycle.matrix6_isSkew q.1
  have hprincipal : ∀ (e : Fin 4 → Fin 6), Function.Injective e →
      ((matrix6 q.1).submatrix e e).det ≠ 0 := by
    intro e he
    have hsubskew : IsSkew ((matrix6 q.1).submatrix e e) := by
      intro i j
      exact hskew (e i) (e j)
    rw [det_skew_four_eq_pfaffian_sq _ hsubskew]
    apply pow_ne_zero 2
    change orderedBracket (matrix6 q.1) (e 0) (e 1) (e 2) (e 3) ≠ 0
    exact orderedBracket_matrix6_ne_zero q _ _ _ _
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
      (he.ne (by decide)) (he.ne (by decide)) (he.ne (by decide))
  let e : Fin 4 → Fin 6 := fun i ↦ ⟨i, Nat.lt_trans i.2 (by omega)⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    simpa [e] using congrArg Fin.val hij
  have hlower : 4 ≤ (matrix6 q.1).rank := by
    have hdet := hprincipal e he
    have h := Matrix.rank_submatrix_le (matrix6 q.1) e e
    rw [Matrix.rank_of_det_ne_zero hdet] at h
    simpa using h
  refine {
    skew := hskew
    rank_four := Nat.le_antisymm (matrix6_rank_le_four q) hlower
    offDiagonal_ne := ?_
    principal_four_ne := hprincipal }
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [matrix6, q.2.u_ne, q.2.v_ne, q.2.s_ne,
      q.2.w_ne, q.2.x_ne, q.2.t_ne, q.2.y_ne, q.2.z_ne,
      q.2.r_ne]

/-! ## Normalizing deleted Gram matrices -/

theorem isSkew_diagonalCongruence {n : Type*} {A : Matrix n n ℂ}
    (hA : IsSkew A) (d : n → ℂ) :
    IsSkew (diagonalCongruence d A) := by
  intro i j
  rw [diagonalCongruence, diagonalCongruence, hA i j]
  ring

/-- The two quotient coordinates are invariant under nonzero diagonal
congruence. -/
theorem chi4_diagonalCongruence (A : Matrix (Fin 4) (Fin 4) ℂ)
    (d : Fin 4 → ℂˣ) (h12 : A 1 2 ≠ 0) (h03 : A 0 3 ≠ 0) :
    chi4 (diagonalCongruence (fun i ↦ (d i : ℂ)) A) = chi4 A := by
  apply Coord4.ext <;>
    simp [chi4, diagonalCongruence] <;>
    field_simp [Units.ne_zero, h12, h03] <;>
    ring

/-- A normalized skew four-by-four matrix is reconstructed from `chi4`. -/
theorem matrix4_chi4_of_normalized_skew
    (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : IsSkew A)
    (hN : IsNormalized A) : matrix4 (chi4 A) = A := by
  have h00 : A 0 0 = 0 := CharZero.eq_neg_self_iff.mp (hA 0 0)
  have h11 : A 1 1 = 0 := CharZero.eq_neg_self_iff.mp (hA 1 1)
  have h22 : A 2 2 = 0 := CharZero.eq_neg_self_iff.mp (hA 2 2)
  have h33 : A 3 3 = 0 := CharZero.eq_neg_self_iff.mp (hA 3 3)
  have h01 : A 0 1 = 1 := hN.firstRow 1 (by decide)
  have h02 : A 0 2 = 1 := hN.firstRow 2 (by decide)
  have h03 : A 0 3 = 1 := hN.firstRow 3 (by decide)
  have h12 : A 1 2 = 1 := hN.twelve
  have hx : (chi4 A).x = A 1 3 := by
    simp [chi4, h02, h03, h12]
  have hy : (chi4 A).y = A 2 3 := by
    simp [chi4, h01, h03, h12]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix4, hx, hy, h00, h11, h22, h33, h01, h02, h03, h12,
      hA 0 1, hA 0 2, hA 0 3, hA 1 2, hA 1 3, hA 2 3]

/-- The rational face formulas are exactly the diagonal-congruence invariants
of the five deleted principal matrices. -/
theorem chi4_deleteMatrix_matrix5 (q : U5) (i : Fin 5) :
    chi4 (deleteMatrix i (matrix5 q.1)) = (face4At i q).1 := by
  fin_cases i <;>
    apply Coord4.ext <;>
    simp [chi4, deleteMatrix, matrix5, face4At, face4_0, face4_1,
      face4_2, face4_3, face4_4, face4Coord0, face4Coord1,
      face4Coord2, face4Coord3, face4Coord4, Fin.succAbove] <;>
    field_simp [q.2.u_ne, q.2.v_ne, q.2.w_ne, q.2.x_ne, q.2.y_ne] <;>
    ring

theorem deleteMatrix_matrix5_offDiagonal (q : U5) (i : Fin 5) :
    ∀ a b : Fin 4, a ≠ b → deleteMatrix i (matrix5 q.1) a b ≠ 0 := by
  intro a b hab
  exact (matrix5_isAdmissible q).offDiagonal_ne _ _
    (Fin.succAbove_right_injective.ne hab)

/-- Each rational face matrix is precisely a normalized representative of
the corresponding deleted five-point Gram matrix. -/
theorem exists_face4_diagonalCongruence (q : U5) (i : Fin 5) :
    ∃ d : Fin 4 → ℂˣ,
      matrix4 (face4At i q).1 =
        diagonalCongruence (fun j ↦ (d j : ℂ))
          (deleteMatrix i (matrix5 q.1)) := by
  let B := deleteMatrix i (matrix5 q.1)
  have hBoff : ∀ a b, a ≠ b → B a b ≠ 0 :=
    deleteMatrix_matrix5_offDiagonal q i
  obtain ⟨d, hN⟩ := exists_normalized_diagonalCongruence B hBoff
  let C := diagonalCongruence (fun j ↦ (d j : ℂ)) B
  have hBskew : IsSkew B := by
    intro a b
    exact AffineCocycle.matrix5_isSkew q.1
      (i.succAbove a) (i.succAbove b)
  have hCskew : IsSkew C := isSkew_diagonalCongruence hBskew _
  have hchi : chi4 C = chi4 B :=
    chi4_diagonalCongruence B d (hBoff 1 2 (by decide))
      (hBoff 0 3 (by decide))
  refine ⟨d, ?_⟩
  calc
    matrix4 (face4At i q).1 = matrix4 (chi4 B) := by
      rw [chi4_deleteMatrix_matrix5]
    _ = matrix4 (chi4 C) := congrArg matrix4 hchi.symm
    _ = C := matrix4_chi4_of_normalized_skew C hCskew hN

/-- The six rational five-point face formulas are normalized representatives
of the corresponding deleted six-point Gram matrices. -/
theorem exists_face5_diagonalCongruence (q : U6) (i : Fin 6) :
    ∃ d : Fin 5 → ℂˣ,
      matrix5 (face5At i q).1 =
        diagonalCongruence (fun j ↦ (d j : ℂ))
          (deleteMatrix i (matrix6 q.1)) := by
  obtain ⟨d, hd, hmatrix⟩ := AffineCocycle.exists_face5MatrixAt_scale q i
  let du : Fin 5 → ℂˣ := fun j ↦ Units.mk0 (d j) (hd j)
  refine ⟨du, ?_⟩
  calc
    matrix5 (face5At i q).1 =
        AffineCocycle.diagonalScale
          (AffineCocycle.deleteMatrix6 (matrix6 q.1) i) d := hmatrix
    _ = diagonalCongruence (fun j ↦ (du j : ℂ))
          (deleteMatrix i (matrix6 q.1)) := by
      ext a b
      rfl

/-- Normalizing any generic skew four-by-four matrix gives the matrix encoded
by its diagonal-congruence invariant `chi4`. -/
theorem exists_matrix4_chi4_diagonalCongruence
    (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : IsSkew A)
    (hoff : ∀ i j, i ≠ j → A i j ≠ 0) :
    ∃ d : Fin 4 → ℂˣ,
      matrix4 (chi4 A) =
        diagonalCongruence (fun i ↦ (d i : ℂ)) A := by
  obtain ⟨d, hN⟩ := exists_normalized_diagonalCongruence A hoff
  let C := diagonalCongruence (fun i ↦ (d i : ℂ)) A
  have hCskew : IsSkew C := isSkew_diagonalCongruence hA _
  have hchi : chi4 C = chi4 A :=
    chi4_diagonalCongruence A d (hoff 1 2 (by decide))
      (hoff 0 3 (by decide))
  refine ⟨d, ?_⟩
  calc
    matrix4 (chi4 A) = matrix4 (chi4 C) := congrArg matrix4 hchi.symm
    _ = C := matrix4_chi4_of_normalized_skew C hCskew hN

/-! ## Chosen realizations and compatibility with faces -/

/-- A generic projective realization together with a lift whose Gram matrix is
literally the prescribed matrix. -/
structure GramRealization {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) where
  config : ProjectiveConfig n
  lift : ProjectiveLift config
  generic : IsGeneric config
  gram_eq : gram lift.vec = A

theorem nonempty_gramRealization_of_admissible {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsAdmissibleGram A)
    (e : Fin 4 → Fin n) (he : Function.Injective e) :
    Nonempty (GramRealization A) := by
  obtain ⟨l, u, hl, hu⟩ := hA.exists_generic_realization e he
  exact ⟨⟨l, u, hl, hu⟩⟩

/-! The normalized slice admits a global rational realization.  This is
stronger than a bare choice of a Gram realization and is the concrete local
section needed by the Lebesgue-coordinate argument.  In the fixed basis
`(e₁,f₁,e₂,f₂)`, the first four columns are a basis with determinant equal to
the leading Pfaffian; every later column is then recovered from its four
pairings with that basis. -/

/-- Explicit lifts of the four normalized projective points. -/
def normalizedVectors4 (q : U4) : Fin 4 → SymplecticVector :=
  ![![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![-1, 1, 1, 0],
    ![-q.1.x, 1, 0, delta4 q.1]]

theorem normalizedVectors4_ne (q : U4) (i : Fin 4) :
    normalizedVectors4 q i ≠ 0 := by
  fin_cases i
  · intro h
    have hi := congrFun h 0
    norm_num [normalizedVectors4] at hi
  all_goals
    intro h
    have hi := congrFun h 1
    norm_num [normalizedVectors4] at hi

theorem gram_normalizedVectors4 (q : U4) :
    gram (normalizedVectors4 q) = matrix4 q.1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, normalizedVectors4, matrix4, omega_apply, delta4] <;> ring

/-- Explicit lifts of the five normalized projective points. -/
noncomputable def normalizedVectors5 (q : U5) : Fin 5 → SymplecticVector :=
  ![![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![-1, 1, 1, 0],
    ![-q.1.u, 1, 0, p4 q.1],
    ![-q.1.v, 1, (q.1.v - q.1.u - q.1.y) / p4 q.1,
      p3 q.1]]

theorem normalizedVectors5_ne (q : U5) (i : Fin 5) :
    normalizedVectors5 q i ≠ 0 := by
  fin_cases i
  · intro h
    have hi := congrFun h 0
    norm_num [normalizedVectors5] at hi
  all_goals
    intro h
    have hi := congrFun h 1
    norm_num [normalizedVectors5] at hi

theorem gram_normalizedVectors5 (q : U5) :
    gram (normalizedVectors5 q) = matrix5 q.1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, normalizedVectors5, matrix5, omega_apply, p3] <;>
    field_simp [q.2.p4_ne]
  all_goals try simp [p4]
  all_goals ring

/-- Explicit lifts of the six normalized projective points.  The sole last
pairing is the six-point Pfaffian equation. -/
noncomputable def normalizedVectors6 (q : U6) : Fin 6 → SymplecticVector :=
  ![![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![-1, 1, 1, 0],
    ![-q.1.u, 1, 0, pf0123 q.1],
    ![-q.1.v, 1, (q.1.v - q.1.u - q.1.y) / pf0123 q.1,
      pf0124 q.1],
    ![-q.1.s, 1, (q.1.s - q.1.u - q.1.z) / pf0123 q.1,
      pf0125 q.1]]

theorem normalizedVectors6_ne (q : U6) (i : Fin 6) :
    normalizedVectors6 q i ≠ 0 := by
  fin_cases i
  · intro h
    have hi := congrFun h 0
    norm_num [normalizedVectors6] at hi
  all_goals
    intro h
    have hi := congrFun h 1
    norm_num [normalizedVectors6] at hi

theorem gram_normalizedVectors6 (q : U6) :
    gram (normalizedVectors6 q) = matrix6 q.1 := by
  have hpi := q.2.pi_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, normalizedVectors6, matrix6, omega_apply,
      pf0124, pf0125] <;>
    field_simp [q.2.pf0123_ne]
  all_goals simp [pf0123, pi6] at hpi ⊢
  all_goals try ring
  all_goals first | linear_combination hpi | linear_combination -hpi

noncomputable def normalizedProjectiveConfig4 (q : U4) : ProjectiveConfig 4 :=
  fun i => Projectivization.mk ℂ (normalizedVectors4 q i)
    (normalizedVectors4_ne q i)

noncomputable def normalizedProjectiveLift4 (q : U4) :
    ProjectiveLift (normalizedProjectiveConfig4 q) where
  vec := normalizedVectors4 q
  ne_zero := normalizedVectors4_ne q
  projectivizes _ := rfl

/-- The explicit four-point Gram realization. -/
noncomputable def normalizedRealization4 (q : U4) :
    GramRealization (matrix4 q.1) where
  config := normalizedProjectiveConfig4 q
  lift := normalizedProjectiveLift4 q
  generic := (normalizedProjectiveLift4 q).isGeneric_of_gram_isAdmissible
    (gram_normalizedVectors4 q ▸ matrix4_isAdmissible q)
  gram_eq := gram_normalizedVectors4 q

noncomputable def normalizedProjectiveConfig5 (q : U5) : ProjectiveConfig 5 :=
  fun i => Projectivization.mk ℂ (normalizedVectors5 q i)
    (normalizedVectors5_ne q i)

noncomputable def normalizedProjectiveLift5 (q : U5) :
    ProjectiveLift (normalizedProjectiveConfig5 q) where
  vec := normalizedVectors5 q
  ne_zero := normalizedVectors5_ne q
  projectivizes _ := rfl

/-- The explicit five-point Gram realization. -/
noncomputable def normalizedRealization5 (q : U5) :
    GramRealization (matrix5 q.1) where
  config := normalizedProjectiveConfig5 q
  lift := normalizedProjectiveLift5 q
  generic := (normalizedProjectiveLift5 q).isGeneric_of_gram_isAdmissible
    (gram_normalizedVectors5 q ▸ matrix5_isAdmissible q)
  gram_eq := gram_normalizedVectors5 q

noncomputable def normalizedProjectiveConfig6 (q : U6) : ProjectiveConfig 6 :=
  fun i => Projectivization.mk ℂ (normalizedVectors6 q i)
    (normalizedVectors6_ne q i)

noncomputable def normalizedProjectiveLift6 (q : U6) :
    ProjectiveLift (normalizedProjectiveConfig6 q) where
  vec := normalizedVectors6 q
  ne_zero := normalizedVectors6_ne q
  projectivizes _ := rfl

/-- The explicit six-point Gram realization. -/
noncomputable def normalizedRealization6 (q : U6) :
    GramRealization (matrix6 q.1) where
  config := normalizedProjectiveConfig6 q
  lift := normalizedProjectiveLift6 q
  generic := (normalizedProjectiveLift6 q).isGeneric_of_gram_isAdmissible
    (gram_normalizedVectors6 q ▸ matrix6_isAdmissible q)
  gram_eq := gram_normalizedVectors6 q

/-- The genuine generic configuration represented by a point of `U4`. -/
def normalizedConfig4 (q : U4) : Sp4.OrbitChain.GenericConfig 4 :=
  ⟨(normalizedRealization4 q).config, (normalizedRealization4 q).generic⟩

/-- The genuine generic configuration represented by a point of `U5`. -/
def normalizedConfig5 (q : U5) : Sp4.OrbitChain.GenericConfig 5 :=
  ⟨(normalizedRealization5 q).config, (normalizedRealization5 q).generic⟩

/-- The genuine generic configuration represented by a point of `U6`. -/
def normalizedConfig6 (q : U6) : Sp4.OrbitChain.GenericConfig 6 :=
  ⟨(normalizedRealization6 q).config, (normalizedRealization6 q).generic⟩

/-- The lift obtained by deleting one vector from the chosen five-point
realization. -/
def normalizedFaceLift5 (q : U5) (i : Fin 5) :
    ProjectiveLift (Sp4.OrbitChain.face i (normalizedConfig5 q)).1 where
  vec := FinTuple.delete i (normalizedRealization5 q).lift.vec
  ne_zero j := (normalizedRealization5 q).lift.ne_zero (i.succAbove j)
  projectivizes j := (normalizedRealization5 q).lift.projectivizes (i.succAbove j)

/-- The lift obtained by deleting one vector from the chosen six-point
realization. -/
def normalizedFaceLift6 (q : U6) (i : Fin 6) :
    ProjectiveLift (Sp4.OrbitChain.face i (normalizedConfig6 q)).1 where
  vec := FinTuple.delete i (normalizedRealization6 q).lift.vec
  ne_zero j := (normalizedRealization6 q).lift.ne_zero (i.succAbove j)
  projectivizes j := (normalizedRealization6 q).lift.projectivizes (i.succAbove j)

/-- The chosen lift of a four-point configuration, reindexed by a
permutation. -/
def normalizedPermutedLift4 (q : U4) (σ : Equiv.Perm (Fin 4)) :
    ProjectiveLift (permuteGeneric σ (normalizedConfig4 q)).1 where
  vec := fun i ↦ (normalizedRealization4 q).lift.vec (σ i)
  ne_zero i := (normalizedRealization4 q).lift.ne_zero (σ i)
  projectivizes i := (normalizedRealization4 q).lift.projectivizes (σ i)

theorem gram_normalizedPermutedLift4 (q : U4)
    (σ : Equiv.Perm (Fin 4)) :
    gram (normalizedPermutedLift4 q σ).vec =
      reindexMatrix4 (matrix4 q.1) σ := by
  ext i j
  exact congr_fun (congr_fun (normalizedRealization4 q).gram_eq (σ i)) (σ j)

/-- Diagonally congruent Gram matrices of arbitrary chosen lifts determine the
same symplectic orbit of generic projective configurations. -/
theorem exists_symplectic_smul_of_lift_gram_diagonalCongruent {n : ℕ}
    (l m : ProjectiveConfig n) (hl : IsGeneric l) (hm : IsGeneric m)
    (ul : ProjectiveLift l) (um : ProjectiveLift m)
    (e : Fin 4 → Fin n) (he : Function.Injective e)
    (d : Fin n → ℂˣ)
    (hgram : gram ul.vec =
      diagonalCongruence (fun i ↦ (d i : ℂ)) (gram um.vec)) :
    ∃ g : SymplecticGroup, g • l = m := by
  let w : Fin n → SymplecticVector := fun i ↦ (d i : ℂ) • um.vec i
  have hw_ne (i : Fin n) : w i ≠ 0 :=
    smul_ne_zero (Units.ne_zero (d i)) (um.ne_zero i)
  let um' : ProjectiveLift m :=
    { vec := w
      ne_zero := hw_ne
      projectivizes := fun i ↦ by
        rw [← um.projectivizes i, Projectivization.mk_eq_mk_iff']
        exact ⟨(d i : ℂ), rfl⟩ }
  have hwgram : gram w =
      diagonalCongruence (fun i ↦ (d i : ℂ)) (gram um.vec) := by
    rw [gram_smul]
  have hgram' : gram ul.vec = gram um'.vec := by
    simpa [um', w] using hgram.trans hwgram.symm
  let bl := ul.selectedBasis hl e he
  let bm := um'.selectedBasis hm e he
  obtain ⟨g, hg⟩ := exists_symplectic_of_gram_eq ul.vec um'.vec e bl bm
    (by intro i; simp [bl]) (by intro i; simp [bm]) hgram'
  refine ⟨g, funext fun i ↦ ?_⟩
  change g.1 • l i = m i
  rw [← ul.projectivizes i, ← um'.projectivizes i,
    Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  exact ⟨1, by simpa using (hg i).symm⟩

/-- Coordinate reindexing is realized by permuting the underlying generic
configuration, up to a symplectic transformation. -/
theorem exists_smul_normalizedConfig4_eq_permute (q q' : U4)
    (σ : Equiv.Perm (Fin 4))
    (hchi : chi4 (reindexMatrix4 (matrix4 q.1) σ) = q'.1) :
    ∃ g : SymplecticGroup,
      smulGeneric g (normalizedConfig4 q') =
        permuteGeneric σ (normalizedConfig4 q) := by
  let A := reindexMatrix4 (matrix4 q.1) σ
  have hAskew : IsSkew A :=
    isSkew_reindexMatrix4 (matrix4_isSkew q.1) σ
  have hAoff : ∀ i j, i ≠ j → A i j ≠ 0 := by
    intro i j hij
    exact (matrix4_isAdmissible q).offDiagonal_ne (σ i) (σ j)
      (σ.injective.ne hij)
  obtain ⟨d, hd⟩ :=
    exists_matrix4_chi4_diagonalCongruence A hAskew hAoff
  have hd' : matrix4 q'.1 =
      diagonalCongruence (fun i ↦ (d i : ℂ)) A := by
    rw [← hchi]
    exact hd
  obtain ⟨g, hg⟩ :=
    exists_symplectic_smul_of_lift_gram_diagonalCongruent
      (normalizedRealization4 q').config
      (permuteGeneric σ (normalizedConfig4 q)).1
      (normalizedRealization4 q').generic
      (permuteGeneric σ (normalizedConfig4 q)).2
      (normalizedRealization4 q').lift
      (normalizedPermutedLift4 q σ)
      id Function.injective_id d (by
        rw [(normalizedRealization4 q').gram_eq,
          gram_normalizedPermutedLift4]
        exact hd')
  exact ⟨g, Subtype.ext hg⟩

/-- Reindexing covariance in the alternating orbit quotient. -/
theorem ofConfig_normalizedConfig4_reindex {R : Type*} [CommRing R]
    (q q' : U4) (σ : Equiv.Perm (Fin 4))
    (hchi : chi4 (reindexMatrix4 (matrix4 q.1) σ) = q'.1) :
    ofConfig (R := R) (normalizedConfig4 q') =
      permSign R σ • ofConfig (R := R) (normalizedConfig4 q) := by
  obtain ⟨g, hg⟩ := exists_smul_normalizedConfig4_eq_permute q q' σ hchi
  have horbit := ofConfig_smulGeneric (R := R) g (normalizedConfig4 q')
  rw [hg] at horbit
  exact horbit.symm.trans (ofConfig_permuteGeneric σ (normalizedConfig4 q))

theorem ofConfig_normalizedConfig4_cyclic {R : Type*} [CommRing R] (q : U4) :
    ofConfig (R := R) (normalizedConfig4 (cyclic q)) =
      ofConfig (R := R) (normalizedConfig4 q) := by
  have hchi : chi4 (reindexMatrix4 (matrix4 q.1) permCyclic) =
      (cyclic q).1 := by
    change chi4 (reindex4 permCyclic (matrix4 q.1)) = cyclicCoord q.1
    exact chi4_reindex4_permCyclic q
  simpa [permSign, sign_permCyclic] using
    (ofConfig_normalizedConfig4_reindex (R := R) q (cyclic q) permCyclic hchi)

theorem ofConfig_normalizedConfig4_rho {R : Type*} [CommRing R] (q : U4) :
    ofConfig (R := R) (normalizedConfig4 (rho q)) =
      -ofConfig (R := R) (normalizedConfig4 q) := by
  have hchi : chi4 (reindexMatrix4 (matrix4 q.1) permRho) = (rho q).1 := by
    change chi4 (reindex4 permRho (matrix4 q.1)) = rhoCoord q.1
    exact chi4_reindex4_permRho q
  simpa [permSign, sign_permRho] using
    (ofConfig_normalizedConfig4_reindex (R := R) q (rho q) permRho hchi)

theorem ofConfig_normalizedConfig4_oddX {R : Type*} [CommRing R] (q : U4) :
    ofConfig (R := R) (normalizedConfig4 (oddX q)) =
      -ofConfig (R := R) (normalizedConfig4 q) := by
  have hchi : chi4 (reindexMatrix4 (matrix4 q.1) permOddX) = (oddX q).1 := by
    change chi4 (reindex4 permOddX (matrix4 q.1)) = oddXCoord q.1
    exact chi4_reindex4_permOddX q
  simpa [permSign, sign_permOddX] using
    (ofConfig_normalizedConfig4_reindex (R := R) q (oddX q) permOddX hchi)

theorem ofConfig_normalizedConfig4_oddY {R : Type*} [CommRing R] (q : U4) :
    ofConfig (R := R) (normalizedConfig4 (oddY q)) =
      -ofConfig (R := R) (normalizedConfig4 q) := by
  have hchi : chi4 (reindexMatrix4 (matrix4 q.1) permOddY) = (oddY q).1 := by
    change chi4 (reindex4 permOddY (matrix4 q.1)) = oddYCoord q.1
    exact chi4_reindex4_permOddY q
  simpa [permSign, sign_permOddY] using
    (ofConfig_normalizedConfig4_reindex (R := R) q (oddY q) permOddY hchi)

/-! Odd stabilizers vanish over the real chain module. -/

theorem oddX_eq_self_of_x_eq_neg_one (q : U4) (hx : q.1.x = -1) :
    oddX q = q := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [oddX, oddXCoord] <;>
    field_simp [q.2.x_ne] <;>
    rw [hx] <;>
    ring

theorem rho_eq_self_of_y_eq_neg_x (q : U4) (hy : q.1.y = -q.1.x) :
    rho q = q := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [rho, rhoCoord] <;>
    rw [hy] <;>
    ring

theorem oddY_eq_self_of_y_eq_one (q : U4) (hy : q.1.y = 1) :
    oddY q = q := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [oddY, oddYCoord] <;>
    field_simp [q.2.y_ne] <;>
    rw [hy] <;>
    ring

theorem two_smul_of_eq_neg_self {R M : Type*} [CommRing R]
    [AddCommGroup M] [_root_.Module R M] {x : M} (h : x = -x) :
    (2 : R) • x = 0 := by
  calc
    (2 : R) • x = x + x := by module
    _ = -x + x := congrArg (fun z ↦ z + x) h
    _ = 0 := neg_add_cancel x

theorem two_smul_ofConfig_normalizedConfig4_of_x_eq_neg_one
    {R : Type*} [CommRing R] (q : U4) (hx : q.1.x = -1) :
    (2 : R) • ofConfig (R := R) (normalizedConfig4 q) = 0 := by
  have h := ofConfig_normalizedConfig4_oddX (R := R) q
  rw [oddX_eq_self_of_x_eq_neg_one q hx] at h
  exact two_smul_of_eq_neg_self h

theorem two_smul_ofConfig_normalizedConfig4_of_y_eq_neg_x
    {R : Type*} [CommRing R] (q : U4) (hy : q.1.y = -q.1.x) :
    (2 : R) • ofConfig (R := R) (normalizedConfig4 q) = 0 := by
  have h := ofConfig_normalizedConfig4_rho (R := R) q
  rw [rho_eq_self_of_y_eq_neg_x q hy] at h
  exact two_smul_of_eq_neg_self h

theorem two_smul_ofConfig_normalizedConfig4_of_y_eq_one
    {R : Type*} [CommRing R] (q : U4) (hy : q.1.y = 1) :
    (2 : R) • ofConfig (R := R) (normalizedConfig4 q) = 0 := by
  have h := ofConfig_normalizedConfig4_oddY (R := R) q
  rw [oddY_eq_self_of_y_eq_one q hy] at h
  exact two_smul_of_eq_neg_self h

theorem eq_zero_of_eq_neg_self_real {M : Type*} [AddCommGroup M]
    [_root_.Module ℝ M] {x : M} (h : x = -x) : x = 0 := by
  have hadd : x + x = 0 := by
    calc
      x + x = -x + x := congrArg (fun z ↦ z + x) h
      _ = 0 := neg_add_cancel x
  calc
    x = (1 / 2 : ℝ) • (x + x) := by module
    _ = (1 / 2 : ℝ) • 0 := by rw [hadd]
    _ = 0 := smul_zero _

theorem ofConfig_normalizedConfig4_zero_of_x_eq_neg_one
    (q : U4) (hx : q.1.x = -1) :
    ofConfig (R := ℝ) (normalizedConfig4 q) = 0 := by
  have h := ofConfig_normalizedConfig4_oddX (R := ℝ) q
  rw [oddX_eq_self_of_x_eq_neg_one q hx] at h
  exact eq_zero_of_eq_neg_self_real h

theorem ofConfig_normalizedConfig4_zero_of_y_eq_neg_x
    (q : U4) (hy : q.1.y = -q.1.x) :
    ofConfig (R := ℝ) (normalizedConfig4 q) = 0 := by
  have h := ofConfig_normalizedConfig4_rho (R := ℝ) q
  rw [rho_eq_self_of_y_eq_neg_x q hy] at h
  exact eq_zero_of_eq_neg_self_real h

theorem ofConfig_normalizedConfig4_zero_of_y_eq_one
    (q : U4) (hy : q.1.y = 1) :
    ofConfig (R := ℝ) (normalizedConfig4 q) = 0 := by
  have h := ofConfig_normalizedConfig4_oddY (R := ℝ) q
  rw [oddY_eq_self_of_y_eq_one q hy] at h
  exact eq_zero_of_eq_neg_self_real h

/-- Deleting an entry of the chosen five-point lift deletes the corresponding
row and column of its Gram matrix. -/
theorem gram_normalizedFaceLift5 (q : U5) (i : Fin 5) :
    gram (normalizedFaceLift5 q i).vec =
      deleteMatrix i (matrix5 q.1) := by
  rw [show gram (normalizedFaceLift5 q i).vec =
      deleteMatrix i (gram (normalizedRealization5 q).lift.vec) by rfl]
  rw [(normalizedRealization5 q).gram_eq]

/-- Deleting an entry of the chosen six-point lift deletes the corresponding
row and column of its Gram matrix. -/
theorem gram_normalizedFaceLift6 (q : U6) (i : Fin 6) :
    gram (normalizedFaceLift6 q i).vec =
      deleteMatrix i (matrix6 q.1) := by
  rw [show gram (normalizedFaceLift6 q i).vec =
      deleteMatrix i (gram (normalizedRealization6 q).lift.vec) by rfl]
  rw [(normalizedRealization6 q).gram_eq]

/-- The normalized coordinate face and the actual deleted projective
configuration lie in the same symplectic orbit. -/
theorem exists_smul_normalizedConfig4_eq_face (q : U5) (i : Fin 5) :
    ∃ g : SymplecticGroup,
      smulGeneric g (normalizedConfig4 (face4At i q)) =
        face i (normalizedConfig5 q) := by
  obtain ⟨d, hd⟩ := exists_face4_diagonalCongruence q i
  obtain ⟨g, hg⟩ :=
    exists_symplectic_smul_of_lift_gram_diagonalCongruent
      (normalizedRealization4 (face4At i q)).config
      (face i (normalizedConfig5 q)).1
      (normalizedRealization4 (face4At i q)).generic
      (face i (normalizedConfig5 q)).2
      (normalizedRealization4 (face4At i q)).lift
      (normalizedFaceLift5 q i)
      id Function.injective_id d (by
        rw [(normalizedRealization4 (face4At i q)).gram_eq,
          gram_normalizedFaceLift5]
        exact hd)
  refine ⟨g, Subtype.ext ?_⟩
  exact hg

/-- Face compatibility after passing to alternating symplectic orbit chains. -/
theorem ofConfig_face_normalizedConfig5 {R : Type*} [CommRing R]
    (q : U5) (i : Fin 5) :
    ofConfig (R := R) (face i (normalizedConfig5 q)) =
      ofConfig (R := R) (normalizedConfig4 (face4At i q)) := by
  obtain ⟨g, hg⟩ := exists_smul_normalizedConfig4_eq_face q i
  rw [← hg, ofConfig_smulGeneric]

/-- The normalized five-point coordinate face and the actual deleted
six-point configuration lie in the same symplectic orbit. -/
theorem exists_smul_normalizedConfig5_eq_face (q : U6) (i : Fin 6) :
    ∃ g : SymplecticGroup,
      smulGeneric g (normalizedConfig5 (face5At i q)) =
        face i (normalizedConfig6 q) := by
  obtain ⟨d, hd⟩ := exists_face5_diagonalCongruence q i
  obtain ⟨g, hg⟩ :=
    exists_symplectic_smul_of_lift_gram_diagonalCongruent
      (normalizedRealization5 (face5At i q)).config
      (face i (normalizedConfig6 q)).1
      (normalizedRealization5 (face5At i q)).generic
      (face i (normalizedConfig6 q)).2
      (normalizedRealization5 (face5At i q)).lift
      (normalizedFaceLift6 q i)
      Fin.castSucc (Fin.castSucc_injective 4) d (by
        rw [(normalizedRealization5 (face5At i q)).gram_eq,
          gram_normalizedFaceLift6]
        exact hd)
  exact ⟨g, Subtype.ext hg⟩

/-- Face compatibility for the six-to-five coordinate model after passing to
alternating symplectic orbit chains. -/
theorem ofConfig_face_normalizedConfig6 {R : Type*} [CommRing R]
    (q : U6) (i : Fin 6) :
    ofConfig (R := R) (face i (normalizedConfig6 q)) =
      ofConfig (R := R) (normalizedConfig5 (face5At i q)) := by
  obtain ⟨g, hg⟩ := exists_smul_normalizedConfig5_eq_face q i
  rw [← hg, ofConfig_smulGeneric]

/-- The coordinate five-term boundary is the genuine orbit-chain boundary of
the chosen five-point realization. -/
theorem boundary_normalizedConfig5 (R : Type*) [CommRing R] (q : U5) :
    boundary R 4 (ofConfig (R := R) (normalizedConfig5 q)) =
      ∑ i : Fin 5, (-1 : R) ^ i.val •
        ofConfig (R := R) (normalizedConfig4 (face4At i q)) := by
  rw [boundary_ofConfig]
  apply Finset.sum_congr rfl
  intro i _
  rw [ofConfig_face_normalizedConfig5]

/-- The coordinate six-term boundary is the genuine orbit-chain boundary of
the chosen six-point realization. -/
theorem boundary_normalizedConfig6 (R : Type*) [CommRing R] (q : U6) :
    boundary R 5 (ofConfig (R := R) (normalizedConfig6 q)) =
      ∑ i : Fin 6, (-1 : R) ^ i.val •
        ofConfig (R := R) (normalizedConfig5 (face5At i q)) := by
  rw [boundary_ofConfig]
  apply Finset.sum_congr rfl
  intro i _
  rw [ofConfig_face_normalizedConfig6]

/-! ## The four defect--dilation boundaries -/

theorem cyclic_phi2_face0_eq_face2 (q : Adm2) :
    cyclic (face4_0 (phi2 q)) = face4_2 (phi2 q) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [cyclic, cyclicCoord, face4_0, face4Coord0,
      face4_2, face4Coord2, phi2, Phi2Coord] <;>
    field_simp [q.1.2.x_ne, q.1.2.y_ne] <;>
    ring

theorem boundary_phi1 (q : Adm1) :
    boundary ℝ 4 (ofConfig (R := ℝ) (normalizedConfig5 (phi1 q))) =
      (2 : ℝ) • ofConfig (R := ℝ) (normalizedConfig4 (base1 q)) -
        ofConfig (R := ℝ) (normalizedConfig4 (T1 q)) := by
  rw [boundary_normalizedConfig5]
  simp [Fin.sum_univ_succ, face4At]
  rw [phi1_face0_eq_rho_face2, phi1_face1_eq_rho_base,
    ofConfig_normalizedConfig4_rho,
    ofConfig_normalizedConfig4_rho]
  norm_num
  rw [show face4_3 (phi1 q) = T1 q by rfl]
  module

/-- Integral form of the first special boundary identity. -/
theorem boundary_phi1_int (q : Adm1) :
    boundary ℤ 4 (ofConfig (R := ℤ) (normalizedConfig5 (phi1 q))) =
      (2 : ℤ) • ofConfig (R := ℤ) (normalizedConfig4 (base1 q)) -
        ofConfig (R := ℤ) (normalizedConfig4 (T1 q)) := by
  rw [boundary_normalizedConfig5]
  simp [Fin.sum_univ_succ, face4At]
  rw [phi1_face0_eq_rho_face2, phi1_face1_eq_rho_base,
    ofConfig_normalizedConfig4_rho,
    ofConfig_normalizedConfig4_rho]
  norm_num
  rw [show face4_3 (phi1 q) = T1 q by rfl]
  module

theorem boundary_phi2 (q : Adm2) :
    boundary ℝ 4 (ofConfig (R := ℝ) (normalizedConfig5 (phi2 q))) =
      (2 : ℝ) • ofConfig (R := ℝ) (normalizedConfig4 (base2 q)) -
        ofConfig (R := ℝ) (normalizedConfig4 (T2 q)) := by
  have hzero0 :
      ofConfig (R := ℝ) (normalizedConfig4 (face4_0 (phi2 q))) = 0 :=
    ofConfig_normalizedConfig4_zero_of_x_eq_neg_one _
      (phi2_face0_x_eq_neg_one q)
  have hzero2 :
      ofConfig (R := ℝ) (normalizedConfig4 (face4_2 (phi2 q))) = 0 :=
    ofConfig_normalizedConfig4_zero_of_y_eq_neg_x _
      (phi2_face2_y_eq_neg_x q)
  rw [boundary_normalizedConfig5]
  simp [Fin.sum_univ_succ, face4At]
  rw [phi2_face1_eq_rho_base, ofConfig_normalizedConfig4_rho,
    hzero0, hzero2]
  norm_num
  rw [show face4_3 (phi2 q) = T2 q by rfl]
  module

/-- Integral form of the second special boundary identity.  Its two singular
faces form one even orbit and hence contribute twice the same `2`-torsion
class. -/
theorem boundary_phi2_int (q : Adm2) :
    boundary ℤ 4 (ofConfig (R := ℤ) (normalizedConfig5 (phi2 q))) =
      (2 : ℤ) • ofConfig (R := ℤ) (normalizedConfig4 (base2 q)) -
        ofConfig (R := ℤ) (normalizedConfig4 (T2 q)) := by
  let c0 : Module ℤ 4 :=
    ofConfig (R := ℤ) (normalizedConfig4 (face4_0 (phi2 q)))
  let cb : Module ℤ 4 :=
    ofConfig (R := ℤ) (normalizedConfig4 (base2 q))
  let ct : Module ℤ 4 :=
    ofConfig (R := ℤ) (normalizedConfig4 (T2 q))
  have h02 :
      ofConfig (R := ℤ) (normalizedConfig4 (face4_2 (phi2 q))) = c0 := by
    rw [← cyclic_phi2_face0_eq_face2]
    exact ofConfig_normalizedConfig4_cyclic (R := ℤ) _
  have htwo : (2 : ℤ) • c0 = 0 :=
    two_smul_ofConfig_normalizedConfig4_of_x_eq_neg_one _
      (phi2_face0_x_eq_neg_one q)
  rw [boundary_normalizedConfig5]
  simp [Fin.sum_univ_succ, face4At]
  rw [phi2_face1_eq_rho_base, ofConfig_normalizedConfig4_rho, h02]
  norm_num
  rw [show face4_3 (phi2 q) = T2 q by rfl]
  change c0 + (cb + (c0 + (-ct + cb))) = (2 : ℤ) • cb - ct
  calc
    c0 + (cb + (c0 + (-ct + cb))) =
        (2 : ℤ) • c0 + ((2 : ℤ) • cb - ct) := by module
    _ = (2 : ℤ) • cb - ct := by rw [htwo, zero_add]

theorem boundary_phi3 (q : Adm3) :
    boundary ℝ 4 (ofConfig (R := ℝ) (normalizedConfig5 (phi3 q))) =
      (2 : ℝ) • ofConfig (R := ℝ) (normalizedConfig4 (base3 q)) -
        ofConfig (R := ℝ) (normalizedConfig4 (T3 q)) := by
  have hzero1 :
      ofConfig (R := ℝ) (normalizedConfig4 (face4_1 (phi3 q))) = 0 :=
    ofConfig_normalizedConfig4_zero_of_x_eq_neg_one _
      (phi3_face1_x_eq_neg_one q)
  have hT := ofConfig_normalizedConfig4_rho (R := ℝ) (face4_2 (phi3 q))
  change ofConfig (R := ℝ) (normalizedConfig4 (T3 q)) =
      -ofConfig (R := ℝ) (normalizedConfig4 (face4_2 (phi3 q))) at hT
  have hface2 :
      ofConfig (R := ℝ) (normalizedConfig4 (face4_2 (phi3 q))) =
        -ofConfig (R := ℝ) (normalizedConfig4 (T3 q)) := by
    rw [hT]
    simp
  rw [boundary_normalizedConfig5]
  simp [Fin.sum_univ_succ, face4At]
  rw [phi3_face0_eq_base, ← phi3_face1_eq_face3, hzero1]
  norm_num
  rw [hface2]
  module

/-- Integral form of the third special boundary identity. -/
theorem boundary_phi3_int (q : Adm3) :
    boundary ℤ 4 (ofConfig (R := ℤ) (normalizedConfig5 (phi3 q))) =
      (2 : ℤ) • ofConfig (R := ℤ) (normalizedConfig4 (base3 q)) -
        ofConfig (R := ℤ) (normalizedConfig4 (T3 q)) := by
  let cbad : Module ℤ 4 :=
    ofConfig (R := ℤ) (normalizedConfig4 (face4_1 (phi3 q)))
  let cbase : Module ℤ 4 :=
    ofConfig (R := ℤ) (normalizedConfig4 (base3 q))
  let ct : Module ℤ 4 :=
    ofConfig (R := ℤ) (normalizedConfig4 (T3 q))
  have htwo : (2 : ℤ) • cbad = 0 :=
    two_smul_ofConfig_normalizedConfig4_of_x_eq_neg_one _
      (phi3_face1_x_eq_neg_one q)
  have hT := ofConfig_normalizedConfig4_rho (R := ℤ) (face4_2 (phi3 q))
  change ct =
      -ofConfig (R := ℤ) (normalizedConfig4 (face4_2 (phi3 q))) at hT
  have hface2 :
      ofConfig (R := ℤ) (normalizedConfig4 (face4_2 (phi3 q))) = -ct := by
    rw [hT]
    simp
  rw [boundary_normalizedConfig5]
  simp [Fin.sum_univ_succ, face4At]
  rw [phi3_face0_eq_base, ← phi3_face1_eq_face3, hface2]
  norm_num
  change cbase + (-cbad + (-ct + (-cbad + cbase))) =
    (2 : ℤ) • cbase - ct
  calc
    cbase + (-cbad + (-ct + (-cbad + cbase))) =
        ((2 : ℤ) • cbase - ct) - (2 : ℤ) • cbad := by module
    _ = (2 : ℤ) • cbase - ct := by rw [htwo, sub_zero]

theorem boundary_phi4 (q : Adm4) :
    boundary ℝ 4 (ofConfig (R := ℝ) (normalizedConfig5 (phi4 q))) =
      (2 : ℝ) • ofConfig (R := ℝ) (normalizedConfig4 (base4 q)) -
        ofConfig (R := ℝ) (normalizedConfig4 (T4 q)) := by
  have hzero1 :
      ofConfig (R := ℝ) (normalizedConfig4 (face4_1 (phi4 q))) = 0 :=
    ofConfig_normalizedConfig4_zero_of_y_eq_one _
      (phi4_face1_y_eq_one q)
  have hT := ofConfig_normalizedConfig4_rho (R := ℝ) (face4_2 (phi4 q))
  change ofConfig (R := ℝ) (normalizedConfig4 (T4 q)) =
      -ofConfig (R := ℝ) (normalizedConfig4 (face4_2 (phi4 q))) at hT
  have hface2 :
      ofConfig (R := ℝ) (normalizedConfig4 (face4_2 (phi4 q))) =
        -ofConfig (R := ℝ) (normalizedConfig4 (T4 q)) := by
    rw [hT]
    simp
  rw [boundary_normalizedConfig5]
  simp [Fin.sum_univ_succ, face4At]
  rw [phi4_face0_eq_base, ← phi4_face1_eq_face3, hzero1]
  norm_num
  rw [hface2]
  module

/-- Integral form of the fourth special boundary identity. -/
theorem boundary_phi4_int (q : Adm4) :
    boundary ℤ 4 (ofConfig (R := ℤ) (normalizedConfig5 (phi4 q))) =
      (2 : ℤ) • ofConfig (R := ℤ) (normalizedConfig4 (base4 q)) -
        ofConfig (R := ℤ) (normalizedConfig4 (T4 q)) := by
  let cbad : Module ℤ 4 :=
    ofConfig (R := ℤ) (normalizedConfig4 (face4_1 (phi4 q)))
  let cbase : Module ℤ 4 :=
    ofConfig (R := ℤ) (normalizedConfig4 (base4 q))
  let ct : Module ℤ 4 :=
    ofConfig (R := ℤ) (normalizedConfig4 (T4 q))
  have htwo : (2 : ℤ) • cbad = 0 :=
    two_smul_ofConfig_normalizedConfig4_of_y_eq_one _
      (phi4_face1_y_eq_one q)
  have hT := ofConfig_normalizedConfig4_rho (R := ℤ) (face4_2 (phi4 q))
  change ct =
      -ofConfig (R := ℤ) (normalizedConfig4 (face4_2 (phi4 q))) at hT
  have hface2 :
      ofConfig (R := ℤ) (normalizedConfig4 (face4_2 (phi4 q))) = -ct := by
    rw [hT]
    simp
  rw [boundary_normalizedConfig5]
  simp [Fin.sum_univ_succ, face4At]
  rw [phi4_face0_eq_base, ← phi4_face1_eq_face3, hface2]
  norm_num
  change cbase + (-cbad + (-ct + (-cbad + cbase))) =
    (2 : ℤ) • cbase - ct
  calc
    cbase + (-cbad + (-ct + (-cbad + cbase))) =
        ((2 : ℤ) • cbase - ct) - (2 : ℤ) • cbad := by module
    _ = (2 : ℤ) • cbase - ct := by rw [htwo, sub_zero]

/-! ## Elementary correspondence edges -/

/-- The difference of the two five-point substitutions over one admissible
correspondence edge. -/
def edgeChain (p : UEdge) : Module ℝ 5 :=
  ofConfig (R := ℝ) (normalizedConfig5 (phi2 (edgeAdm2 p))) -
    ofConfig (R := ℝ) (normalizedConfig5 (phi1 (edgeAdm1 p)))

/-- The boundary of an elementary edge is source minus target. -/
theorem boundary_edgeChain (p : UEdge) :
    boundary ℝ 4 (edgeChain p) =
      ofConfig (R := ℝ) (normalizedConfig4 (edgeSource p)) -
        ofConfig (R := ℝ) (normalizedConfig4 (edgeTarget p)) := by
  rw [edgeChain, map_sub, boundary_phi2, boundary_phi1,
    T1_edgeAdm1, T2_edgeAdm2]
  change ((2 : ℝ) •
      ofConfig (R := ℝ) (normalizedConfig4 (edgeBase p)) -
        ofConfig (R := ℝ) (normalizedConfig4 (edgeTarget p))) -
      ((2 : ℝ) •
        ofConfig (R := ℝ) (normalizedConfig4 (edgeBase p)) -
          ofConfig (R := ℝ) (normalizedConfig4 (edgeSource p))) = _
  module

/-- An admissible discriminant canonically supplies the torus and genericity
data needed for an elementary edge. -/
def edgeOfDelta (a b : ℂ) (h : deltaU a b ≠ 0) : UEdge := by
  have ha : a ≠ 0 := by
    intro ha
    apply h
    simp [deltaU, ha]
  have hb : b ≠ 0 := by
    intro hb
    apply h
    simp [deltaU, hb]
  exact ⟨⟨⟨a, b⟩, ⟨ha, hb⟩⟩, h⟩

/-- A finite sum of elementary correspondence edges. -/
def edgeSum {n : ℕ} (e : Fin n → UEdge) : Module ℝ 5 :=
  ∑ i, edgeChain (e i)

/-- If the target of every edge agrees in orbit chains with the source of the
next cyclically indexed edge, their sum is a cycle. -/
theorem boundary_edgeSum_eq_zero_of_cyclic_matches {n : ℕ}
    (e : Fin n → UEdge)
    (hmatch : ∀ i,
      ofConfig (R := ℝ) (normalizedConfig4 (edgeTarget (e i))) =
        ofConfig (R := ℝ)
          (normalizedConfig4 (edgeSource (e (finRotate n i))))) :
    boundary ℝ 4 (edgeSum e) = 0 := by
  rw [edgeSum, map_sum]
  simp_rw [boundary_edgeChain, hmatch]
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  exact (Function.Bijective.sum_comp (finRotate n).bijective
    (fun i ↦ ofConfig (R := ℝ) (normalizedConfig4 (edgeSource (e i))))).symm

/-- The eight discriminants required by the paper's two-parameter period
cycle. -/
structure PeriodCycleAdmissible (A B : ℂ) : Prop where
  edge_one : deltaU (A ^ 2) B ≠ 0
  edge_two : deltaU (-A ^ 2 * B) B ≠ 0
  edge_three : deltaU (-(1 / B ^ 2)) A ≠ 0
  edge_four : deltaU (A / B ^ 2) A ≠ 0
  edge_five : deltaU (-(1 / A ^ 2)) (Complex.I / B) ≠ 0
  edge_six : deltaU (Complex.I / (A ^ 2 * B)) (Complex.I / B) ≠ 0
  edge_seven : deltaU (B ^ 2) (Complex.I / A) ≠ 0
  edge_eight : deltaU (-(B ^ 2 * Complex.I / A)) (Complex.I / A) ≠ 0

theorem PeriodCycleAdmissible.a_ne {A B : ℂ}
    (h : PeriodCycleAdmissible A B) : A ≠ 0 := by
  intro hA
  apply h.edge_one
  simp [deltaU, hA]

theorem PeriodCycleAdmissible.b_ne {A B : ℂ}
    (h : PeriodCycleAdmissible A B) : B ≠ 0 := by
  intro hB
  apply h.edge_one
  simp [deltaU, hB]

/-- The ordered eight elementary edges defining `Z(A,B)`. -/
def periodEdges (A B : ℂ) (h : PeriodCycleAdmissible A B) : Fin 8 → UEdge :=
  ![edgeOfDelta (A ^ 2) B h.edge_one,
    edgeOfDelta (-A ^ 2 * B) B h.edge_two,
    edgeOfDelta (-(1 / B ^ 2)) A h.edge_three,
    edgeOfDelta (A / B ^ 2) A h.edge_four,
    edgeOfDelta (-(1 / A ^ 2)) (Complex.I / B) h.edge_five,
    edgeOfDelta (Complex.I / (A ^ 2 * B)) (Complex.I / B) h.edge_six,
    edgeOfDelta (B ^ 2) (Complex.I / A) h.edge_seven,
    edgeOfDelta (-(B ^ 2 * Complex.I / A)) (Complex.I / A) h.edge_eight]

/-- The paper's eight-edge period chain. -/
def periodCycle (A B : ℂ) (h : PeriodCycleAdmissible A B) : Module ℝ 5 :=
  edgeSum (periodEdges A B h)

@[simp]
theorem edgeSource_edgeOfDelta_val (a b : ℂ) (h : deltaU a b ≠ 0) :
    (edgeSource (edgeOfDelta a b h)).1 = sourceUCoord ⟨a, b⟩ := rfl

@[simp]
theorem edgeTarget_edgeOfDelta_val (a b : ℂ) (h : deltaU a b ≠ 0) :
    (edgeTarget (edgeOfDelta a b h)).1 = targetUCoord ⟨a, b⟩ := rfl

theorem periodEdges_match01 (A B : ℂ) (h : PeriodCycleAdmissible A B) :
    edgeTarget (periodEdges A B h 0) = edgeSource (periodEdges A B h 1) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    simp [periodEdges, targetUCoord, sourceUCoord] <;>
    ring

theorem periodEdges_match12 (A B : ℂ) (h : PeriodCycleAdmissible A B) :
    cyclic (edgeTarget (periodEdges A B h 1)) =
      edgeSource (periodEdges A B h 2) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    simp [periodEdges, cyclic, cyclicCoord, targetUCoord, sourceUCoord,
      Complex.I_sq] <;>
    field_simp [h.a_ne, h.b_ne] <;>
    ring

theorem periodEdges_match23 (A B : ℂ) (h : PeriodCycleAdmissible A B) :
    edgeTarget (periodEdges A B h 2) = edgeSource (periodEdges A B h 3) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    simp [periodEdges, targetUCoord, sourceUCoord, Complex.I_sq] <;>
    field_simp [h.a_ne, h.b_ne] <;>
    ring

theorem periodEdges_match34 (A B : ℂ) (h : PeriodCycleAdmissible A B) :
    cyclic (edgeTarget (periodEdges A B h 3)) =
      edgeSource (periodEdges A B h 4) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    simp [periodEdges, cyclic, cyclicCoord, targetUCoord, sourceUCoord,
      Complex.I_sq] <;>
    field_simp [h.a_ne, h.b_ne, Complex.I_ne_zero] <;>
    simp only [Complex.I_sq] <;>
    ring

theorem periodEdges_match45 (A B : ℂ) (h : PeriodCycleAdmissible A B) :
    edgeTarget (periodEdges A B h 4) = edgeSource (periodEdges A B h 5) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    simp [periodEdges, targetUCoord, sourceUCoord, Complex.I_sq] <;>
    field_simp [h.a_ne, h.b_ne, Complex.I_ne_zero] <;>
    simp only [Complex.I_sq] <;>
    ring

theorem periodEdges_match56 (A B : ℂ) (h : PeriodCycleAdmissible A B) :
    cyclic (edgeTarget (periodEdges A B h 5)) =
      edgeSource (periodEdges A B h 6) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    simp [periodEdges, cyclic, cyclicCoord, targetUCoord, sourceUCoord,
      Complex.I_sq] <;>
    field_simp [h.a_ne, h.b_ne, Complex.I_ne_zero] <;>
    simp only [Complex.I_sq] <;>
    ring

theorem periodEdges_match67 (A B : ℂ) (h : PeriodCycleAdmissible A B) :
    edgeTarget (periodEdges A B h 6) = edgeSource (periodEdges A B h 7) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    simp [periodEdges, targetUCoord, sourceUCoord] <;>
    field_simp [h.a_ne, h.b_ne, Complex.I_ne_zero] <;>
    simp only [Complex.I_sq] <;>
    ring

theorem periodEdges_match70 (A B : ℂ) (h : PeriodCycleAdmissible A B) :
    cyclic (edgeTarget (periodEdges A B h 7)) =
      edgeSource (periodEdges A B h 0) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    simp [periodEdges, cyclic, cyclicCoord, targetUCoord, sourceUCoord,
      Complex.I_sq] <;>
    field_simp [h.a_ne, h.b_ne, Complex.I_ne_zero] <;>
    simp only [Complex.I_sq] <;>
    ring

theorem ofConfig_eq_of_cyclic_eq {x y : U4} (hxy : cyclic x = y) :
    ofConfig (R := ℝ) (normalizedConfig4 x) =
      ofConfig (R := ℝ) (normalizedConfig4 y) := by
  rw [← hxy]
  exact (ofConfig_normalizedConfig4_cyclic (R := ℝ) x).symm

theorem periodEdges_cyclic_matches (A B : ℂ)
    (h : PeriodCycleAdmissible A B) :
    ∀ i,
      ofConfig (R := ℝ)
          (normalizedConfig4 (edgeTarget (periodEdges A B h i))) =
        ofConfig (R := ℝ)
          (normalizedConfig4
            (edgeSource (periodEdges A B h (finRotate 8 i)))) := by
  intro i
  fin_cases i
  · simpa [finRotate_succ_apply] using congrArg
      (fun q : U4 ↦ ofConfig (R := ℝ) (normalizedConfig4 q))
      (periodEdges_match01 A B h)
  · simpa [finRotate_succ_apply] using
      ofConfig_eq_of_cyclic_eq (periodEdges_match12 A B h)
  · simpa [finRotate_succ_apply] using congrArg
      (fun q : U4 ↦ ofConfig (R := ℝ) (normalizedConfig4 q))
      (periodEdges_match23 A B h)
  · simpa [finRotate_succ_apply] using
      ofConfig_eq_of_cyclic_eq (periodEdges_match34 A B h)
  · simpa [finRotate_succ_apply] using congrArg
      (fun q : U4 ↦ ofConfig (R := ℝ) (normalizedConfig4 q))
      (periodEdges_match45 A B h)
  · simpa [finRotate_succ_apply] using
      ofConfig_eq_of_cyclic_eq (periodEdges_match56 A B h)
  · simpa [finRotate_succ_apply] using congrArg
      (fun q : U4 ↦ ofConfig (R := ℝ) (normalizedConfig4 q))
      (periodEdges_match67 A B h)
  · simpa [finRotate_succ_apply] using
      ofConfig_eq_of_cyclic_eq (periodEdges_match70 A B h)

/-- The eight-edge period chain is a genuine orbit-chain cycle. -/
theorem boundary_periodCycle (A B : ℂ) (h : PeriodCycleAdmissible A B) :
    boundary ℝ 4 (periodCycle A B h) = 0 := by
  exact boundary_edgeSum_eq_zero_of_cyclic_matches
    (periodEdges A B h) (periodEdges_cyclic_matches A B h)

/-! ## Evaluation of the affine cocycle on the displayed presentation -/

/-- Evaluation of the affine cocycle on one elementary edge presentation. -/
def edgeCocycleValue (p : UEdge) : ℂ :=
  reducedR (matrix5 (phi2 (edgeAdm2 p)).1) -
    reducedR (matrix5 (phi1 (edgeAdm1 p)).1)

theorem edgeCocycleValue_eq_specialG (p : UEdge) :
    edgeCocycleValue p = specialG p.1.1.x p.1.1.y := by
  change reducedR (matrix5 (Phi2Coord p.1.1)) -
      reducedR (matrix5 (Phi1Coord p.1.1)) =
        specialG p.1.1.x p.1.1.y
  have h2 : reducedR (matrix5 (Phi2Coord p.1.1)) =
      specialF2 p.1.1.x p.1.1.y := by
    have h := reducedR_Phi2 (edgeAdm2 p)
    change reducedR (matrix5 (Phi2Coord p.1.1)) =
      specialF2 p.1.1.x p.1.1.y at h
    exact h
  have h1 : reducedR (matrix5 (Phi1Coord p.1.1)) =
      specialF1 p.1.1.x p.1.1.y := by
    have h := reducedR_Phi1 (edgeAdm1 p)
    change reducedR (matrix5 (Phi1Coord p.1.1)) =
      specialF1 p.1.1.x p.1.1.y at h
    exact h
  rw [h2, h1]
  rfl

/-- Evaluation of the affine cocycle on the eight displayed facets. -/
def periodCycleValue (A B : ℂ) (h : PeriodCycleAdmissible A B) : ℂ :=
  ∑ i, edgeCocycleValue (periodEdges A B h i)

theorem periodCycleValue_eq (A B : ℂ) (h : PeriodCycleAdmissible A B) :
    periodCycleValue A B h =
      specialQ (-A ^ 2) B + specialQ (1 / B ^ 2) A +
        specialQ (1 / A ^ 2) (Complex.I / B) +
          specialQ (-B ^ 2) (Complex.I / A) := by
  have h2 : (B ^ 2)⁻¹ * A = A / B ^ 2 := by
    field_simp [h.b_ne]
  have h6 : (A ^ 2)⁻¹ * (Complex.I / B) =
      Complex.I / (A ^ 2 * B) := by
    field_simp [h.a_ne, h.b_ne]
  have h8 : (-B ^ 2) * (Complex.I / A) =
      -(B ^ 2 * Complex.I / A) := by
    field_simp [h.a_ne]
  have hAB : -(A ^ 2 * B) = -A ^ 2 * B := by
    ring
  simp [periodCycleValue, Fin.sum_univ_succ, periodEdges,
    edgeCocycleValue_eq_specialG, edgeOfDelta]
  unfold specialQ
  rw [h2, h6, h8, hAB]
  simp only [neg_neg]
  abel

/-! ## The displayed raw presentation and its mass -/

/-- The raw two-facet presentation of an elementary edge. -/
def rawEdgeChain (p : UEdge) : Raw ℝ 5 :=
  generator (normalizedConfig5 (phi2 (edgeAdm2 p))) -
    generator (normalizedConfig5 (phi1 (edgeAdm1 p)))

@[simp]
theorem mkQ_rawEdgeChain (p : UEdge) :
    (relations ℝ 5).mkQ (rawEdgeChain p) = edgeChain p := by
  simp [rawEdgeChain, edgeChain, ofConfig]

theorem rawMass_rawEdgeChain_le_two (p : UEdge) :
    rawMass (rawEdgeChain p) ≤ 2 := by
  exact (rawMass_sub_le _ _).trans (by norm_num)

/-- The sixteen-facet raw presentation of `Z(A,B)`. -/
def rawPeriodCycle (A B : ℂ) (h : PeriodCycleAdmissible A B) : Raw ℝ 5 :=
  ∑ i, rawEdgeChain (periodEdges A B h i)

@[simp]
theorem mkQ_rawPeriodCycle (A B : ℂ) (h : PeriodCycleAdmissible A B) :
    (relations ℝ 5).mkQ (rawPeriodCycle A B h) = periodCycle A B h := by
  rw [rawPeriodCycle, periodCycle, edgeSum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact mkQ_rawEdgeChain _

theorem rawMass_rawPeriodCycle_le_sixteen (A B : ℂ)
    (h : PeriodCycleAdmissible A B) :
    rawMass (rawPeriodCycle A B h) ≤ 16 := by
  calc
    rawMass (rawPeriodCycle A B h) ≤
        ∑ i : Fin 8, rawMass (rawEdgeChain (periodEdges A B h i)) := by
      simpa [rawPeriodCycle] using
        rawMass_sum_le (Finset.univ)
          (fun i : Fin 8 ↦ rawEdgeChain (periodEdges A B h i))
    _ ≤ ∑ _i : Fin 8, (2 : ℝ) := by
      exact Finset.sum_le_sum fun i _ ↦ rawMass_rawEdgeChain_le_two _
    _ = 16 := by norm_num

/-- The quotient `ℓ¹` mass of the period cycle is at most sixteen, counted
before any cancellation in the orbit quotient. -/
theorem quotientL1_periodCycle_le_sixteen (A B : ℂ)
    (h : PeriodCycleAdmissible A B) :
    quotientL1 (periodCycle A B h) ≤ 16 := by
  rw [← mkQ_rawPeriodCycle]
  exact (quotientL1_mkQ_le (rawPeriodCycle A B h)).trans
    (rawMass_rawPeriodCycle_le_sixteen A B h)

end

end OrbitChain

end Sp4
