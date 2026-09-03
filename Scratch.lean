import Sp4.Chains.Orbit
import Sp4.Cohomology.AffineCocycleIdentity

open scoped BigOperators Matrix

namespace Sp4
namespace Scratch

open Pfaffian AffineCocycle

#check Matrix.det_succ_row
#check Matrix.rank_submatrix_le
#check LinearMap.finrank_range_add_finrank_ker
#check Submodule.one_le_finrank_iff
#check Matrix.rank
#check Matrix.mulVecLin_apply
#check Function.Injective.ne
#check Fin.succAbove_right_injective

set_option maxRecDepth 100000 in
theorem det_skew_four_eq_pfaffian_sq
    (A : Matrix (Fin 4) (Fin 4) ℂ) (hA : IsSkew A) :
    A.det = pfaffian4 A ^ 2 := by
  have h00 : A 0 0 = 0 := by
    have h := hA 0 0
    exact CharZero.eq_neg_self_iff.mp h
  have h11 : A 1 1 = 0 := by
    have h := hA 1 1
    exact CharZero.eq_neg_self_iff.mp h
  have h22 : A 2 2 = 0 := by
    have h := hA 2 2
    exact CharZero.eq_neg_self_iff.mp h
  have h33 : A 3 3 = 0 := by
    have h := hA 3 3
    exact CharZero.eq_neg_self_iff.mp h
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
  simp [Matrix.det_fin_three, Fin.sum_univ_succ,
    Fin.succAbove, pfaffian4]
  ring

def kernel5 (q : Coord5) : Fin 5 → ℂ :=
  ![p0 q, -p1 q, p2 q, -p3 q, p4 q]

theorem matrix5_mulVec_kernel5 (q : Coord5) :
    matrix5 q *ᵥ kernel5 q = 0 := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, kernel5, matrix5,
      p0, p1, p2, p3, p4, Fin.sum_univ_succ] <;>
    ring

theorem matrix5_rank_le_four (q : U5) : (matrix5 q.1).rank ≤ 4 := by
  let k : Fin 5 → ℂ := kernel5 q.1
  have hk_mem : k ∈ LinearMap.ker (matrix5 q.1).mulVecLin := by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact matrix5_mulVec_kernel5 q.1
  have hk_ne : k ≠ 0 := by
    intro h
    have h4 := congr_fun h 4
    change p4 q.1 = 0 at h4
    exact q.2.p4_ne h4
  have hker : (LinearMap.ker (matrix5 q.1).mulVecLin) ≠ ⊥ := by
    intro hbot
    have : k ∈ (⊥ : Submodule ℂ (Fin 5 → ℂ)) := hbot ▸ hk_mem
    exact hk_ne (by simpa using this)
  have hone : 1 ≤ Module.finrank ℂ (LinearMap.ker (matrix5 q.1).mulVecLin) :=
    Submodule.one_le_finrank_iff.mpr hker
  have hnull := LinearMap.finrank_range_add_finrank_ker
    (matrix5 q.1).mulVecLin
  have hnull' : (matrix5 q.1).rank +
      Module.finrank ℂ (LinearMap.ker (matrix5 q.1).mulVecLin) = 5 := by
    simpa [Matrix.rank] using hnull
  omega

theorem matrix4_isSkew (q : Coord4) : IsSkew (matrix4 q) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [matrix4]

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

end Scratch
end Sp4

namespace Sp4
namespace Scratch2

open scoped Matrix
open Pfaffian AffineCocycle

theorem isSkew_diagonalCongruence {n : Type*} {A : Matrix n n ℂ}
    (hA : IsSkew A) (d : n → ℂ) :
    IsSkew (diagonalCongruence d A) := by
  intro i j
  rw [diagonalCongruence, diagonalCongruence, hA i j]
  ring

theorem chi4_diagonalCongruence (A : Matrix (Fin 4) (Fin 4) ℂ)
    (d : Fin 4 → ℂˣ) (h12 : A 1 2 ≠ 0) (h03 : A 0 3 ≠ 0) :
    chi4 (diagonalCongruence (fun i ↦ (d i : ℂ)) A) = chi4 A := by
  apply Coord4.ext <;>
    simp [chi4, diagonalCongruence] <;>
    field_simp [Units.ne_zero, h12, h03] <;>
    ring

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
  exact (Sp4.Scratch.matrix5_isAdmissible q).offDiagonal_ne _ _
    (Fin.succAbove_right_injective.ne hab)

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
    exact AffineCocycle.matrix5_isSkew q.1 (i.succAbove a) (i.succAbove b)
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

end Scratch2
end Sp4
