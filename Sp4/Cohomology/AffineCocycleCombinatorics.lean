import Sp4.Cohomology.AffineCocycle
import Sp4.Pfaffian.Operators

/-!
# Finite alternation identities for the affine cocycle

This module proves the signed `S₆` cancellation used by the six-point
coboundary.  It is independent of the coordinate realization.
-/

namespace Sp4.AffineCocycle

open scoped BigOperators
open Pfaffian

def lastBlockPerm (τ : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 6) :=
  τ.viaFintypeEmbedding (Fin.natAddEmb 3)

@[simp] theorem lastBlockPerm_zero (τ : Equiv.Perm (Fin 3)) :
    lastBlockPerm τ 0 = 0 := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  intro hx
  rcases hx with ⟨x, hx⟩
  have hval := congrArg Fin.val hx
  change 3 + x.val = 0 at hval
  omega

@[simp] theorem lastBlockPerm_one (τ : Equiv.Perm (Fin 3)) :
    lastBlockPerm τ 1 = 1 := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  intro hx
  rcases hx with ⟨x, hx⟩
  have hval := congrArg Fin.val hx
  change 3 + x.val = 1 at hval
  omega

@[simp] theorem lastBlockPerm_two (τ : Equiv.Perm (Fin 3)) :
    lastBlockPerm τ 2 = 2 := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  intro hx
  rcases hx with ⟨x, hx⟩
  have hval := congrArg Fin.val hx
  change 3 + x.val = 2 at hval
  omega

@[simp] theorem lastBlockPerm_three (τ : Equiv.Perm (Fin 3)) :
    lastBlockPerm τ 3 = Fin.natAdd 3 (τ 0) := by
  exact Equiv.Perm.viaFintypeEmbedding_apply_image τ (Fin.natAddEmb 3) 0

@[simp] theorem lastBlockPerm_four (τ : Equiv.Perm (Fin 3)) :
    lastBlockPerm τ 4 = Fin.natAdd 3 (τ 1) := by
  exact Equiv.Perm.viaFintypeEmbedding_apply_image τ (Fin.natAddEmb 3) 1

@[simp] theorem lastBlockPerm_five (τ : Equiv.Perm (Fin 3)) :
    lastBlockPerm τ 5 = Fin.natAdd 3 (τ 2) := by
  exact Equiv.Perm.viaFintypeEmbedding_apply_image τ (Fin.natAddEmb 3) 2

@[simp] theorem sign_lastBlockPerm (τ : Equiv.Perm (Fin 3)) :
    Equiv.Perm.sign (lastBlockPerm τ) = Equiv.Perm.sign τ := by
  exact Equiv.Perm.viaFintypeEmbedding_sign τ (Fin.natAddEmb 3)

private theorem decomposeFinSymm_apply' {n : ℕ} (p : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) (i : Fin (n + 1)) :
    Equiv.Perm.decomposeFin.symm (p, e) i =
      Fin.cases p (fun x => Equiv.swap 0 p (e x).succ) i := by
  refine Fin.cases ?_ (fun x => ?_) i
  · exact Equiv.Perm.decomposeFin_symm_apply_zero p e
  · exact Equiv.Perm.decomposeFin_symm_apply_succ e p x

private theorem finCasesOne' {n : ℕ} {C : Sort*} (z : C) (s : Fin (n + 1) → C) :
    Fin.cases z s (1 : Fin (n + 2)) = s 0 := by
  rw [show (1 : Fin (n + 2)) = Fin.succ 0 by rfl, Fin.cases_succ]

private theorem finCasesTwo' {n : ℕ} {C : Sort*} (z : C) (s : Fin (n + 2) → C) :
    Fin.cases z s (2 : Fin (n + 3)) = s 1 := by
  rw [show (2 : Fin (n + 3)) = Fin.succ 1 by rfl, Fin.cases_succ]

private theorem finCasesThree' {n : ℕ} {C : Sort*} (z : C) (s : Fin (n + 3) → C) :
    Fin.cases z s (3 : Fin (n + 4)) = s 2 := by
  rw [show (3 : Fin (n + 4)) = Fin.succ 2 by rfl, Fin.cases_succ]

private theorem finCasesFour' {n : ℕ} {C : Sort*} (z : C) (s : Fin (n + 4) → C) :
    Fin.cases z s (4 : Fin (n + 5)) = s 3 := by
  rw [show (4 : Fin (n + 5)) = Fin.succ 3 by rfl, Fin.cases_succ]

private theorem finCasesFive' {n : ℕ} {C : Sort*} (z : C) (s : Fin (n + 5) → C) :
    Fin.cases z s (5 : Fin (n + 6)) = s 4 := by
  rw [show (5 : Fin (n + 6)) = Fin.succ 4 by rfl, Fin.cases_succ]

theorem inner_lastBlock_sum
    (r : Fin 6 → Fin 6 → Fin 6 → Fin 6 → Fin 6 → ℂ)
    (hanti : ∀ i j k l m, r i j k l m = -r i j k m l)
    (σ : Equiv.Perm (Fin 6)) :
    (∑ τ : Equiv.Perm (Fin 3),
      (Equiv.Perm.sign τ : ℂ) *
        r (σ (lastBlockPerm τ 0)) (σ (lastBlockPerm τ 1))
          (σ (lastBlockPerm τ 2)) (σ (lastBlockPerm τ 3))
          (σ (lastBlockPerm τ 4))) =
      2 * (r (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) -
        r (σ 0) (σ 1) (σ 2) (σ 3) (σ 5) +
        r (σ 0) (σ 1) (σ 2) (σ 4) (σ 5)) := by
  simp_rw [Finset.univ_perm_fin_succ, Finset.sum_map,
    ← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [Finset.univ_perm_fin_succ, Finset.sum_map,
    ← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [Finset.univ_perm_fin_succ, Finset.sum_map,
    ← Finset.univ_product_univ, Finset.sum_product]
  simp [Fin.sum_univ_succ,
    decomposeFinSymm_apply', finCasesOne', Equiv.swap_apply_def]
  rw [hanti (σ 0) (σ 1) (σ 2) (σ 4) (σ 3),
    hanti (σ 0) (σ 1) (σ 2) (σ 5) (σ 4),
    hanti (σ 0) (σ 1) (σ 2) (σ 5) (σ 3)]
  ring

def permuteInputsRight (τ : Equiv.Perm (Fin 6)) :
    Equiv.Perm (Equiv.Perm (Fin 6)) where
  toFun σ := τ.trans σ
  invFun σ := τ.symm.trans σ
  left_inv σ := by
    ext i
    simp
  right_inv σ := by
    ext i
    simp

def fullAlternatingSum6
    (r : Fin 6 → Fin 6 → Fin 6 → Fin 6 → Fin 6 → ℂ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin 6), (Equiv.Perm.sign σ : ℂ) *
    r (σ 0) (σ 1) (σ 2) (σ 3) (σ 4)

theorem full_reindex
    (r : Fin 6 → Fin 6 → Fin 6 → Fin 6 → Fin 6 → ℂ)
    (τ : Equiv.Perm (Fin 6)) :
    (∑ σ : Equiv.Perm (Fin 6),
      (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        r (σ (τ 0)) (σ (τ 1)) (σ (τ 2)) (σ (τ 3)) (σ (τ 4))) =
      fullAlternatingSum6 r := by
  let e := permuteInputsRight τ
  let F : Equiv.Perm (Fin 6) → ℂ := fun ρ =>
    (Equiv.Perm.sign ρ : ℂ) * r (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4)
  calc
    _ = ∑ σ : Equiv.Perm (Fin 6), F (e σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      simp [F, e, permuteInputsRight, Equiv.Perm.sign_trans]
    _ = ∑ ρ : Equiv.Perm (Fin 6), F ρ := Equiv.sum_comp e F
    _ = fullAlternatingSum6 r := rfl

theorem lastBlock_reindex
    (r : Fin 6 → Fin 6 → Fin 6 → Fin 6 → Fin 6 → ℂ)
    (τ : Equiv.Perm (Fin 3)) :
    (∑ σ : Equiv.Perm (Fin 6),
      (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        r (σ (lastBlockPerm τ 0)) (σ (lastBlockPerm τ 1))
          (σ (lastBlockPerm τ 2)) (σ (lastBlockPerm τ 3))
          (σ (lastBlockPerm τ 4))) = fullAlternatingSum6 r := by
  let e := permuteInputsRight (lastBlockPerm τ)
  let F : Equiv.Perm (Fin 6) → ℂ := fun ρ =>
    (Equiv.Perm.sign ρ : ℂ) * r (ρ 0) (ρ 1) (ρ 2) (ρ 3) (ρ 4)
  calc
    _ = ∑ σ : Equiv.Perm (Fin 6), F (e σ) := by
      apply Finset.sum_congr rfl
      intro σ _
      simp [F, e, permuteInputsRight, Equiv.Perm.sign_trans]
    _ = ∑ ρ : Equiv.Perm (Fin 6), F ρ := Equiv.sum_comp e F
    _ = fullAlternatingSum6 r := rfl

theorem fullAlternatingSum6_eq_zero
    (r : Fin 6 → Fin 6 → Fin 6 → Fin 6 → Fin 6 → ℂ)
    (hanti : ∀ i j k l m, r i j k l m = -r i j k m l)
    (htriangle : ∀ σ : Equiv.Perm (Fin 6),
      r (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) -
        r (σ 0) (σ 1) (σ 2) (σ 3) (σ 5) +
        r (σ 0) (σ 1) (σ 2) (σ 4) (σ 5) = 0) :
    fullAlternatingSum6 r = 0 := by
  have hdouble :
      (∑ σ : Equiv.Perm (Fin 6), (Equiv.Perm.sign σ : ℂ) *
        ∑ τ : Equiv.Perm (Fin 3), (Equiv.Perm.sign τ : ℂ) *
          r (σ (lastBlockPerm τ 0)) (σ (lastBlockPerm τ 1))
            (σ (lastBlockPerm τ 2)) (σ (lastBlockPerm τ 3))
            (σ (lastBlockPerm τ 4))) = 0 := by
    apply Finset.sum_eq_zero
    intro σ _
    rw [inner_lastBlock_sum r hanti σ, htriangle σ]
    simp
  simp_rw [Finset.mul_sum] at hdouble
  rw [Finset.sum_comm] at hdouble
  simp_rw [← mul_assoc] at hdouble
  simp_rw [lastBlock_reindex r] at hdouble
  norm_num at hdouble
  exact hdouble

def fullAlternatingTailSum6
    (r : Fin 6 → Fin 6 → Fin 6 → Fin 6 → Fin 6 → ℂ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin 6), (Equiv.Perm.sign σ : ℂ) *
    r (σ 1) (σ 2) (σ 3) (σ 4) (σ 5)

theorem fullAlternatingTailSum6_eq_zero
    (r : Fin 6 → Fin 6 → Fin 6 → Fin 6 → Fin 6 → ℂ)
    (hfull : fullAlternatingSum6 r = 0) :
    fullAlternatingTailSum6 r = 0 := by
  have h := full_reindex r (finRotate 6)
  rw [hfull] at h
  simpa [fullAlternatingTailSum6, finRotate_of_lt] using h

def reindexMatrix6 (A : Matrix (Fin 6) (Fin 6) ℂ)
    (σ : Equiv.Perm (Fin 6)) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => A (σ i) (σ j)

theorem isSkew_reindexMatrix6 {A : Matrix (Fin 6) (Fin 6) ℂ}
    (hA : IsSkew A) (σ : Equiv.Perm (Fin 6)) :
    IsSkew (reindexMatrix6 A σ) := by
  intro i j
  exact hA (σ i) (σ j)

set_option maxHeartbeats 4000000 in
theorem pfaffian6_reindex_swap (A : Matrix (Fin 6) (Fin 6) ℂ)
    (hA : IsSkew A) (i j : Fin 6) (hij : i ≠ j) :
    pfaffian6 (reindexMatrix6 A (Equiv.swap i j)) = -pfaffian6 A := by
  have h10 := hA 0 1
  have h20 := hA 0 2
  have h30 := hA 0 3
  have h40 := hA 0 4
  have h50 := hA 0 5
  have h21 := hA 1 2
  have h31 := hA 1 3
  have h41 := hA 1 4
  have h51 := hA 1 5
  have h32 := hA 2 3
  have h42 := hA 2 4
  have h52 := hA 2 5
  have h43 := hA 3 4
  have h53 := hA 3 5
  have h54 := hA 4 5
  clear hA
  fin_cases i <;> fin_cases j <;>
    simp_all [pfaffian6, reindexMatrix6, Equiv.swap_apply_def] <;>
    ring

theorem reindexMatrix6_mul (A : Matrix (Fin 6) (Fin 6) ℂ)
    (σ τ : Equiv.Perm (Fin 6)) :
    reindexMatrix6 A (σ * τ) = reindexMatrix6 (reindexMatrix6 A σ) τ := by
  ext i j
  rfl

theorem pfaffian6_reindex (A : Matrix (Fin 6) (Fin 6) ℂ)
    (hA : IsSkew A) (σ : Equiv.Perm (Fin 6)) :
    pfaffian6 (reindexMatrix6 A σ) =
      (Equiv.Perm.sign σ : ℂ) * pfaffian6 A := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one =>
      have hreindex : reindexMatrix6 A 1 = A := by
        ext i j
        simp [reindexMatrix6]
      rw [hreindex]
      simp
  | mul_swap σ i j hij ih =>
      rw [reindexMatrix6_mul,
        pfaffian6_reindex_swap (reindexMatrix6 A σ)
          (isSkew_reindexMatrix6 hA σ) i j hij,
        ih]
      simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]

theorem bracket_plucker_standard (A : Matrix (Fin 6) (Fin 6) ℂ) :
    orderedBracket A 0 1 3 4 * orderedBracket A 0 1 2 5 -
        orderedBracket A 0 1 3 5 * orderedBracket A 0 1 2 4 +
        orderedBracket A 0 1 4 5 * orderedBracket A 0 1 2 3 =
      A 0 1 * pfaffian6 A := by
  simp only [orderedBracket, pfaffian6]
  ring

def deletedIndex6 (skip : Fin 6) (i : Fin 5) : Fin 6 :=
  skip.succAbove i

def rawFaceSum6
    (r : Fin 6 → Fin 6 → Fin 6 → Fin 6 → Fin 6 → ℂ) (skip : Fin 6) : ℂ :=
  ∑ σ : Equiv.Perm (Fin 5), (Equiv.Perm.sign σ : ℂ) *
    r (deletedIndex6 skip (σ 0)) (deletedIndex6 skip (σ 1))
      (deletedIndex6 skip (σ 2)) (deletedIndex6 skip (σ 3))
      (deletedIndex6 skip (σ 4))

def rawBoundarySum6
    (r : Fin 6 → Fin 6 → Fin 6 → Fin 6 → Fin 6 → ℂ) : ℂ :=
  ∑ skip : Fin 6, ((-1 : ℂ) ^ skip.val) * rawFaceSum6 r skip

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
theorem rawBoundarySum6_eq_fullAlternatingTailSum6
    (r : Fin 6 → Fin 6 → Fin 6 → Fin 6 → Fin 6 → ℂ) :
    rawBoundarySum6 r = fullAlternatingTailSum6 r := by
  simp only [rawBoundarySum6, rawFaceSum6, fullAlternatingTailSum6,
    Fin.sum_univ_succ]
  simp_rw [Finset.univ_perm_fin_succ, Finset.sum_map,
    ← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [Finset.univ_perm_fin_succ, Finset.sum_map,
    ← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [Finset.univ_perm_fin_succ, Finset.sum_map,
    ← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [Finset.univ_perm_fin_succ, Finset.sum_map,
    ← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [Finset.univ_perm_fin_succ, Finset.sum_map,
    ← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [Finset.univ_perm_fin_succ, Finset.sum_map,
    ← Finset.univ_product_univ, Finset.sum_product]
  simp [Fin.sum_univ_succ, deletedIndex6, decomposeFinSymm_apply',
    finCasesOne', finCasesTwo', finCasesThree', finCasesFour', finCasesFive',
    Fin.succAbove, Equiv.swap_apply_def]
  ring

end Sp4.AffineCocycle
