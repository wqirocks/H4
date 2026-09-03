import Sp4.Chains.Orbit

/-!
# Full permutation alternation on homogeneous cochains

This file contains the finite combinatorics behind the fact that homogeneous
alternation is a chain map.  In particular, it is independent of the
Burger--Monod bounded homotopy: the latter supplies a bounded normal form,
whereas commutation of alternation with deletion is proved here.
-/

namespace Sp4
namespace CochainAlternation

noncomputable section

open scoped BigOperators
open OrbitChain

universe u

/-! ## A permutation and its deleted permutation -/

/-- Assemble a permutation which sends the distinguished source `j` to `i`
and acts by `τ` on their order-preserving complements. -/
def assemblePermAt {n : ℕ} (j i : Fin (n + 1))
    (τ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' j).trans
    ((Equiv.optionCongr τ).trans (finSuccEquiv' i).symm)

@[simp]
theorem assemblePermAt_fixed {n : ℕ} (j i : Fin (n + 1))
    (τ : Equiv.Perm (Fin n)) : assemblePermAt j i τ j = i := by
  simp [assemblePermAt, finSuccEquiv'_at, finSuccEquiv'_symm_none]

@[simp]
theorem assemblePermAt_succAbove {n : ℕ} (j i : Fin (n + 1))
    (τ : Equiv.Perm (Fin n)) (k : Fin n) :
    assemblePermAt j i τ (j.succAbove k) = i.succAbove (τ k) := by
  simp [assemblePermAt, finSuccEquiv'_succAbove, finSuccEquiv'_symm_some]

@[simp]
theorem deletePerm_assemblePermAt {n : ℕ} (j i : Fin (n + 1))
    (τ : Equiv.Perm (Fin n)) :
    deletePerm (assemblePermAt j i τ) j = τ := by
  apply Equiv.ext
  intro k
  apply Fin.succAbove_right_injective (p := i)
  simpa only [assemblePermAt_fixed, assemblePermAt_succAbove] using
    (succAbove_deletePerm (assemblePermAt j i τ) j k)

/-- Decompose a permutation into the image of one distinguished vertex and
the induced permutation after deleting that vertex. -/
def decomposePermAt {n : ℕ} (j : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 1)) ≃
      Fin (n + 1) × Equiv.Perm (Fin n) where
  toFun σ := (σ j, deletePerm σ j)
  invFun p := assemblePermAt j p.1 p.2
  left_inv σ := by
    apply Equiv.ext
    intro a
    by_cases ha : a = j
    · subst a
      exact assemblePermAt_fixed j (σ j) (deletePerm σ j)
    · obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq ha
      rw [← hk, assemblePermAt_succAbove, succAbove_deletePerm]
  right_inv p := by
    apply Prod.ext
    · exact assemblePermAt_fixed j p.1 p.2
    · exact deletePerm_assemblePermAt j p.1 p.2

@[simp]
theorem decomposePermAt_fst {n : ℕ} (j : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (decomposePermAt j σ).1 = σ j :=
  rfl

@[simp]
theorem decomposePermAt_snd {n : ℕ} (j : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    (decomposePermAt j σ).2 = deletePerm σ j :=
  rfl

/-! ## Alternation -/

variable {X : Type u}

/-- The unnormalized signed sum over all vertex permutations. -/
def alternatingSum (n : ℕ) (f : FinTuple X n → ℝ) :
    FinTuple X n → ℝ := fun x ↦
  ∑ σ : Equiv.Perm (Fin n),
    permSign ℝ σ * f (FinTuple.permute σ x)

/-- Full homogeneous alternation, normalized by `n!`. -/
def alternation (n : ℕ) (f : FinTuple X n → ℝ) :
    FinTuple X n → ℝ := fun x ↦
  ((Nat.factorial n : ℝ)⁻¹) * alternatingSum n f x

/-- The alternating deletion coboundary on ordinary functions. -/
def coboundary (n : ℕ) (f : FinTuple X n → ℝ) :
    FinTuple X (n + 1) → ℝ := fun x ↦
  ∑ i : Fin (n + 1), (-1 : ℝ) ^ i.1 * f (FinTuple.delete i x)

@[simp]
theorem alternatingSum_apply (n : ℕ) (f : FinTuple X n → ℝ)
    (x : FinTuple X n) :
    alternatingSum n f x =
      ∑ σ : Equiv.Perm (Fin n),
        permSign ℝ σ * f (FinTuple.permute σ x) :=
  rfl

@[simp]
theorem alternation_apply (n : ℕ) (f : FinTuple X n → ℝ)
    (x : FinTuple X n) :
    alternation n f x =
      ((Nat.factorial n : ℝ)⁻¹) * alternatingSum n f x :=
  rfl

@[simp]
theorem coboundary_apply (n : ℕ) (f : FinTuple X n → ℝ)
    (x : FinTuple X (n + 1)) :
    coboundary n f x =
      ∑ i : Fin (n + 1),
        (-1 : ℝ) ^ i.1 * f (FinTuple.delete i x) :=
  rfl

/-- The incidence-sign identity in the orientation needed for cochains. -/
theorem deletePerm_incidence_sign_cast_cochain {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    (-1 : ℝ) ^ (σ i).val * permSign ℝ (deletePerm σ i) =
      (-1 : ℝ) ^ i.val * permSign ℝ σ := by
  have h := congrArg (Int.castRingHom ℝ) (deletePerm_incidence_sign σ i)
  simpa [permSign] using h

/-- For a fixed deleted source vertex, permutations are reindexed by the
image vertex and the permutation induced on the complementary tuple. -/
theorem sum_permutations_delete_at (n : ℕ) (f : FinTuple X n → ℝ)
    (x : FinTuple X (n + 1)) (j : Fin (n + 1)) :
    (∑ σ : Equiv.Perm (Fin (n + 1)),
        permSign ℝ σ * ((-1 : ℝ) ^ j.val *
          f (FinTuple.delete j (FinTuple.permute σ x)))) =
      ∑ p : Fin (n + 1) × Equiv.Perm (Fin n),
        (-1 : ℝ) ^ p.1.val * permSign ℝ p.2 *
          f (FinTuple.permute p.2 (FinTuple.delete p.1 x)) := by
  classical
  refine Fintype.sum_equiv (decomposePermAt j) _ _ ?_
  intro σ
  rw [delete_permute]
  simp only [decomposePermAt_fst, decomposePermAt_snd]
  rw [deletePerm_incidence_sign_cast_cochain]
  ring

/-- The unnormalized alternation commutes with coboundary up to the number
of possible source vertices.  This is the factorial which normalization
removes. -/
theorem alternatingSum_coboundary (n : ℕ) (f : FinTuple X n → ℝ)
    (x : FinTuple X (n + 1)) :
    alternatingSum (n + 1) (coboundary n f) x =
      (n + 1 : ℝ) * coboundary n (alternatingSum n f) x := by
  classical
  change
    (∑ σ : Equiv.Perm (Fin (n + 1)),
        permSign ℝ σ *
          ∑ j : Fin (n + 1), (-1 : ℝ) ^ j.val *
            f (FinTuple.delete j (FinTuple.permute σ x))) = _
  calc
    (∑ σ : Equiv.Perm (Fin (n + 1)),
        permSign ℝ σ *
          ∑ j : Fin (n + 1), (-1 : ℝ) ^ j.val *
            f (FinTuple.delete j (FinTuple.permute σ x))) =
        ∑ σ : Equiv.Perm (Fin (n + 1)),
          ∑ j : Fin (n + 1), permSign ℝ σ *
            ((-1 : ℝ) ^ j.val *
              f (FinTuple.delete j (FinTuple.permute σ x))) := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [Finset.mul_sum]
    _ = ∑ j : Fin (n + 1), ∑ σ : Equiv.Perm (Fin (n + 1)),
        permSign ℝ σ *
          ((-1 : ℝ) ^ j.val *
            f (FinTuple.delete j (FinTuple.permute σ x))) := by
      rw [Finset.sum_comm]
    _ =
        ∑ _j : Fin (n + 1),
          ∑ p : Fin (n + 1) × Equiv.Perm (Fin n),
            (-1 : ℝ) ^ p.1.val * permSign ℝ p.2 *
              f (FinTuple.permute p.2 (FinTuple.delete p.1 x)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact sum_permutations_delete_at n f x j
    _ = ∑ _j : Fin (n + 1),
          coboundary n (alternatingSum n f) x := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Fintype.sum_prod_type]
      simp only [coboundary_apply, alternatingSum_apply]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      simp [mul_assoc]
    _ = (n + 1 : ℝ) * coboundary n (alternatingSum n f) x := by
      simp

/-- Coboundary is linear with respect to a constant real scalar. -/
theorem coboundary_const_mul (n : ℕ) (c : ℝ)
    (f : FinTuple X n → ℝ) (x : FinTuple X (n + 1)) :
    coboundary n (fun y ↦ c * f y) x = c * coboundary n f x := by
  rw [coboundary_apply, coboundary_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Full normalized homogeneous alternation is a chain map. -/
theorem alternation_coboundary (n : ℕ) (f : FinTuple X n → ℝ) :
    alternation (n + 1) (coboundary n f) =
      coboundary n (alternation n f) := by
  funext x
  rw [alternation_apply, alternatingSum_coboundary]
  change
    (Nat.factorial (n + 1) : ℝ)⁻¹ *
        ((n + 1 : ℝ) * coboundary n (alternatingSum n f) x) =
      coboundary n
        (fun y ↦ (Nat.factorial n : ℝ)⁻¹ * alternatingSum n f y) x
  rw [coboundary_const_mul]
  have hfactor :
      (Nat.factorial (n + 1) : ℝ)⁻¹ * (n + 1 : ℝ) =
        (Nat.factorial n : ℝ)⁻¹ := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    field_simp
    norm_num
  rw [← mul_assoc, hfactor]

end
end CochainAlternation
end Sp4
