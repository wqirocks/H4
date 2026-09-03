import Mathlib.Data.Fin.Tuple.Basic

/-!
# Finite tuples and deletion

The original proof uses the same twice-deletion identity for coboundaries, chain
boundaries, and simplicial homotopies.  We expose that identity here once, in terms of
the order-preserving embedding `Fin.succAbove`.
-/

namespace Sp4

/-- An ordered tuple of length `n`. -/
abbrev FinTuple (X : Type*) (n : ℕ) := Fin n → X

namespace FinTuple

/-- Delete the entry indexed by `i`, preserving the order of all other entries. -/
def delete {X : Type*} {n : ℕ} (i : Fin (n + 1)) (x : FinTuple X (n + 1)) :
    FinTuple X n :=
  i.removeNth x

@[simp]
theorem delete_apply {X : Type*} {n : ℕ} (i : Fin (n + 1))
    (x : FinTuple X (n + 1)) (k : Fin n) :
    delete i x k = x (i.succAbove k) :=
  rfl

/-- The canonical simplicial identity for deleting two entries.  The index
`j.succAbove i` is the original position represented by `i` after deleting `j`, and
`i.predAbove j` is the position represented by `j` after deleting that other entry. -/
theorem delete_delete_swap {X : Type*} {n : ℕ} (x : FinTuple X (n + 2))
    (i : Fin (n + 1)) (j : Fin (n + 2)) :
    delete i (delete j x) =
      delete (i.predAbove j) (delete (j.succAbove i) x) := by
  simpa only [delete] using Fin.removeNth_removeNth_eq_swap x i j

/-- Permute a tuple by precomposition. -/
def permute {X : Type*} {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : FinTuple X n) :
    FinTuple X n :=
  x ∘ σ

@[simp]
theorem permute_apply {X : Type*} {n : ℕ} (σ : Equiv.Perm (Fin n))
    (x : FinTuple X n) (i : Fin n) : permute σ x i = x (σ i) :=
  rfl

end FinTuple

end Sp4
