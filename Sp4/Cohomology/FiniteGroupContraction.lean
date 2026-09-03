import Mathlib
import Sp4.Basic.FinTuple

/-!
# The finite-stabilizer contraction

For a finite group and a real vector space with trivial action, homogeneous
cochains are honest functions on finite powers of the group.  This file proves
the averaging contraction used in the positive columns of the measurable
projective spectral sequence.  No measurable representative is evaluated on a
null subset: the entire calculation takes place in the finite group's atomic
bar complex.
-/

namespace Sp4
namespace FiniteGroupCohomology

noncomputable section

open scoped BigOperators

variable {K V : Type*} [Fintype K] [Nonempty K]
  [AddCommGroup V] [Module ℝ V]

/-- Homogeneous degree-`q` cochains with trivial coefficients. -/
abbrev Cochain (K V : Type*) (q : ℕ) := (Fin (q + 1) → K) → V

/-- The alternating homogeneous coboundary. -/
def coboundary (q : ℕ) : Cochain K V q →ₗ[ℝ] Cochain K V (q + 1) where
  toFun f x :=
    ∑ i : Fin (q + 2), (-1 : ℝ) ^ i.1 • f (FinTuple.delete i x)
  map_add' f g := by
    funext x
    simp only [Pi.add_apply]
    simp_rw [smul_add]
    exact Finset.sum_add_distrib
  map_smul' a f := by
    funext x
    simp only [Pi.smul_apply]
    change (∑ i : Fin (q + 2),
      (-1 : ℝ) ^ i.1 • a • f (FinTuple.delete i x)) =
        a • ∑ i : Fin (q + 2),
          (-1 : ℝ) ^ i.1 • f (FinTuple.delete i x)
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    module

@[simp]
theorem coboundary_apply (q : ℕ) (f : Cochain K V q)
    (x : Fin (q + 2) → K) :
    coboundary q f x =
      ∑ i : Fin (q + 2), (-1 : ℝ) ^ i.1 •
        f (FinTuple.delete i x) :=
  rfl

@[simp]
theorem delete_zero_cons {n : ℕ} (k : K) (x : Fin (n + 1) → K) :
    FinTuple.delete (0 : Fin (n + 2)) (Fin.cons k x) = x := by
  funext i
  rfl

@[simp]
theorem delete_succ_cons {n : ℕ} (i : Fin (n + 1))
    (k : K) (x : Fin (n + 1) → K) :
    FinTuple.delete i.succ (Fin.cons k x) =
      Fin.cons k (FinTuple.delete i x) := by
  exact Fin.cons_comp_succ_succAbove k x i

/-- Insert a fixed new first coordinate. -/
def contractAt (k : K) (q : ℕ) :
    Cochain K V (q + 1) →ₗ[ℝ] Cochain K V q where
  toFun f x := f (Fin.cons k x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem contractAt_apply (k : K) (q : ℕ) (f : Cochain K V (q + 1))
    (x : Fin (q + 1) → K) :
    contractAt k q f x = f (Fin.cons k x) :=
  rfl

/-- Splitting the coboundary of a cochain evaluated on a tuple with a new
first coordinate. -/
theorem coboundary_cons (k : K) (q : ℕ) (f : Cochain K V (q + 1))
    (x : Fin (q + 2) → K) :
    coboundary (q + 1) f (Fin.cons k x) =
      f x - coboundary q (contractAt k q f) x := by
  rw [coboundary_apply, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, delete_zero_cons,
    Fin.val_succ, pow_succ, delete_succ_cons, contractAt_apply,
    coboundary_apply]
  simp only [mul_neg, mul_one, neg_smul]
  rw [Finset.sum_neg_distrib]
  abel

/-- The extra-degeneracy identity for insertion of one fixed coordinate. -/
theorem coboundary_contractAt_add_contractAt_coboundary
    (k : K) (q : ℕ) (f : Cochain K V (q + 1)) :
    coboundary q (contractAt k q f) +
        contractAt k (q + 1) (coboundary (q + 1) f) = f := by
  funext x
  rw [Pi.add_apply, contractAt_apply, coboundary_cons]
  module

/-- Average the fixed-coordinate contractions. -/
def contract (q : ℕ) : Cochain K V (q + 1) →ₗ[ℝ] Cochain K V q :=
  ((Fintype.card K : ℝ)⁻¹) • ∑ k : K, contractAt k q

@[simp]
theorem contract_apply (q : ℕ) (f : Cochain K V (q + 1))
    (x : Fin (q + 1) → K) :
    contract q f x =
      ((Fintype.card K : ℝ)⁻¹) • ∑ k : K, f (Fin.cons k x) :=
  by simp [contract]

/-- The explicit averaging homotopy identity `d s + s d = id`. -/
theorem coboundary_contract_add_contract_coboundary
    (q : ℕ) (f : Cochain K V (q + 1)) :
    coboundary q (contract q f) +
        contract (q + 1) (coboundary (q + 1) f) = f := by
  simp only [contract, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum]
  rw [← smul_add, ← Finset.sum_add_distrib]
  simp_rw [coboundary_contractAt_add_contractAt_coboundary]
  rw [Finset.sum_const]
  have hcard : (Fintype.card K : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simpa [Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ] using
    inv_smul_smul₀ hcard f

/-! ## The invariant homogeneous complex -/

variable [Group K]

/-- Homogeneous cochains invariant under simultaneous left translation.  The
coefficient action is trivial, as it is for the parameter modules in the
finite-stabilizer columns of the article. -/
def InvariantCochains (K V : Type*) [Fintype K] [Group K]
    [AddCommGroup V] [Module ℝ V] (q : ℕ) :
    Submodule ℝ (Cochain K V q) where
  carrier := {f | ∀ (g : K) (x : Fin (q + 1) → K),
    f (fun i ↦ g * x i) = f x}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg a x
    simp only [Pi.add_apply, hf a x, hg a x]
  smul_mem' := by
    intro a f hf g x
    simp only [Pi.smul_apply, hf g x]

/-- The homogeneous coboundary preserves invariance. -/
def invariantCoboundary (q : ℕ) :
    InvariantCochains K V q →ₗ[ℝ] InvariantCochains K V (q + 1) where
  toFun f := ⟨coboundary q f.1, by
    intro g x
    simp only [coboundary_apply]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact f.2 g (FinTuple.delete i x)⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add (coboundary q) f.1 g.1
  map_smul' a f := by
    apply Subtype.ext
    exact map_smul (coboundary q) a f.1

@[simp]
theorem invariantCoboundary_coe (q : ℕ)
    (f : InvariantCochains K V q) :
    (invariantCoboundary q f).1 = coboundary q f.1 :=
  rfl

/-- Reindexing the finite average shows that the averaging contraction
preserves homogeneous invariance. -/
theorem contract_invariant (q : ℕ) (f : InvariantCochains K V (q + 1)) :
    ∀ (g : K) (x : Fin (q + 1) → K),
      contract q f.1 (fun i ↦ g * x i) = contract q f.1 x := by
  intro g x
  simp only [contract_apply]
  congr 1
  apply Eq.symm
  apply Fintype.sum_bijective (g * ·) (Group.mulLeft_bijective g)
  intro k
  have htuple :
      (fun i : Fin (q + 2) ↦
        g * (Fin.cons k x : Fin (q + 2) → K) i) =
        Fin.cons (g * k) (fun i : Fin (q + 1) ↦ g * x i) := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp
    · simp
  rw [← htuple]
  exact (f.2 g (Fin.cons k x)).symm

/-- The averaging contraction on invariant cochains. -/
def invariantContract (q : ℕ) :
    InvariantCochains K V (q + 1) →ₗ[ℝ] InvariantCochains K V q where
  toFun f := ⟨contract q f.1, contract_invariant q f⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add (contract q) f.1 g.1
  map_smul' a f := by
    apply Subtype.ext
    exact map_smul (contract q) a f.1

@[simp]
theorem invariantContract_coe (q : ℕ)
    (f : InvariantCochains K V (q + 1)) :
    (invariantContract q f).1 = contract q f.1 :=
  rfl

/-- The finite-group averaging identity inside the invariant homogeneous
complex. -/
theorem invariantCoboundary_contract_add_contract_coboundary
    (q : ℕ) (f : InvariantCochains K V (q + 1)) :
    invariantCoboundary q (invariantContract q f) +
        invariantContract (q + 1) (invariantCoboundary (q + 1) f) = f := by
  apply Subtype.ext
  exact coboundary_contract_add_contract_coboundary q f.1

/-- Every invariant cocycle of positive degree is an invariant coboundary.
This is the precise M5 vanishing statement consumed by the projective
resolution. -/
theorem exists_invariant_primitive
    (q : ℕ) (f : InvariantCochains K V (q + 1))
    (hf : invariantCoboundary (q + 1) f = 0) :
    ∃ b : InvariantCochains K V q, invariantCoboundary q b = f := by
  refine ⟨invariantContract q f, ?_⟩
  have h := invariantCoboundary_contract_add_contract_coboundary q f
  rw [hf, map_zero, add_zero] at h
  exact h

/-! ## Quotient cohomology and its vanishing -/

/-- Positive-degree invariant cocycles in the atomic homogeneous complex. -/
def CocyclesSucc (q : ℕ) :
    Submodule ℝ (InvariantCochains K V (q + 1)) :=
  LinearMap.ker (invariantCoboundary (K := K) (V := V) (q + 1))

/-- Positive-degree invariant boundaries, regarded as a submodule of the
cocycles. -/
def BoundariesSucc (q : ℕ) :
    Submodule ℝ (CocyclesSucc (K := K) (V := V) q) :=
  (LinearMap.range (invariantCoboundary (K := K) (V := V) q)).comap
    (CocyclesSucc (K := K) (V := V) q).subtype

/-- Degree `q + 1` cohomology of the invariant finite-group bar complex. -/
abbrev HSucc (q : ℕ) : Type _ :=
  (↑(CocyclesSucc (K := K) (V := V) q) : Type _) ⧸
    (BoundariesSucc (K := K) (V := V) q).toAddSubgroup

/-- The explicit averaging contraction kills every positive-degree quotient
cohomology class. -/
theorem cohomologySucc_eq_zero (q : ℕ)
    (x : HSucc (K := K) (V := V) q) : x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H f =>
      apply (QuotientAddGroup.eq_zero_iff f).2
      change f.1 ∈ LinearMap.range
        (invariantCoboundary (K := K) (V := V) q)
      obtain ⟨b, hb⟩ := exists_invariant_primitive q f.1 f.2
      exact ⟨b, hb⟩

end
end FiniteGroupCohomology
end Sp4
