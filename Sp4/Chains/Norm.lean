import Sp4.Chains.Orbit
import Mathlib.Analysis.Seminorm

/-!
# The quotient `ℓ¹` seminorm on finite orbit chains

The raw configuration module is a finitely supported function space.  We put
the ordinary coefficient `ℓ¹` mass on it and give the orbit quotient the
infimum over all raw presentations.  In particular, this file proves the
arbitrary-`ε` near-attainment statement used by the diffusion argument.
-/

namespace Sp4
namespace OrbitChain

noncomputable section

open scoped BigOperators

/-- Total coefficient mass of a raw finite real chain. -/
def rawMass {n : ℕ} (c : Raw ℝ n) : ℝ :=
  ∑ x ∈ c.support, |c x|

theorem rawMass_nonneg {n : ℕ} (c : Raw ℝ n) : 0 ≤ rawMass c := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

@[simp]
theorem rawMass_zero {n : ℕ} : rawMass (0 : Raw ℝ n) = 0 := by
  simp [rawMass]

@[simp]
theorem rawMass_single {n : ℕ} (x : GenericConfig n) (a : ℝ) :
    rawMass (Finsupp.single x a) = |a| := by
  by_cases ha : a = 0
  · simp [ha]
  · simp [rawMass, ha]

@[simp]
theorem rawMass_generator {n : ℕ} (x : GenericConfig n) :
    rawMass (generator (R := ℝ) x) = 1 := by
  simp [generator]

theorem rawMass_add_le {n : ℕ} (c d : Raw ℝ n) :
    rawMass (c + d) ≤ rawMass c + rawMass d := by
  classical
  let s := c.support ∪ d.support
  have hadd : (c + d).support ⊆ s := Finsupp.support_add
  have hleft : rawMass (c + d) = ∑ x ∈ s, |(c + d) x| := by
    rw [rawMass]
    apply Finset.sum_subset hadd
    intro x hxs hx
    have hx0 : (c + d) x = 0 := Finsupp.notMem_support_iff.mp hx
    simp [hx0]
  have hc : rawMass c = ∑ x ∈ s, |c x| := by
    rw [rawMass]
    apply Finset.sum_subset Finset.subset_union_left
    intro x hxs hx
    have hx0 : c x = 0 := Finsupp.notMem_support_iff.mp hx
    simp [hx0]
  have hd : rawMass d = ∑ x ∈ s, |d x| := by
    rw [rawMass]
    apply Finset.sum_subset Finset.subset_union_right
    intro x hxs hx
    have hx0 : d x = 0 := Finsupp.notMem_support_iff.mp hx
    simp [hx0]
  rw [hleft, hc, hd, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  simpa using abs_add_le (c x) (d x)

@[simp]
theorem rawMass_neg {n : ℕ} (c : Raw ℝ n) : rawMass (-c) = rawMass c := by
  classical
  simp only [rawMass, Finsupp.support_neg]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finsupp.neg_apply, abs_neg]

theorem rawMass_sub_le {n : ℕ} (c d : Raw ℝ n) :
    rawMass (c - d) ≤ rawMass c + rawMass d := by
  simpa [sub_eq_add_neg] using rawMass_add_le c (-d)

@[simp]
theorem rawMass_smul {n : ℕ} (a : ℝ) (c : Raw ℝ n) :
    rawMass (a • c) = |a| * rawMass c := by
  by_cases ha : a = 0
  · simp [ha]
  · simp [rawMass, Finsupp.support_smul_eq ha, Finsupp.smul_apply,
      abs_mul, Finset.mul_sum]

theorem rawMass_sum_le {n : ℕ} {ι : Type*} (s : Finset ι)
    (c : ι → Raw ℝ n) :
    rawMass (∑ i ∈ s, c i) ≤ ∑ i ∈ s, rawMass (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (rawMass_add_le (c a) (∑ i ∈ s, c i)).trans
        (add_le_add (le_refl _) ih)

/-- The set of masses of all raw presentations of a quotient chain. -/
def presentationMasses {n : ℕ} (z : Module ℝ n) : Set ℝ :=
  {r | ∃ c : Raw ℝ n, (relations ℝ n).mkQ c = z ∧ rawMass c = r}

theorem presentationMasses_nonempty {n : ℕ} (z : Module ℝ n) :
    (presentationMasses z).Nonempty := by
  obtain ⟨c, rfl⟩ := (relations ℝ n).mkQ_surjective z
  exact ⟨rawMass c, c, rfl, rfl⟩

theorem presentationMasses_bddBelow {n : ℕ} (z : Module ℝ n) :
    BddBelow (presentationMasses z) := by
  refine ⟨0, ?_⟩
  rintro r ⟨c, -, rfl⟩
  exact rawMass_nonneg c

/-- Quotient `ℓ¹` seminorm: the infimum of raw coefficient masses over all
presentations of the orbit-chain class. -/
def quotientL1 {n : ℕ} (z : Module ℝ n) : ℝ :=
  sInf (presentationMasses z)

theorem quotientL1_nonneg {n : ℕ} (z : Module ℝ n) : 0 ≤ quotientL1 z := by
  apply le_csInf (presentationMasses_nonempty z)
  rintro r ⟨c, -, rfl⟩
  exact rawMass_nonneg c

/-- Every displayed raw presentation bounds the quotient seminorm. -/
theorem quotientL1_mkQ_le {n : ℕ} (c : Raw ℝ n) :
    quotientL1 ((relations ℝ n).mkQ c) ≤ rawMass c := by
  apply csInf_le (presentationMasses_bddBelow _)
  exact ⟨c, rfl, rfl⟩

/-- The defining infimum can be approached by an actual finite presentation
to within any positive `ε`. -/
theorem exists_presentation_lt_quotientL1_add {n : ℕ}
    (z : Module ℝ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : Raw ℝ n,
      (relations ℝ n).mkQ c = z ∧ rawMass c < quotientL1 z + ε := by
  have hlt : quotientL1 z < quotientL1 z + ε := by linarith
  obtain ⟨r, hr, hrlt⟩ :=
    exists_lt_of_csInf_lt (presentationMasses_nonempty z) hlt
  rcases hr with ⟨c, hc, rfl⟩
  exact ⟨c, hc, hrlt⟩

@[simp]
theorem quotientL1_zero {n : ℕ} : quotientL1 (0 : Module ℝ n) = 0 := by
  apply le_antisymm
  · have h := quotientL1_mkQ_le (0 : Raw ℝ n)
    simpa using h
  · exact quotientL1_nonneg _

theorem quotientL1_add_le {n : ℕ} (z w : Module ℝ n) :
    quotientL1 (z + w) ≤ quotientL1 z + quotientL1 w := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨c, hc, hcm⟩ :=
    exists_presentation_lt_quotientL1_add z (show 0 < ε / 2 by linarith)
  obtain ⟨d, hd, hdm⟩ :=
    exists_presentation_lt_quotientL1_add w (show 0 < ε / 2 by linarith)
  have hmk : (relations ℝ n).mkQ (c + d) = z + w := by
    rw [map_add, hc, hd]
  rw [← hmk]
  exact (quotientL1_mkQ_le (c + d)).trans
    ((rawMass_add_le c d).trans (by linarith))

theorem quotientL1_smul_le {n : ℕ} (a : ℝ) (z : Module ℝ n) :
    quotientL1 (a • z) ≤ |a| * quotientL1 z := by
  by_cases ha : a = 0
  · simp [ha]
  have habs : 0 < |a| := abs_pos.mpr ha
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨c, hc, hcm⟩ := exists_presentation_lt_quotientL1_add z
    (show 0 < ε / |a| by positivity)
  have hmk : (relations ℝ n).mkQ (a • c) = a • z := by
    rw [map_smul, hc]
  rw [← hmk]
  apply le_of_lt
  calc
    quotientL1 ((relations ℝ n).mkQ (a • c)) ≤ rawMass (a • c) :=
      quotientL1_mkQ_le _
    _ = |a| * rawMass c := rawMass_smul _ _
    _ < |a| * quotientL1 z + ε := by
      calc
        |a| * rawMass c < |a| * (quotientL1 z + ε / |a|) :=
          mul_lt_mul_of_pos_left hcm habs
        _ = |a| * quotientL1 z + ε := by field_simp

/-- The quotient mass bundled as an actual seminorm. -/
def quotientL1Seminorm (n : ℕ) : Seminorm ℝ (Module ℝ n) :=
  Seminorm.ofSMulLE quotientL1 quotientL1_zero quotientL1_add_le
    (fun a z ↦ by simpa [Real.norm_eq_abs] using quotientL1_smul_le a z)

@[simp]
theorem quotientL1Seminorm_apply {n : ℕ} (z : Module ℝ n) :
    quotientL1Seminorm n z = quotientL1 z := rfl

@[simp]
theorem quotientL1_neg {n : ℕ} (z : Module ℝ n) :
    quotientL1 (-z) = quotientL1 z := by
  change quotientL1Seminorm n (-z) = quotientL1Seminorm n z
  exact map_neg_eq_map (quotientL1Seminorm n) z

@[simp]
theorem quotientL1_smul {n : ℕ} (a : ℝ) (z : Module ℝ n) :
    quotientL1 (a • z) = |a| * quotientL1 z := by
  change quotientL1Seminorm n (a • z) =
    |a| * quotientL1Seminorm n z
  simpa [Real.norm_eq_abs] using map_smul_eq_mul (quotientL1Seminorm n) a z

end
end OrbitChain
end Sp4
