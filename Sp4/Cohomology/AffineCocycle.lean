import Sp4.Pfaffian.Certificates

/-!
# The affine-difference cocycle

This file defines the ordered rational difference and the thirty-term normalized
formula.  The construction is finite and algebraic; no measurable-cohomology input is
used here.
-/

namespace Sp4

namespace AffineCocycle

noncomputable section

open scoped BigOperators
open Pfaffian

/-- A square matrix is skew with the sign convention used for Gram matrices. -/
def IsSkew {n : Type*} [Neg ℂ] (A : Matrix n n ℂ) : Prop :=
  ∀ i j, A j i = -A i j

theorem matrix5_isSkew (q : Pfaffian.Coord5) : IsSkew (Pfaffian.matrix5 q) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Pfaffian.matrix5]

/-- The ordered Pfaffian bracket `[i j k l]`. -/
def orderedBracket {n : Type*} (A : Matrix n n ℂ) (i j k l : n) : ℂ :=
  A i j * A k l - A i k * A j l + A i l * A j k

theorem orderedBracket_swap_last {n : Type*} {A : Matrix n n ℂ}
    (hA : IsSkew A) (i j k l : n) :
    orderedBracket A i j l k = -orderedBracket A i j k l := by
  rw [orderedBracket, orderedBracket, hA k l]
  ring

theorem orderedBracket_swap_first {n : Type*} {A : Matrix n n ℂ}
    (hA : IsSkew A) (i j k l : n) :
    orderedBracket A j i k l = -orderedBracket A i j k l := by
  rw [orderedBracket, orderedBracket, hA i j]
  ring

/-- The lift-independent rational affine difference attached to five ordered labels. -/
def affineDifference {n : Type*} (A : Matrix n n ℂ) (i j k l m : n) : ℂ :=
  -(A i k * A j k * orderedBracket A i j l m) /
    (orderedBracket A i j k l * orderedBracket A i j k m)

theorem affineDifference_swap {n : Type*} {A : Matrix n n ℂ}
    (hA : IsSkew A) (i j k l m : n) :
    affineDifference A i j k l m = -affineDifference A i j k m l := by
  rw [affineDifference, affineDifference, orderedBracket_swap_last hA]
  ring

/-- Principal four-bracket after deleting one label from a five-by-five matrix. -/
def principalPf5 (A : Matrix (Fin 5) (Fin 5) ℂ) (k : Fin 5) : ℂ :=
  Pfaffian.pfaffian4 (Pfaffian.principal4Of5 A k)

@[simp] theorem principalPf5_matrix5_zero (q : Pfaffian.Coord5) :
    principalPf5 (Pfaffian.matrix5 q) 0 = Pfaffian.p0 q := by
  simp [principalPf5]

@[simp] theorem principalPf5_matrix5_one (q : Pfaffian.Coord5) :
    principalPf5 (Pfaffian.matrix5 q) 1 = Pfaffian.p1 q := by
  simp [principalPf5]

@[simp] theorem principalPf5_matrix5_two (q : Pfaffian.Coord5) :
    principalPf5 (Pfaffian.matrix5 q) 2 = Pfaffian.p2 q := by
  simp [principalPf5]

@[simp] theorem principalPf5_matrix5_three (q : Pfaffian.Coord5) :
    principalPf5 (Pfaffian.matrix5 q) 3 = Pfaffian.p3 q := by
  simp [principalPf5]

@[simp] theorem principalPf5_matrix5_four (q : Pfaffian.Coord5) :
    principalPf5 (Pfaffian.matrix5 q) 4 = Pfaffian.p4 q := by
  simp [principalPf5]

/-- The finite index set `(k,i,j)` with `i<j` and both different from `k`.
It indexes the thirty terms in the reduced alternation. -/
def reducedIndices : Finset (Fin 5 × Fin 5 × Fin 5) :=
  Finset.univ.filter fun t => t.2.1 < t.2.2 ∧ t.2.1 ≠ t.1 ∧ t.2.2 ≠ t.1

theorem reducedIndices_card : reducedIndices.card = 30 := by
  decide

/-- Product of the two complementary principal Pfaffians. -/
def complementaryPfProduct (A : Matrix (Fin 5) (Fin 5) ℂ)
    (k i j : Fin 5) : ℂ :=
  ∏ s : Fin 5, if s = k ∨ s = i ∨ s = j then 1 else principalPf5 A s

/-- One normalized term of the thirty-term formula. -/
def reducedTerm (A : Matrix (Fin 5) (Fin 5) ℂ)
    (t : Fin 5 × Fin 5 × Fin 5) : ℂ :=
  let k := t.1
  let i := t.2.1
  let j := t.2.2
  (-1 : ℂ) ^ (i.val + j.val) * A i k * A j k * principalPf5 A k /
    complementaryPfProduct A k i j

/-- The thirty-term normalized affine cocycle formula from the paper. -/
def reducedR (A : Matrix (Fin 5) (Fin 5) ℂ) : ℂ :=
  (1 / 30 : ℂ) * ∑ t ∈ reducedIndices, reducedTerm A t

/-- Exact evaluation of the thirty-term formula on the first special face. -/
theorem reducedR_Phi1 (q : Adm1) :
    reducedR (matrix5 (Phi1Coord q.1.1)) = specialF1 q.1.1.x q.1.1.y := by
  classical
  simp only [reducedR, reducedIndices, Finset.sum_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Fin.sum_univ_succ, Fin.prod_univ_succ, reducedTerm, complementaryPfProduct]
  simp [Phi1Coord, matrix5]
  have ha : q.1.1.x ≠ 0 := q.1.2.x_ne
  have hb : q.1.1.y ≠ 0 := q.1.2.y_ne
  have hb2 : q.1.1.y - 2 ≠ 0 := by
    intro h
    apply q.2.p2_ne
    rw [p2_Phi1Coord, h]
    ring
  have hab1 : q.1.1.x - q.1.1.y - 1 ≠ 0 := by
    intro h
    apply q.2.p1_ne
    rw [p1_Phi1Coord, h]
    ring
  have hab2 : q.1.1.x - q.1.1.y ^ 2 + 1 ≠ 0 := by
    simpa only [p3_Phi1Coord] using q.2.p3_ne
  have hdelta : -q.1.1.x + q.1.1.y + 1 ≠ 0 := by
    simpa only [p4_Phi1Coord] using q.2.p4_ne
  norm_num [specialF1, specialDenom1, specialN1]
  field_simp [ha, hb, hb2, hab1, hab2, hdelta]
  ring

/-- Exact evaluation of the thirty-term formula on the second special face. -/
theorem reducedR_Phi2 (q : Adm2) :
    reducedR (matrix5 (Phi2Coord q.1.1)) = specialF2 q.1.1.x q.1.1.y := by
  classical
  generalize hQeq : Phi2Coord q.1.1 = Q
  have hQ : IsU5 Q := hQeq ▸ q.2
  change reducedR (matrix5 Q) = specialF2 q.1.1.x q.1.1.y
  simp only [reducedR, reducedIndices, Finset.sum_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Fin.sum_univ_succ, Fin.prod_univ_succ, reducedTerm, complementaryPfProduct]
  field_simp [hQ.p0_ne, hQ.p1_ne, hQ.p2_ne, hQ.p3_ne, hQ.p4_ne]
  clear hQ
  rw [← hQeq]
  simp [Phi2Coord, matrix5, p0, p1, p2, p3, p4]
  have ha : q.1.1.x ≠ 0 := q.1.2.x_ne
  have hb : q.1.1.y ≠ 0 := q.1.2.y_ne
  have hb2 : 2 * q.1.1.y - 1 ≠ 0 := by
    intro h
    apply q.2.p2_ne
    rw [p2_Phi2Coord, h]
    ring
  have hab1 : q.1.1.x - q.1.1.y - 1 ≠ 0 := by
    intro h
    apply q.2.p1_ne
    rw [p1_Phi2Coord, h]
    ring
  have hab2 : q.1.1.x * q.1.1.y + q.1.1.y ^ 2 - 1 ≠ 0 := by
    intro h
    apply q.2.p3_ne
    rw [p3_Phi2Coord, show 1 - q.1.1.x * q.1.1.y - q.1.1.y ^ 2 =
      -(q.1.1.x * q.1.1.y + q.1.1.y ^ 2 - 1) by ring, h]
    ring
  have hdelta : -q.1.1.x + q.1.1.y + 1 ≠ 0 := by
    simpa only [p4_Phi2Coord] using q.2.p4_ne
  have hc2f : (2 * q.1.1.y - 1) ^ 2 *
      (q.1.1.x * q.1.1.y + q.1.1.y ^ 2 - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hb2) hab2
  have hc2fField : -1 + q.1.1.y * 4 + q.1.1.y * q.1.1.x -
      q.1.1.y ^ 2 * 3 - q.1.1.y ^ 2 * 4 * q.1.1.x - q.1.1.y ^ 3 * 4 +
      q.1.1.y ^ 3 * 4 * q.1.1.x + q.1.1.y ^ 4 * 4 ≠ 0 := by
    convert hc2f using 1 <;> ring
  simp only [specialF2, specialDenom2, specialN2]
  field_simp [hb2, hab1, hab2]
  ring_nf
  field_simp [hc2fField]
  set_option maxRecDepth 10000 in
    ring

/-- Exact evaluation of the thirty-term formula on the third special face. -/
theorem reducedR_Phi3 (q : Adm3) :
    reducedR (matrix5 (Phi3Coord q.1.1)) = specialF1 q.1.1.x q.1.1.y := by
  classical
  generalize hQeq : Phi3Coord q.1.1 = Q
  have hQ : IsU5 Q := hQeq ▸ q.2
  change reducedR (matrix5 Q) = specialF1 q.1.1.x q.1.1.y
  simp only [reducedR, reducedIndices, Finset.sum_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Fin.sum_univ_succ, Fin.prod_univ_succ, reducedTerm, complementaryPfProduct]
  field_simp [hQ.p0_ne, hQ.p1_ne, hQ.p2_ne, hQ.p3_ne, hQ.p4_ne]
  clear hQ
  rw [← hQeq]
  simp [Phi3Coord, matrix5, p0, p1, p2, p3, p4]
  have ha : q.1.1.x ≠ 0 := q.1.2.x_ne
  have hb : q.1.1.y ≠ 0 := q.1.2.y_ne
  have hb2 : q.1.1.y - 2 ≠ 0 := by
    intro h
    apply q.2.p1_ne
    rw [p1_Phi3Coord, h]
    ring
  have hab1 : q.1.1.x - q.1.1.y - 1 ≠ 0 := by
    intro h
    apply q.2.p0_ne
    rw [p0_Phi3Coord, h]
    ring
  have hab2 : q.1.1.x - q.1.1.y ^ 2 + 1 ≠ 0 := by
    simpa only [p2_Phi3Coord] using q.2.p2_ne
  have hdelta : -q.1.1.x + q.1.1.y + 1 ≠ 0 := by
    simpa only [p4_Phi3Coord] using q.2.p4_ne
  simp only [specialF1, specialDenom1, specialN1]
  field_simp [ha, hb, hb2, hab1, hab2, hdelta]
  set_option maxRecDepth 10000 in
    ring

/-- Exact evaluation of the thirty-term formula on the fourth special face. -/
theorem reducedR_Phi4 (q : Adm4) :
    reducedR (matrix5 (Phi4Coord q.1.1)) = specialF2 q.1.1.x q.1.1.y := by
  classical
  generalize hQeq : Phi4Coord q.1.1 = Q
  have hQ : IsU5 Q := hQeq ▸ q.2
  change reducedR (matrix5 Q) = specialF2 q.1.1.x q.1.1.y
  simp only [reducedR, reducedIndices, Finset.sum_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [Fin.sum_univ_succ, Fin.prod_univ_succ, reducedTerm, complementaryPfProduct]
  field_simp [hQ.p0_ne, hQ.p1_ne, hQ.p2_ne, hQ.p3_ne, hQ.p4_ne]
  clear hQ
  rw [← hQeq]
  simp [Phi4Coord, matrix5, p0, p1, p2, p3, p4]
  have ha : q.1.1.x ≠ 0 := q.1.2.x_ne
  have hb : q.1.1.y ≠ 0 := q.1.2.y_ne
  have hb2 : 2 * q.1.1.y - 1 ≠ 0 := by
    simpa only [p1_Phi4Coord] using q.2.p1_ne
  have hab1 : q.1.1.x - q.1.1.y - 1 ≠ 0 := by
    intro h
    apply q.2.p0_ne
    rw [p0_Phi4Coord _ hb]
    rw [show -q.1.1.x + q.1.1.y + 1 = -(q.1.1.x - q.1.1.y - 1) by ring, h]
    ring
  have hab2 : q.1.1.x * q.1.1.y + q.1.1.y ^ 2 - 1 ≠ 0 := by
    intro h
    apply q.2.p2_ne
    rw [p2_Phi4Coord _ hb, h]
    simp
  have hdelta : -q.1.1.x + q.1.1.y + 1 ≠ 0 := by
    simpa only [p0_Phi4Coord _ hb] using q.2.p0_ne
  have hc2f : (2 * q.1.1.y - 1) ^ 2 *
      (q.1.1.x * q.1.1.y + q.1.1.y ^ 2 - 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hb2) hab2
  have hc2fField : -1 + q.1.1.y * 4 + q.1.1.y * q.1.1.x -
      q.1.1.y ^ 2 * 3 - q.1.1.y ^ 2 * 4 * q.1.1.x - q.1.1.y ^ 3 * 4 +
      q.1.1.y ^ 3 * 4 * q.1.1.x + q.1.1.y ^ 4 * 4 ≠ 0 := by
    convert hc2f using 1 <;> ring
  field_simp [hb]
  simp only [specialF2, specialDenom2, specialN2]
  field_simp [ha, hb, hb2, hab1, hab2, hdelta]
  ring_nf
  field_simp [hc2fField]
  set_option maxRecDepth 10000 in
    ring

/-! ## The original 120-term alternation -/

/-- The signed summand in the original `5!`-term definition. -/
def rawTerm (A : Matrix (Fin 5) (Fin 5) ℂ) (σ : Equiv.Perm (Fin 5)) : ℂ :=
  (Equiv.Perm.sign σ : ℂ) *
    affineDifference A (σ 0) (σ 1) (σ 2) (σ 3) (σ 4)

/-- The original alternating average over all `5! = 120` orderings. -/
def rawAlternationR (A : Matrix (Fin 5) (Fin 5) ℂ) : ℂ :=
  (1 / 120 : ℂ) * ∑ σ : Equiv.Perm (Fin 5), rawTerm A σ

/-- The reduced index `(k,min i j,max i j)` associated with an ordering. -/
def reducedIndexOfPerm (σ : Equiv.Perm (Fin 5)) : Fin 5 × Fin 5 × Fin 5 :=
  (σ 2, min (σ 0) (σ 1), max (σ 0) (σ 1))

private theorem decomposeFinSymm_apply {n : ℕ} (p : Fin (n + 1))
    (e : Equiv.Perm (Fin n)) (i : Fin (n + 1)) :
    Equiv.Perm.decomposeFin.symm (p, e) i =
      Fin.cases p (fun x => Equiv.swap 0 p (e x).succ) i := by
  refine Fin.cases ?_ (fun x => ?_) i
  · exact Equiv.Perm.decomposeFin_symm_apply_zero p e
  · exact Equiv.Perm.decomposeFin_symm_apply_succ e p x

private theorem finCasesOne {n : ℕ} {C : Sort*} (z : C) (s : Fin (n + 1) → C) :
    Fin.cases z s (1 : Fin (n + 2)) = s 0 := by
  rw [show (1 : Fin (n + 2)) = Fin.succ 0 by rfl, Fin.cases_succ]

private theorem finCasesTwo {n : ℕ} {C : Sort*} (z : C) (s : Fin (n + 2) → C) :
    Fin.cases z s (2 : Fin (n + 3)) = s 1 := by
  rw [show (2 : Fin (n + 3)) = Fin.succ 1 by rfl, Fin.cases_succ]

private theorem finCasesThree {n : ℕ} {C : Sort*} (z : C) (s : Fin (n + 3) → C) :
    Fin.cases z s (3 : Fin (n + 4)) = s 2 := by
  rw [show (3 : Fin (n + 4)) = Fin.succ 2 by rfl, Fin.cases_succ]

private theorem finCasesFour {n : ℕ} {C : Sort*} (z : C) (s : Fin (n + 4) → C) :
    Fin.cases z s (4 : Fin (n + 5)) = s 3 := by
  rw [show (4 : Fin (n + 5)) = Fin.succ 3 by rfl, Fin.cases_succ]

set_option maxHeartbeats 4000000 in
/-- Every reduced index has total multiplicity four in the permutation sum.
This is the finite combinatorial step reducing 120 summands to 30. -/
theorem sum_reducedIndexOfPerm (f : Fin 5 × Fin 5 × Fin 5 → ℂ) :
    ∑ σ : Equiv.Perm (Fin 5), f (reducedIndexOfPerm σ) =
      4 * ∑ t ∈ reducedIndices, f t := by
  classical
  simp only [reducedIndices, Finset.sum_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product]
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
  simp [Fin.sum_univ_succ, reducedIndexOfPerm, decomposeFinSymm_apply,
    finCasesOne, finCasesTwo, finCasesThree, finCasesFour,
    Equiv.swap_apply_def, min_def, max_def]
  ring

/-- Lehmer-code enumeration of all permutations of five labels. -/
private def permOfLehmer5 (a : Fin 5) (b : Fin 4) (c : Fin 3) (d : Fin 2) :
    Equiv.Perm (Fin 5) :=
  Equiv.Perm.decomposeFin.symm
    (a, Equiv.Perm.decomposeFin.symm
      (b, Equiv.Perm.decomposeFin.symm
        (c, Equiv.Perm.decomposeFin.symm (d, 1))))

private theorem exists_permOfLehmer5 (σ : Equiv.Perm (Fin 5)) :
    ∃ a b c d, σ = permOfLehmer5 a b c d := by
  rcases h5 : Equiv.Perm.decomposeFin σ with ⟨a, σ4⟩
  rcases h4 : Equiv.Perm.decomposeFin σ4 with ⟨b, σ3⟩
  rcases h3 : Equiv.Perm.decomposeFin σ3 with ⟨c, σ2⟩
  rcases h2 : Equiv.Perm.decomposeFin σ2 with ⟨d, σ1⟩
  have h1 : σ1 = 1 := Subsingleton.elim _ _
  refine ⟨a, b, c, d, ?_⟩
  have hs5 := (Equiv.Perm.decomposeFin.symm_apply_apply σ).symm
  have hs4 := (Equiv.Perm.decomposeFin.symm_apply_apply σ4).symm
  have hs3 := (Equiv.Perm.decomposeFin.symm_apply_apply σ3).symm
  have hs2 := (Equiv.Perm.decomposeFin.symm_apply_apply σ2).symm
  rw [h5] at hs5
  rw [h4] at hs4
  rw [h3] at hs3
  rw [h2] at hs2
  rw [hs5, hs4, hs3, hs2, h1]
  rfl

set_option maxHeartbeats 4000000 in
/-- Every ordered four-bracket of distinct labels is nonzero on the generic
five-point chart. -/
theorem orderedBracket_matrix5_ne_zero (q : U5) (i j k l : Fin 5)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    orderedBracket (matrix5 q.1) i j k l ≠ 0 := by
  have hp0 := q.2.p0_ne
  have hp1 := q.2.p1_ne
  have hp2 := q.2.p2_ne
  have hp3 := q.2.p3_ne
  have hp4 := q.2.p4_ne
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp_all [orderedBracket, matrix5, p0, p1, p2, p3, p4] <;>
    intro hzero <;>
    first
    | exact hp0 (by first | linear_combination hzero | linear_combination -hzero)
    | exact hp1 (by first | linear_combination hzero | linear_combination -hzero)
    | exact hp2 (by first | linear_combination hzero | linear_combination -hzero)
    | exact hp3 (by first | linear_combination hzero | linear_combination -hzero)
    | exact hp4 (by first | linear_combination hzero | linear_combination -hzero)

set_option maxHeartbeats 4000000 in
/-- The signed summand attached to a permutation is exactly the corresponding
summand of the reduced formula. -/
theorem rawTerm_eq_reducedTerm (q : U5) (σ : Equiv.Perm (Fin 5)) :
    rawTerm (matrix5 q.1) σ =
      reducedTerm (matrix5 q.1) (reducedIndexOfPerm σ) := by
  rcases exists_permOfLehmer5 σ with ⟨a, b, c, d, rfl⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp only [rawTerm, reducedIndexOfPerm, permOfLehmer5,
      decomposeFinSymm_apply, finCasesOne, finCasesTwo, finCasesThree,
      finCasesFour, Equiv.Perm.decomposeFin.symm_sign, Equiv.swap_apply_def] <;>
    simp only [reducedTerm, complementaryPfProduct, Fin.prod_univ_succ] <;>
    simp <;>
    simp only [affineDifference] <;>
    field_simp [orderedBracket_matrix5_ne_zero q, q.2.p0_ne, q.2.p1_ne,
      q.2.p2_ne, q.2.p3_ne, q.2.p4_ne] <;>
    simp [orderedBracket, matrix5, p0, p1, p2, p3, p4] <;>
    ring

/-- On the generic five-point chart, the original 120-term alternating average
is exactly the paper's thirty-term normalized formula. -/
theorem rawAlternationR_eq_reducedR (q : U5) :
    rawAlternationR (matrix5 q.1) = reducedR (matrix5 q.1) := by
  rw [rawAlternationR]
  simp_rw [rawTerm_eq_reducedTerm q]
  rw [sum_reducedIndexOfPerm, reducedR]
  ring

end

end AffineCocycle

end Sp4
