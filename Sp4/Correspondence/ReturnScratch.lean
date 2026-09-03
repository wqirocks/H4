import Sp4.Correspondence.Genericity

/-!
# Dyadic radial return

Exact word representatives and the quantitative arithmetic used in the
compact-return argument.
-/

namespace Sp4
namespace Pfaffian

noncomputable section

open scoped Matrix Topology
open Filter

def vWord : List CorrLetter := [.CInv, .U, .C]
def vInvWord : List CorrLetter := [.CInv, .UInv, .C]

/-- Execution-order representative of
`U⁴ V U² V⁻² U⁻²`. -/
def radialWord : List CorrLetter :=
  [.UInv, .UInv] ++ vInvWord ++ vInvWord ++ [.U, .U] ++ vWord ++
    [.U, .U, .U, .U]

def inverseLetter : CorrLetter → CorrLetter
  | .U => .UInv
  | .UInv => .U
  | .C => .CInv
  | .CInv => .C
  | .rho => .rho

/-- Reverse execution order and invert every letter. -/
def inverseWord (word : List CorrLetter) : List CorrLetter :=
  (word.map inverseLetter).reverse

def radialWordInv : List CorrLetter := inverseWord radialWord

@[simp]
theorem radialWord_length : radialWord.length = 17 := by decide

@[simp]
theorem radialWordInv_length : radialWordInv.length = 17 := by decide

def radiusR : Mat2R := !![2, 0; 0, 1 / 2]
def radiusRInv : Mat2R := !![1 / 2, 0; 0, 2]

theorem radialWord_matrix : wordRadiusMatrix radialWord = radiusR := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [radialWord, vWord, vInvWord, wordRadiusMatrix,
      letterRadiusMatrix, radiusU, radiusUInv, radiusC, radiusCInv,
      radiusR, Matrix.mul_apply, Fin.sum_univ_two]

theorem radialWordInv_matrix : wordRadiusMatrix radialWordInv = radiusRInv := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [radialWordInv, inverseWord, radialWord, vWord, vInvWord,
      inverseLetter, wordRadiusMatrix, letterRadiusMatrix, radiusU, radiusUInv,
      radiusC, radiusCInv, radiusRInv, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem radiusR_mul_radiusRInv : radiusR * radiusRInv = (1 : Mat2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [radiusR, radiusRInv, Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem radiusRInv_mul_radiusR : radiusRInv * radiusR = (1 : Mat2R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [radiusR, radiusRInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem wordRadiusMatrix_append (u v : List CorrLetter) :
    wordRadiusMatrix (u ++ v) = wordRadiusMatrix v * wordRadiusMatrix u := by
  induction u with
  | nil => simp [wordRadiusMatrix]
  | cons letter u ih =>
      simp [wordRadiusMatrix, ih, Matrix.mul_assoc]

/-- Execute the same word `n` times. -/
def wordPower (word : List CorrLetter) : ℕ → List CorrLetter
  | 0 => []
  | n + 1 => word ++ wordPower word n

@[simp]
theorem wordPower_length (word : List CorrLetter) (n : ℕ) :
    (wordPower word n).length = n * word.length := by
  induction n with
  | zero => simp [wordPower]
  | succ n ih => simp [wordPower, ih, Nat.succ_mul, Nat.add_comm]

theorem wordPower_matrix (word : List CorrLetter) (n : ℕ) :
    wordRadiusMatrix (wordPower word n) = wordRadiusMatrix word ^ n := by
  induction n with
  | zero => simp [wordPower, wordRadiusMatrix]
  | succ n ih =>
      rw [wordPower, wordRadiusMatrix_append, ih, pow_succ]

theorem radialWordPower_matrix (n : ℕ) :
    wordRadiusMatrix (wordPower radialWord n) = radiusR ^ n := by
  rw [wordPower_matrix, radialWord_matrix]

theorem radialWordInvPower_matrix (n : ℕ) :
    wordRadiusMatrix (wordPower radialWordInv n) = radiusRInv ^ n := by
  rw [wordPower_matrix, radialWordInv_matrix]

/-! ## One-bit dyadic shear words -/

def radiusShear (t : ℝ) : Mat2R := !![1, t; 0, 1]

theorem radiusRInv_conjugates_shear (t : ℝ) :
    radiusRInv * radiusShear t * radiusR = radiusShear (t / 4) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [radiusRInv, radiusR, radiusShear, Matrix.mul_apply,
      Fin.sum_univ_two] <;> ring

/-- A word for the single dyadic digit `u(2⁻ᵐ)`. -/
def dyadicDigitWord : ℕ → List CorrLetter
  | 0 => [.U, .U]
  | 1 => [.U]
  | m + 2 => radialWord ++ dyadicDigitWord m ++ radialWordInv

theorem dyadicDigitWord_matrix (m : ℕ) :
    wordRadiusMatrix (dyadicDigitWord m) =
      radiusShear (1 / (2 : ℝ) ^ m) := by
  induction m using Nat.twoStepInduction with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [dyadicDigitWord, wordRadiusMatrix, letterRadiusMatrix,
          radiusU, radiusShear, Matrix.mul_apply, Fin.sum_univ_two]
  | one =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [dyadicDigitWord, wordRadiusMatrix, letterRadiusMatrix,
          radiusU, radiusShear, Matrix.mul_apply, Fin.sum_univ_two]
  | more m ihm _ =>
      rw [dyadicDigitWord, wordRadiusMatrix_append, wordRadiusMatrix_append,
        radialWordInv_matrix, radialWord_matrix, ihm,
        ← Matrix.mul_assoc, radiusRInv_conjugates_shear]
      congr 1
      rw [pow_add]
      norm_num
      field_simp

theorem dyadicDigitWord_length_bound (m : ℕ) :
    (dyadicDigitWord m).length ≤ 34 * m + 2 := by
  induction m using Nat.twoStepInduction with
  | zero => simp [dyadicDigitWord]
  | one => simp [dyadicDigitWord]
  | more m ihm _ =>
      simp [dyadicDigitWord, ihm]
      omega

theorem radiusShear_mul (s t : ℝ) :
    radiusShear s * radiusShear t = radiusShear (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radiusShear, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def dyadicBitsValue (m : ℕ) (bits : List ℕ) : ℝ :=
  (bits.map fun i => 1 / (2 : ℝ) ^ (m - i)).sum

def dyadicBitsWord (m k : ℕ) : List CorrLetter :=
  k.bitIndices.flatMap fun i => dyadicDigitWord (m - i)

private theorem dyadicBitsWord_matrix_aux (m : ℕ) (bits : List ℕ) :
    wordRadiusMatrix (bits.flatMap fun i => dyadicDigitWord (m - i)) =
      radiusShear (dyadicBitsValue m bits) := by
  induction bits with
  | nil =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [wordRadiusMatrix, dyadicBitsValue, radiusShear]
  | cons i bits ih =>
      rw [List.flatMap_cons, wordRadiusMatrix_append,
        dyadicDigitWord_matrix, ih, radiusShear_mul]
      simp [dyadicBitsValue, add_comm]

private theorem dyadic_digit_value_eq (m i : ℕ) (hi : i ≤ m) :
    (1 / (2 : ℝ) ^ (m - i)) = (2 : ℝ) ^ i / (2 : ℝ) ^ m := by
  have hp : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - i) * (2 : ℝ) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi]
  rw [hp]
  field_simp

private theorem dyadicBitsValue_eq_sum_div (m : ℕ) (bits : List ℕ)
    (hbits : ∀ i ∈ bits, i ≤ m) :
    dyadicBitsValue m bits =
      ((bits.map fun i => 2 ^ i).sum : ℕ) / (2 : ℝ) ^ m := by
  induction bits with
  | nil => simp [dyadicBitsValue]
  | cons i bits ih =>
      have hi : i ≤ m := hbits i (by simp)
      have htail : ∀ j ∈ bits, j ≤ m := by
        intro j hj
        exact hbits j (by simp [hj])
      rw [dyadicBitsValue]
      simp only [List.map_cons, List.sum_cons]
      rw [dyadic_digit_value_eq m i hi]
      have iht := ih htail
      rw [show (bits.map fun j => 1 / (2 : ℝ) ^ (m - j)).sum =
          dyadicBitsValue m bits by rfl, iht]
      push_cast
      ring

theorem bitIndex_le_of_lt_two_pow_succ {k m i : ℕ}
    (hk : k < 2 ^ (m + 1)) (hi : i ∈ k.bitIndices) : i ≤ m := by
  have hipow : 2 ^ i < 2 ^ (m + 1) :=
    (Nat.two_pow_le_of_mem_bitIndices hi).trans_lt hk
  have him : i < m + 1 :=
    (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp hipow
  omega

theorem dyadicBitsWord_matrix (m k : ℕ) (hk : k < 2 ^ (m + 1)) :
    wordRadiusMatrix (dyadicBitsWord m k) =
      radiusShear ((k : ℝ) / (2 : ℝ) ^ m) := by
  rw [dyadicBitsWord, dyadicBitsWord_matrix_aux]
  congr 1
  rw [dyadicBitsValue_eq_sum_div]
  · simp
  · intro i hi
    exact bitIndex_le_of_lt_two_pow_succ hk hi

private theorem flatMap_length_le (f : ℕ → List CorrLetter) (bits : List ℕ)
    (B : ℕ) (hf : ∀ i ∈ bits, (f i).length ≤ B) :
    (bits.flatMap f).length ≤ bits.length * B := by
  induction bits with
  | nil => simp
  | cons i bits ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hi := hf i (by simp)
      have htail : ∀ j ∈ bits, (f j).length ≤ B := by
        intro j hj
        exact hf j (by simp [hj])
      have hih := ih htail
      calc
        (f i).length + (bits.flatMap f).length ≤ B + bits.length * B :=
          Nat.add_le_add hi hih
        _ = (bits.length + 1) * B := by
          rw [Nat.add_mul, one_mul, Nat.add_comm]

theorem bitIndices_length_le (m k : ℕ) (hk : k < 2 ^ (m + 1)) :
    k.bitIndices.length ≤ m + 1 := by
  have hsubset : k.bitIndices.toFinset ⊆ Finset.range (m + 1) := by
    intro i hi
    simp only [List.mem_toFinset] at hi
    simp only [Finset.mem_range]
    exact Nat.lt_succ_iff.mpr (bitIndex_le_of_lt_two_pow_succ hk hi)
  calc
    k.bitIndices.length = k.bitIndices.toFinset.card := by
      symm
      exact List.toFinset_card_of_nodup Nat.bitIndices_nodup
    _ ≤ (Finset.range (m + 1)).card := Finset.card_le_card hsubset
    _ = m + 1 := Finset.card_range _

/-- An explicit quadratic word-length bound for a numerator whose binary
digits do not exceed the denominator exponent. -/
theorem dyadicBitsWord_length_bound (m k : ℕ) (hk : k < 2 ^ (m + 1)) :
    (dyadicBitsWord m k).length ≤ (m + 1) * (34 * m + 2) := by
  rw [dyadicBitsWord]
  have hflat := flatMap_length_le
    (fun i => dyadicDigitWord (m - i)) k.bitIndices (34 * m + 2) (by
      intro i hi
      have him := bitIndex_le_of_lt_two_pow_succ hk hi
      calc
        (dyadicDigitWord (m - i)).length ≤ 34 * (m - i) + 2 :=
          dyadicDigitWord_length_bound _
        _ ≤ 34 * m + 2 := by omega)
  exact hflat.trans (Nat.mul_le_mul_right _ (bitIndices_length_le m k hk))

def negativeDyadicDigitWord : ℕ → List CorrLetter
  | 0 => [.UInv, .UInv]
  | 1 => [.UInv]
  | m + 2 => radialWord ++ negativeDyadicDigitWord m ++ radialWordInv

theorem negativeDyadicDigitWord_matrix (m : ℕ) :
    wordRadiusMatrix (negativeDyadicDigitWord m) =
      radiusShear (-(1 / (2 : ℝ) ^ m)) := by
  induction m using Nat.twoStepInduction with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [negativeDyadicDigitWord, wordRadiusMatrix, letterRadiusMatrix,
          radiusUInv, radiusShear, Matrix.mul_apply, Fin.sum_univ_two]
  | one =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [negativeDyadicDigitWord, wordRadiusMatrix, letterRadiusMatrix,
          radiusUInv, radiusShear, Matrix.mul_apply, Fin.sum_univ_two]
  | more m ihm _ =>
      rw [negativeDyadicDigitWord, wordRadiusMatrix_append,
        wordRadiusMatrix_append, radialWordInv_matrix, radialWord_matrix, ihm,
        ← Matrix.mul_assoc, radiusRInv_conjugates_shear]
      congr 1
      rw [pow_add]
      norm_num
      field_simp

theorem negativeDyadicDigitWord_length_bound (m : ℕ) :
    (negativeDyadicDigitWord m).length ≤ 34 * m + 2 := by
  induction m using Nat.twoStepInduction with
  | zero => simp [negativeDyadicDigitWord]
  | one => simp [negativeDyadicDigitWord]
  | more m ihm _ =>
      simp [negativeDyadicDigitWord]
      have := ihm
      omega

def negativeDyadicBitsWord (m k : ℕ) : List CorrLetter :=
  k.bitIndices.flatMap fun i => negativeDyadicDigitWord (m - i)

private theorem negativeDyadicBitsWord_matrix_aux (m : ℕ) (bits : List ℕ) :
    wordRadiusMatrix (bits.flatMap fun i => negativeDyadicDigitWord (m - i)) =
      radiusShear (-dyadicBitsValue m bits) := by
  induction bits with
  | nil =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [wordRadiusMatrix, dyadicBitsValue, radiusShear]
  | cons i bits ih =>
      rw [List.flatMap_cons, wordRadiusMatrix_append,
        negativeDyadicDigitWord_matrix, ih, radiusShear_mul]
      simp [dyadicBitsValue]

theorem negativeDyadicBitsWord_matrix (m k : ℕ) (hk : k < 2 ^ (m + 1)) :
    wordRadiusMatrix (negativeDyadicBitsWord m k) =
      radiusShear (-((k : ℝ) / (2 : ℝ) ^ m)) := by
  rw [negativeDyadicBitsWord, negativeDyadicBitsWord_matrix_aux]
  congr 1
  rw [dyadicBitsValue_eq_sum_div]
  · simp
  · intro i hi
    exact bitIndex_le_of_lt_two_pow_succ hk hi

theorem negativeDyadicBitsWord_length_bound (m k : ℕ)
    (hk : k < 2 ^ (m + 1)) :
    (negativeDyadicBitsWord m k).length ≤ (m + 1) * (34 * m + 2) := by
  rw [negativeDyadicBitsWord]
  have hflat := flatMap_length_le
    (fun i => negativeDyadicDigitWord (m - i)) k.bitIndices (34 * m + 2) (by
      intro i hi
      have him := bitIndex_le_of_lt_two_pow_succ hk hi
      calc
        (negativeDyadicDigitWord (m - i)).length ≤ 34 * (m - i) + 2 :=
          negativeDyadicDigitWord_length_bound _
        _ ≤ 34 * m + 2 := by omega)
  exact hflat.trans (Nat.mul_le_mul_right _ (bitIndices_length_le m k hk))

def integerDyadicWord (m : ℕ) : ℤ → List CorrLetter
  | .ofNat k => dyadicBitsWord m k
  | .negSucc k => negativeDyadicBitsWord m (k + 1)

theorem integerDyadicWord_matrix (m : ℕ) (k : ℤ)
    (hk : k.natAbs < 2 ^ (m + 1)) :
    wordRadiusMatrix (integerDyadicWord m k) =
      radiusShear ((k : ℝ) / (2 : ℝ) ^ m) := by
  cases k with
  | ofNat k =>
      simpa [integerDyadicWord] using dyadicBitsWord_matrix m k hk
  | negSucc k =>
      rw [integerDyadicWord, negativeDyadicBitsWord_matrix m (k + 1) hk]
      congr 1
      push_cast
      ring

theorem integerDyadicWord_length_bound (m : ℕ) (k : ℤ)
    (hk : k.natAbs < 2 ^ (m + 1)) :
    (integerDyadicWord m k).length ≤ (m + 1) * (34 * m + 2) := by
  cases k with
  | ofNat k =>
      exact dyadicBitsWord_length_bound m k hk
  | negSucc k =>
      exact negativeDyadicBitsWord_length_bound m (k + 1) hk

/-! ## The complete radial-return word -/

def returnWord (n : ℕ) (k : ℤ) : List CorrLetter :=
  integerDyadicWord (2 * n) (-k) ++ wordPower radialWord n

theorem returnWord_matrix (n : ℕ) (k : ℤ)
    (hk : k.natAbs < 2 ^ (2 * n + 1)) :
    wordRadiusMatrix (returnWord n k) =
      radiusR ^ n * radiusShear (-((k : ℝ) / (2 : ℝ) ^ (2 * n))) := by
  rw [returnWord, wordRadiusMatrix_append, radialWordPower_matrix,
    integerDyadicWord_matrix]
  · congr 2
    push_cast
    ring
  · simpa using hk

theorem returnWord_length_bound (n : ℕ) (k : ℤ)
    (hk : k.natAbs < 2 ^ (2 * n + 1)) :
    (returnWord n k).length ≤
      (2 * n + 1) * (34 * (2 * n) + 2) + 17 * n := by
  have hs := integerDyadicWord_length_bound (2 * n) (-k) (by simpa using hk)
  calc
    (returnWord n k).length =
        (integerDyadicWord (2 * n) (-k)).length + 17 * n := by
      simp [returnWord, wordPower_length, Nat.mul_comm]
    _ ≤ (2 * n + 1) * (34 * (2 * n) + 2) + 17 * n :=
      Nat.add_le_add_right hs _

/-! The explicit return words use no `rho`, hence they preserve rather than
reverse the sign of an alternating function. -/

theorem wordSign_eq_one_of_rho_not_mem {word : List CorrLetter}
    (hword : CorrLetter.rho ∉ word) : wordSign word = 1 := by
  induction word with
  | nil => simp [wordSign]
  | cons letter word ih =>
      have hletter : letter ≠ CorrLetter.rho := by
        intro h
        apply hword
        simp [h]
      have htail : CorrLetter.rho ∉ word := by
        intro h
        exact hword (by simp [h])
      cases letter <;> simp_all [wordSign, letterSign]

theorem wordUCount_le_length (word : List CorrLetter) :
    wordUCount word ≤ word.length := by
  induction word with
  | nil => simp [wordUCount]
  | cons letter word ih =>
      cases letter <;> simp [wordUCount, letterUCount] <;> omega

theorem rho_not_mem_radialWord : CorrLetter.rho ∉ radialWord := by
  decide

theorem rho_not_mem_radialWordInv : CorrLetter.rho ∉ radialWordInv := by
  decide

theorem rho_not_mem_dyadicDigitWord (m : ℕ) :
    CorrLetter.rho ∉ dyadicDigitWord m := by
  induction m using Nat.twoStepInduction with
  | zero => simp [dyadicDigitWord]
  | one => simp [dyadicDigitWord]
  | more m ihm _ =>
      simp [dyadicDigitWord, rho_not_mem_radialWord,
        rho_not_mem_radialWordInv, ihm]

theorem rho_not_mem_negativeDyadicDigitWord (m : ℕ) :
    CorrLetter.rho ∉ negativeDyadicDigitWord m := by
  induction m using Nat.twoStepInduction with
  | zero => simp [negativeDyadicDigitWord]
  | one => simp [negativeDyadicDigitWord]
  | more m ihm _ =>
      simp [negativeDyadicDigitWord, rho_not_mem_radialWord,
        rho_not_mem_radialWordInv, ihm]

theorem rho_not_mem_dyadicBitsWord (m k : ℕ) :
    CorrLetter.rho ∉ dyadicBitsWord m k := by
  simp [dyadicBitsWord, rho_not_mem_dyadicDigitWord]

theorem rho_not_mem_negativeDyadicBitsWord (m k : ℕ) :
    CorrLetter.rho ∉ negativeDyadicBitsWord m k := by
  simp [negativeDyadicBitsWord, rho_not_mem_negativeDyadicDigitWord]

theorem rho_not_mem_integerDyadicWord (m : ℕ) (k : ℤ) :
    CorrLetter.rho ∉ integerDyadicWord m k := by
  cases k with
  | ofNat k => exact rho_not_mem_dyadicBitsWord m k
  | negSucc k => exact rho_not_mem_negativeDyadicBitsWord m (k + 1)

theorem rho_not_mem_wordPower_radialWord (n : ℕ) :
    CorrLetter.rho ∉ wordPower radialWord n := by
  induction n with
  | zero => simp [wordPower]
  | succ n ih => simp [wordPower, rho_not_mem_radialWord, ih]

theorem rho_not_mem_returnWord (n : ℕ) (k : ℤ) :
    CorrLetter.rho ∉ returnWord n k := by
  simp [returnWord, rho_not_mem_integerDyadicWord,
    rho_not_mem_wordPower_radialWord]

@[simp]
theorem returnWord_sign (n : ℕ) (k : ℤ) :
    wordSign (returnWord n k) = 1 :=
  wordSign_eq_one_of_rho_not_mem (rho_not_mem_returnWord n k)

theorem radiusR_pow (n : ℕ) :
    radiusR ^ n = !![(2 : ℝ) ^ n, 0; 0, (1 / 2 : ℝ) ^ n] := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp [radiusR]
  | succ n ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [radiusR, Matrix.mul_apply, Fin.sum_univ_two, pow_succ] <;> ring

theorem radiusShear_mulVec_pair (t a b : ℝ) :
    radiusShear t *ᵥ ![a, b] = ![a + t * b, b] := by
  ext i
  fin_cases i <;> simp [radiusShear] <;> ring

theorem radiusR_pow_mulVec_pair (n : ℕ) (a b : ℝ) :
    radiusR ^ n *ᵥ ![a, b] =
      ![(2 : ℝ) ^ n * a, (1 / 2 : ℝ) ^ n * b] := by
  rw [radiusR_pow]
  ext i
  fin_cases i <;> simp <;> ring

theorem returnWord_matrix_action (a b : ℝ) (n : ℕ) (k : ℤ)
    (hk : k.natAbs < 2 ^ (2 * n + 1)) :
    wordRadiusMatrix (returnWord n k) *ᵥ
        ![a, (2 : ℝ) ^ n * b] =
      ![(2 : ℝ) ^ n *
          (a - ((k : ℝ) / (2 : ℝ) ^ (2 * n)) * (2 : ℝ) ^ n * b), b] := by
  rw [returnWord_matrix n k hk, ← Matrix.mulVec_mulVec,
    radiusShear_mulVec_pair, radiusR_pow_mulVec_pair]
  have hinvpow : (1 / 2 : ℝ) ^ n * (2 : ℝ) ^ n = 1 := by
    rw [← mul_pow]
    norm_num
  ext i
  fin_cases i <;>
    simp [hinvpow] <;> ring

/-! ## Iterating the first dilation -/

def radiusT1 : Mat2R := !![1, 0; 0, 2]

theorem logRadius_sourceU_dilation (q : TorusPoint) :
    logRadius (sourceU q) = radiusT1 *ᵥ logRadius q := by
  funext i
  fin_cases i <;>
    simp [logRadius, sourceU, sourceUCoord, radiusT1, Matrix.mulVec,
      Fin.sum_univ_two, Real.log_pow] <;> ring

theorem logRadius_sourceU_iterate (q : TorusPoint) (n : ℕ) :
    logRadius ((sourceU^[n]) q) = radiusT1 ^ n *ᵥ logRadius q := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', logRadius_sourceU_dilation, ih,
        Matrix.mulVec_mulVec, pow_succ']

theorem radiusT1_pow (n : ℕ) :
    radiusT1 ^ n = !![(1 : ℝ), 0; 0, (2 : ℝ) ^ n] := by
  induction n with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;> simp [radiusT1]
  | succ n ih =>
      rw [pow_succ, ih]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [radiusT1, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

theorem logRadius_sourceU_iterate_apply_zero (q : TorusPoint) (n : ℕ) :
    logRadius ((sourceU^[n]) q) 0 = logRadius q 0 := by
  rw [logRadius_sourceU_iterate, radiusT1_pow]
  simp [logRadius]

theorem logRadius_sourceU_iterate_apply_one (q : TorusPoint) (n : ℕ) :
    logRadius ((sourceU^[n]) q) 1 = (2 : ℝ) ^ n * logRadius q 1 := by
  rw [logRadius_sourceU_iterate, radiusT1_pow]
  simp [logRadius]
  ring

/-- Every lift of the return word from a fully generic iterate is admissible,
and its endpoint has the branch-independent radial-return coordinates. -/
theorem exists_admissible_returnLift (z : TorusPoint) (hz : FullyGeneric z)
    (n : ℕ) (k : ℤ) (hk : k.natAbs < 2 ^ (2 * n + 1)) :
    ∃ y : TorusPoint,
      ∃ e : WordLift (returnWord n k) ((sourceU^[n]) z) y,
        e.Admissible ∧
          logRadius y =
            ![(2 : ℝ) ^ n *
                (logRadius z 0 -
                  ((k : ℝ) / (2 : ℝ) ^ (2 * n)) *
                    (2 : ℝ) ^ n * logRadius z 1),
              logRadius z 1] := by
  obtain ⟨y, ⟨e⟩⟩ := exists_wordLift (returnWord n k) ((sourceU^[n]) z)
  refine ⟨y, e, hz.everyLift n (returnWord n k) e, ?_⟩
  have hinput : logRadius ((sourceU^[n]) z) =
      ![logRadius z 0, (2 : ℝ) ^ n * logRadius z 1] := by
    funext i
    fin_cases i
    · exact logRadius_sourceU_iterate_apply_zero z n
    · exact logRadius_sourceU_iterate_apply_one z n
  rw [e.logRadius_terminal, hinput,
    returnWord_matrix_action (logRadius z 0) (logRadius z 1) n k hk]

/-! ## Nearest dyadic approximation -/

def nearestDyadicNumerator (x : ℝ) (N : ℕ) : ℤ :=
  round ((2 : ℝ) ^ N * x)

theorem nearestDyadicNumerator_error (x : ℝ) (N : ℕ) :
    |(nearestDyadicNumerator x N : ℝ) / (2 : ℝ) ^ N - x| ≤
      (1 / 2 : ℝ) / (2 : ℝ) ^ N := by
  let d : ℝ := (2 : ℝ) ^ N
  have hd : 0 < d := by positivity
  have hround :
      |d * x - (nearestDyadicNumerator x N : ℝ)| ≤ (1 / 2 : ℝ) := by
    simpa [nearestDyadicNumerator, d] using
      (abs_sub_round (d * x) :
        |d * x - (round (d * x) : ℝ)| ≤ (1 / 2 : ℝ))
  rw [show (nearestDyadicNumerator x N : ℝ) / (2 : ℝ) ^ N - x =
      -(d * x - (nearestDyadicNumerator x N : ℝ)) / d by
    dsimp [d]
    field_simp
    ring]
  rw [abs_div, abs_neg, abs_of_pos hd]
  exact div_le_div_of_nonneg_right hround hd.le

theorem nearestDyadicNumerator_bound (x : ℝ) (N : ℕ) :
    |(nearestDyadicNumerator x N : ℝ)| ≤
      (2 : ℝ) ^ N * |x| + 1 / 2 := by
  let d : ℝ := (2 : ℝ) ^ N
  have hd : 0 < d := by positivity
  have hround :
      |d * x - (nearestDyadicNumerator x N : ℝ)| ≤ (1 / 2 : ℝ) := by
    simpa [nearestDyadicNumerator, d] using
      (abs_sub_round (d * x) :
        |d * x - (round (d * x) : ℝ)| ≤ (1 / 2 : ℝ))
  calc
    |(nearestDyadicNumerator x N : ℝ)| =
        |d * x - (d * x - (nearestDyadicNumerator x N : ℝ))| := by ring_nf
    _ ≤ |d * x| + |d * x - (nearestDyadicNumerator x N : ℝ)| := abs_sub _ _
    _ ≤ d * |x| + 1 / 2 := by
      rw [abs_mul, abs_of_pos hd]
      simpa [add_comm] using add_le_add_left hround (d * |x|)
    _ = (2 : ℝ) ^ N * |x| + 1 / 2 := by rfl

theorem exists_dyadic_approximation (x : ℝ) (N : ℕ) :
    ∃ k : ℤ,
      |(k : ℝ) / (2 : ℝ) ^ N - x| ≤ (1 / 2 : ℝ) / (2 : ℝ) ^ N ∧
      |(k : ℝ)| ≤ (2 : ℝ) ^ N * |x| + 1 / 2 := by
  exact ⟨nearestDyadicNumerator x N,
    nearestDyadicNumerator_error x N,
    nearestDyadicNumerator_bound x N⟩

theorem radial_return_first_coordinate_bound
    (a b : ℝ) (hb : b ≠ 0) (n : ℕ) (k : ℤ)
    (happrox :
      |(k : ℝ) / (2 : ℝ) ^ (2 * n) -
          a / ((2 : ℝ) ^ n * b)| ≤
        (1 / 2 : ℝ) / (2 : ℝ) ^ (2 * n)) :
    |(2 : ℝ) ^ n *
        (a - ((k : ℝ) / (2 : ℝ) ^ (2 * n)) * (2 : ℝ) ^ n * b)| ≤
      |b| / 2 := by
  let d : ℝ := (2 : ℝ) ^ n
  let D : ℝ := (2 : ℝ) ^ (2 * n)
  have hd : 0 < d := by positivity
  have hD : 0 < D := by positivity
  have hpow : D = d ^ 2 := by
    dsimp [D, d]
    rw [show 2 * n = n * 2 by omega, pow_mul]
  let q : ℝ := (k : ℝ) / D
  have hq : |q - a / (d * b)| ≤ (1 / 2 : ℝ) / D := by
    simpa [q, d, D] using happrox
  have halg : d * (a - q * d * b) = -(D * b) * (q - a / (d * b)) := by
    rw [hpow]
    field_simp [hb, ne_of_gt hd]
    ring
  rw [show (k : ℝ) / (2 : ℝ) ^ (2 * n) = q by rfl]
  rw [halg, abs_mul, abs_neg, abs_mul, abs_of_pos hD]
  calc
    D * |b| * |q - a / (d * b)| ≤
        D * |b| * ((1 / 2 : ℝ) / D) :=
      mul_le_mul_of_nonneg_left hq (mul_nonneg hD.le (abs_nonneg b))
    _ = |b| / 2 := by field_simp [ne_of_gt hD]

/-- Quantified nearest-integer choice used by compact return. -/
theorem exists_radial_return_numerator (a b : ℝ) (hb : b ≠ 0) (n : ℕ) :
    ∃ k : ℤ,
      |(k : ℝ) / (2 : ℝ) ^ (2 * n) -
          a / ((2 : ℝ) ^ n * b)| ≤
        (1 / 2 : ℝ) / (2 : ℝ) ^ (2 * n) ∧
      |(2 : ℝ) ^ n *
          (a - ((k : ℝ) / (2 : ℝ) ^ (2 * n)) * (2 : ℝ) ^ n * b)| ≤
        |b| / 2 ∧
      |(k : ℝ)| ≤ (2 : ℝ) ^ (2 * n) *
          |a / ((2 : ℝ) ^ n * b)| + 1 / 2 := by
  obtain ⟨k, hk, hkbound⟩ :=
    exists_dyadic_approximation (a / ((2 : ℝ) ^ n * b)) (2 * n)
  exact ⟨k, hk, radial_return_first_coordinate_bound a b hb n k hk, hkbound⟩

theorem exists_radial_return_numerator_simplified
    (a b : ℝ) (hb : b ≠ 0) (n : ℕ) :
    ∃ k : ℤ,
      |(k : ℝ) / (2 : ℝ) ^ (2 * n) -
          a / ((2 : ℝ) ^ n * b)| ≤
        (1 / 2 : ℝ) / (2 : ℝ) ^ (2 * n) ∧
      |(2 : ℝ) ^ n *
          (a - ((k : ℝ) / (2 : ℝ) ^ (2 * n)) * (2 : ℝ) ^ n * b)| ≤
        |b| / 2 ∧
      |(k : ℝ)| ≤ (2 : ℝ) ^ n * |a / b| + 1 / 2 := by
  obtain ⟨k, happrox, hcoord, hk⟩ := exists_radial_return_numerator a b hb n
  refine ⟨k, happrox, hcoord, ?_⟩
  have hd : 0 < (2 : ℝ) ^ n := by positivity
  have hbabs : |b| ≠ 0 := abs_ne_zero.mpr hb
  calc
    |(k : ℝ)| ≤ (2 : ℝ) ^ (2 * n) *
        |a / ((2 : ℝ) ^ n * b)| + 1 / 2 := hk
    _ = (2 : ℝ) ^ n * |a / b| + 1 / 2 := by
      rw [abs_div, abs_mul, abs_of_pos hd, abs_div]
      rw [show (2 : ℝ) ^ (2 * n) = ((2 : ℝ) ^ n) ^ 2 by
        rw [show 2 * n = n * 2 by omega, pow_mul]]
      field_simp [ne_of_gt hd, hbabs]

/-- From some explicit threshold onward, the nearest numerator fits into the
`2n+1` binary positions used by `integerDyadicWord`. -/
theorem radial_return_numerator_eventually_in_range
    (a b : ℝ) (hb : b ≠ 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ k : ℤ,
        |(k : ℝ) / (2 : ℝ) ^ (2 * n) -
            a / ((2 : ℝ) ^ n * b)| ≤
          (1 / 2 : ℝ) / (2 : ℝ) ^ (2 * n) ∧
        |(2 : ℝ) ^ n *
            (a - ((k : ℝ) / (2 : ℝ) ^ (2 * n)) * (2 : ℝ) ^ n * b)| ≤
          |b| / 2 ∧
        k.natAbs < 2 ^ (2 * n + 1) ∧
        |(k : ℝ)| ≤ (2 : ℝ) ^ n * |a / b| + 1 / 2 := by
  obtain ⟨N, hN⟩ := exists_nat_ge |a / b|
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, happrox, hcoord, hk⟩ :=
    exists_radial_return_numerator_simplified a b hb n
  refine ⟨k, happrox, hcoord, ?_, hk⟩
  let d : ℝ := (2 : ℝ) ^ n
  have hd : 0 < d := by positivity
  have hd1 : 1 ≤ d := by
    dsimp [d]
    exact one_le_pow₀ (by norm_num)
  have hncast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnexp : (n : ℝ) < d := by
    dsimp [d]
    exact_mod_cast n.lt_two_pow_self
  have hCd : |a / b| ≤ d := (hN.trans hncast).trans hnexp.le
  have hmul : d * |a / b| ≤ d ^ 2 := by
    nlinarith
  have hkcast : (k.natAbs : ℝ) ≤ d * |a / b| + 1 / 2 := by
    simpa [d] using hk
  have hpow : (2 : ℝ) ^ (2 * n + 1) = 2 * d ^ 2 := by
    rw [pow_add, pow_one]
    dsimp [d]
    rw [show (2 : ℝ) ^ (2 * n) = ((2 : ℝ) ^ n) ^ 2 by
      rw [show 2 * n = n * 2 by omega, pow_mul]]
    ring
  have hkr : (k.natAbs : ℝ) < (2 : ℝ) ^ (2 * n + 1) := by
    rw [hpow]
    nlinarith [sq_nonneg d]
  exact_mod_cast hkr

/-! ## Compact-return package -/

/-- The uniform quadratic bound used below. -/
def returnLengthBound (n : ℕ) : ℕ :=
  (2 * n + 1) * (34 * (2 * n) + 2) + 17 * n

theorem returnWord_length_le_returnLengthBound (n : ℕ) (k : ℤ)
    (hk : k.natAbs < 2 ^ (2 * n + 1)) :
    (returnWord n k).length ≤ returnLengthBound n := by
  exact returnWord_length_bound n k hk

/-- An admissible return lift changes the value of a point-alternating
cochain by at most the number of `U`-letters, and hence by the explicit
quadratic word-length bound. -/
theorem WordLift.return_value_oscillation
    {z y : TorusPoint} {n : ℕ} {k : ℤ}
    (e : WordLift (returnWord n k) ((sourceU^[n]) z) y)
    (he : e.Admissible) (hk : k.natAbs < 2 ^ (2 * n + 1))
    (f : U4 → ℝ) (hf : PointAlt f) (M : ℝ) (hM : 0 ≤ M)
    (hD : ∀ q : U5, |D f q| ≤ M) :
    |f (y.toU4 (e.terminal_generic he)) -
        f (((sourceU^[n]) z).toU4 (e.initial_generic he))| ≤
      2 * M * (returnLengthBound n : ℝ) := by
  have hosc := e.value_oscillation he f hf M hD
  rw [returnWord_sign, one_mul] at hosc
  calc
    |f (y.toU4 (e.terminal_generic he)) -
        f (((sourceU^[n]) z).toU4 (e.initial_generic he))| ≤
        2 * M * (wordUCount (returnWord n k) : ℝ) := hosc
    _ ≤ 2 * M * ((returnWord n k).length : ℝ) := by
      gcongr
      exact_mod_cast wordUCount_le_length (returnWord n k)
    _ ≤ 2 * M * (returnLengthBound n : ℝ) := by
      gcongr
      exact_mod_cast returnWord_length_le_returnLengthBound n k hk

/-- Fully quantified compact return when the second logarithmic radius is
nonzero.  For every sufficiently large dilation level, this supplies a
literal admissible lift, a bounded endpoint, the dyadic numerator bounds,
and the cochain oscillation estimate needed later in the recurrence proof. -/
theorem fullyGeneric_compact_return
    (z : TorusPoint) (hz : FullyGeneric z)
    (hb : logRadius z 1 ≠ 0)
    (f : U4 → ℝ) (hf : PointAlt f) (M : ℝ) (hM : 0 ≤ M)
    (hD : ∀ q : U5, |D f q| ≤ M) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (k : ℤ) (y : TorusPoint)
        (e : WordLift (returnWord n k) ((sourceU^[n]) z) y),
        ∃ he : e.Admissible,
          k.natAbs < 2 ^ (2 * n + 1) ∧
          |(k : ℝ) / (2 : ℝ) ^ (2 * n) -
              logRadius z 0 / ((2 : ℝ) ^ n * logRadius z 1)| ≤
            (1 / 2 : ℝ) / (2 : ℝ) ^ (2 * n) ∧
          |(k : ℝ)| ≤ (2 : ℝ) ^ n *
              |logRadius z 0 / logRadius z 1| + 1 / 2 ∧
          logRadius y 1 = logRadius z 1 ∧
          |logRadius y 0| ≤ |logRadius z 1| / 2 ∧
          (returnWord n k).length ≤ returnLengthBound n ∧
          |f (y.toU4 (e.terminal_generic he)) -
              f (((sourceU^[n]) z).toU4 (e.initial_generic he))| ≤
            2 * M * (returnLengthBound n : ℝ) := by
  obtain ⟨N, hN⟩ := radial_return_numerator_eventually_in_range
    (logRadius z 0) (logRadius z 1) hb
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, happrox, hcoord, hkRange, hkBound⟩ := hN n hn
  obtain ⟨y, e, he, hlog⟩ :=
    exists_admissible_returnLift z hz n k hkRange
  refine ⟨k, y, e, he, hkRange, happrox, hkBound, ?_, ?_,
    returnWord_length_le_returnLengthBound n k hkRange,
    e.return_value_oscillation he hkRange f hf M hM hD⟩
  · have h := congrFun hlog 1
    simpa using h
  · have h := congrFun hlog 0
    rw [h]
    exact hcoord

/-- Degenerate radial case: if the second logarithmic radius is zero, the
initial dilation orbit is already contained in one compact radial fibre, so
the empty return word suffices at every level. -/
theorem fullyGeneric_zero_second_radius_return
    (z : TorusPoint) (hz : FullyGeneric z)
    (hb : logRadius z 1 = 0) (n : ℕ) :
    ∃ e : WordLift ([] : List CorrLetter) ((sourceU^[n]) z) ((sourceU^[n]) z),
      ∃ he : e.Admissible,
        logRadius ((sourceU^[n]) z) = logRadius z ∧
        (wordUCount ([] : List CorrLetter) = 0) := by
  let e : WordLift ([] : List CorrLetter) ((sourceU^[n]) z)
      ((sourceU^[n]) z) := WordLift.nil _
  have he : e.Admissible := hz.everyLift n [] e
  refine ⟨e, he, ?_, by simp [wordUCount]⟩
  funext i
  fin_cases i
  · exact logRadius_sourceU_iterate_apply_zero z n
  · change logRadius ((sourceU^[n]) z) 1 = logRadius z 1
    rw [logRadius_sourceU_iterate_apply_one, hb]
    simp

/-! ## Compact annuli and convergent subsequences -/

def complexNormAnnulus (r R : ℝ) : Set ℂ :=
  {z | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}

def coordNormAnnulus (r R : ℝ) : Set Coord4 :=
  {q | q.x ∈ complexNormAnnulus r R ∧
    q.y ∈ complexNormAnnulus r R}

theorem isCompact_complexNormAnnulus (r R : ℝ) :
    IsCompact (complexNormAnnulus r R) := by
  have hclosed : IsClosed (complexNormAnnulus r R) :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  refine (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hclosed ?_
  intro z hz
  have hzR : ‖z‖ ≤ R := hz.2
  simpa [Metric.mem_closedBall, dist_zero_right] using hzR

theorem isCompact_coordNormAnnulus (r R : ℝ) :
    IsCompact (coordNormAnnulus r R) := by
  have hEq : coordNormAnnulus r R =
      coord4HomeomorphProd ⁻¹'
        (complexNormAnnulus r R ×ˢ complexNormAnnulus r R) := by
    ext q
    rfl
  rw [hEq, coord4HomeomorphProd.isCompact_preimage]
  exact (isCompact_complexNormAnnulus r R).prod
    (isCompact_complexNormAnnulus r R)

theorem TorusPoint.mem_coordNormAnnulus_of_logRadius_abs_le
    (q : TorusPoint) (B : ℝ)
    (hx : |logRadius q 0| ≤ B) (hy : |logRadius q 1| ≤ B) :
    q.1 ∈ coordNormAnnulus (Real.exp (-B)) (Real.exp B) := by
  change |Real.log ‖q.1.x‖| ≤ B at hx
  change |Real.log ‖q.1.y‖| ≤ B at hy
  have hxpos : 0 < ‖q.1.x‖ := norm_pos_iff.mpr q.2.x_ne
  have hypos : 0 < ‖q.1.y‖ := norm_pos_iff.mpr q.2.y_ne
  have hxlower := (Real.exp_le_exp.mpr (abs_le.mp hx).1)
  have hxupper := (Real.exp_le_exp.mpr (abs_le.mp hx).2)
  have hylower := (Real.exp_le_exp.mpr (abs_le.mp hy).1)
  have hyupper := (Real.exp_le_exp.mpr (abs_le.mp hy).2)
  rw [Real.exp_log hxpos] at hxlower hxupper
  rw [Real.exp_log hypos] at hylower hyupper
  exact ⟨⟨hxlower, hxupper⟩, ⟨hylower, hyupper⟩⟩

/-- Coordinatewise logarithmic-radius bounds give a subsequence converging
inside the nonzero torus.  The positive lower annulus radius is what prevents
either coordinate of the limit from vanishing. -/
theorem exists_tendsto_subsequence_of_logRadius_bounded
    (y : ℕ → TorusPoint) (B : ℝ)
    (hy : ∀ n : ℕ, |logRadius (y n) 0| ≤ B ∧
      |logRadius (y n) 1| ≤ B) :
    ∃ q : TorusPoint,
      q.1 ∈ coordNormAnnulus (Real.exp (-B)) (Real.exp B) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (y ∘ φ) atTop (𝓝 q) := by
  have hmem : ∀ n : ℕ,
      (y n).1 ∈ coordNormAnnulus (Real.exp (-B)) (Real.exp B) := by
    intro n
    exact (y n).mem_coordNormAnnulus_of_logRadius_abs_le B
      (hy n).1 (hy n).2
  obtain ⟨q, hq, φ, hφ, hlim⟩ :=
    (isCompact_coordNormAnnulus (Real.exp (-B)) (Real.exp B)).tendsto_subseq hmem
  have hqx : q.x ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact ne_of_gt ((Real.exp_pos (-B)).trans_le hq.1.1)
  have hqy : q.y ≠ 0 := by
    apply norm_ne_zero_iff.mp
    exact ne_of_gt ((Real.exp_pos (-B)).trans_le hq.2.1)
  let qt : TorusPoint := ⟨q, ⟨hqx, hqy⟩⟩
  refine ⟨qt, hq, φ, hφ, ?_⟩
  rw [tendsto_subtype_rng]
  exact hlim

/-! ## Uniform return data and a precompact subsequence -/

/-- A single admissible compact-return path at dilation level `n`.  The word
is kept abstract here so that the same structure covers the nonzero-radius
construction and the empty word used in the degenerate case. -/
structure BoundedReturnDatum (z : TorusPoint) (f : U4 → ℝ)
    (M B : ℝ) (n : ℕ) where
  word : List CorrLetter
  endpoint : TorusPoint
  lift : WordLift word ((sourceU^[n]) z) endpoint
  admissible : lift.Admissible
  radius_bound : |logRadius endpoint 0| ≤ B ∧
    |logRadius endpoint 1| ≤ B
  length_bound : word.length ≤ returnLengthBound n
  value_oscillation :
    |f (endpoint.toU4 (lift.terminal_generic admissible)) -
        f (((sourceU^[n]) z).toU4 (lift.initial_generic admissible))| ≤
      2 * M * (returnLengthBound n : ℝ)

/-- Return data after the optional fixed correction. -/
structure FinalReturnDatum (z : TorusPoint) (f : U4 → ℝ)
    (M : ℝ) (n : ℕ) where
  word : List CorrLetter
  endpoint : TorusPoint
  lift : WordLift word ((sourceU^[n]) z) endpoint
  admissible : lift.Admissible
  length_bound : word.length ≤ returnLengthBound n + 4
  value_oscillation :
    |f (endpoint.toU4 (lift.terminal_generic admissible)) -
        f (((sourceU^[n]) z).toU4 (lift.initial_generic admissible))| ≤
      2 * M * (returnLengthBound n : ℝ) + 4 * M

/-- Use no correction when the subsequential limit is already generic. -/
def BoundedReturnDatum.toFinal
    {z : TorusPoint} {f : U4 → ℝ} {M B : ℝ} {n : ℕ}
    (d : BoundedReturnDatum z f M B n) (hM : 0 ≤ M) :
    FinalReturnDatum z f M n := {
  word := d.word
  endpoint := d.endpoint
  lift := d.lift
  admissible := d.admissible
  length_bound := d.length_bound.trans (Nat.le_add_right _ _)
  value_oscillation := d.value_oscillation.trans (by nlinarith)
}

/-- Append a fixed correction containing two `U`-moves and at most four
letters.  Crucially, admissibility is obtained by applying full genericity to
the concatenated lift, not to the intermediate endpoint. -/
def BoundedReturnDatum.appendCorrection
    {z : TorusPoint} (hz : FullyGeneric z)
    {f : U4 → ℝ} (hf : PointAlt f) {M B : ℝ} (hM : 0 ≤ M)
    (hD : ∀ q : U5, |D f q| ≤ M) {n : ℕ}
    (d : BoundedReturnDatum z f M B n)
    {correctionWord : List CorrLetter} {w : TorusPoint}
    (c : WordLift correctionWord d.endpoint w)
    (hcLength : correctionWord.length ≤ 4)
    (hcSign : wordSign correctionWord = 1)
    (hcUCount : wordUCount correctionWord = 2) :
    FinalReturnDatum z f M n := by
  let e : WordLift (d.word ++ correctionWord) ((sourceU^[n]) z) w :=
    d.lift.append c
  have he : e.Admissible := hz.everyLift n (d.word ++ correctionWord) e
  have hcAdm : c.Admissible := d.lift.append_right_admissible c he
  have hcOsc := c.value_oscillation hcAdm f hf M hD
  rw [hcSign, one_mul, hcUCount] at hcOsc
  have hcOsc' :
      |f (w.toU4 (c.terminal_generic hcAdm)) -
          f (d.endpoint.toU4 (c.initial_generic hcAdm))| ≤ 4 * M := by
    convert hcOsc using 1 <;> ring
  refine {
    word := d.word ++ correctionWord
    endpoint := w
    lift := e
    admissible := he
    length_bound := ?_
    value_oscillation := ?_
  }
  · simp only [List.length_append]
    exact Nat.add_le_add d.length_bound hcLength
  · let A := f (w.toU4 (e.terminal_generic he))
    let C := f (((sourceU^[n]) z).toU4 (e.initial_generic he))
    let P := f (d.endpoint.toU4 (d.lift.terminal_generic d.admissible))
    change |A - C| ≤ 2 * M * (returnLengthBound n : ℝ) + 4 * M
    calc
      |A - C| = |(A - P) + (P - C)| := by
        congr 1
        ring
      _ ≤ |A - P| + |P - C| := by
        simpa [Real.norm_eq_abs] using norm_add_le (A - P) (P - C)
      _ ≤ 4 * M + 2 * M * (returnLengthBound n : ℝ) := by
        apply add_le_add
        · simpa [A, P] using hcOsc'
        · simpa [P, C] using d.value_oscillation
      _ = 2 * M * (returnLengthBound n : ℝ) + 4 * M := by ring

/-- Both radial cases give uniformly bounded endpoints at every sufficiently
large level. -/
theorem fullyGeneric_bounded_returns
    (z : TorusPoint) (hz : FullyGeneric z)
    (f : U4 → ℝ) (hf : PointAlt f) (M : ℝ) (hM : 0 ≤ M)
    (hD : ∀ q : U5, |D f q| ≤ M) :
    ∃ (B : ℝ) (N : ℕ), ∀ n : ℕ, N ≤ n →
      Nonempty (BoundedReturnDatum z f M B n) := by
  by_cases hb : logRadius z 1 = 0
  · refine ⟨|logRadius z 0| + 1, 0, fun n _ => ?_⟩
    obtain ⟨e, he, hlog, _⟩ :=
      fullyGeneric_zero_second_radius_return z hz hb n
    let datum : BoundedReturnDatum z f M (|logRadius z 0| + 1) n := {
      word := []
      endpoint := (sourceU^[n]) z
      lift := e
      admissible := he
      radius_bound := by
        rw [hlog]
        constructor
        · linarith
        · rw [hb, abs_zero]
          positivity
      length_bound := by simp
      value_oscillation := by
        have hnonneg : 0 ≤ 2 * M * (returnLengthBound n : ℝ) := by
          positivity
        simpa using hnonneg
    }
    exact ⟨datum⟩
  · obtain ⟨N, hreturn⟩ :=
      fullyGeneric_compact_return z hz hb f hf M hM hD
    refine ⟨|logRadius z 1| + 1, N, fun n hn => ?_⟩
    obtain ⟨k, y, e, he, hkRange, happrox, hkBound, hyOne,
      hyZero, hlength, hosc⟩ := hreturn n hn
    let datum : BoundedReturnDatum z f M (|logRadius z 1| + 1) n := {
      word := returnWord n k
      endpoint := y
      lift := e
      admissible := he
      radius_bound := by
        constructor
        · exact hyZero.trans (by nlinarith [abs_nonneg (logRadius z 1)])
        · rw [hyOne]
          linarith
      length_bound := hlength
      value_oscillation := hosc
    }
    exact ⟨datum⟩

/-- Selecting the return data and applying compactness produces increasing
dilation levels and a convergent endpoint subsequence in the ambient torus. -/
theorem fullyGeneric_precompact_return_subsequence
    (z : TorusPoint) (hz : FullyGeneric z)
    (f : U4 → ℝ) (hf : PointAlt f) (M : ℝ) (hM : 0 ≤ M)
    (hD : ∀ q : U5, |D f q| ≤ M) :
    ∃ (B : ℝ) (q : TorusPoint) (ns : ℕ → ℕ),
      StrictMono ns ∧ Tendsto ns atTop atTop ∧
      ∃ data : ∀ k : ℕ, BoundedReturnDatum z f M B (ns k),
        Tendsto (fun k => (data k).endpoint) atTop (𝓝 q) := by
  obtain ⟨B, N, hreturn⟩ :=
    fullyGeneric_bounded_returns z hz f hf M hM hD
  let data₀ : ∀ j : ℕ, BoundedReturnDatum z f M B (N + j) :=
    fun j => Classical.choice (hreturn (N + j) (Nat.le_add_right N j))
  obtain ⟨q, _, φ, hφ, hlim⟩ :=
    exists_tendsto_subsequence_of_logRadius_bounded
      (fun j => (data₀ j).endpoint) B (fun j => (data₀ j).radius_bound)
  let ns : ℕ → ℕ := fun k => N + φ k
  have hns : StrictMono ns := fun _ _ hij => Nat.add_lt_add_left (hφ hij) N
  let data : ∀ k : ℕ, BoundedReturnDatum z f M B (ns k) :=
    fun k => data₀ (φ k)
  refine ⟨B, q, ns, hns, hns.tendsto_atTop, data, ?_⟩
  simpa [data, Function.comp_def] using hlim

/-- The quantified polynomial-length compact return proposition.  The final
endpoints, viewed in `U4`, form a convergent sequence and hence lie in one
compact subset.  If the ambient torus limit lies on the deleted divisor, one
fixed two-edge correction is appended to every selected return path. -/
theorem polynomial_length_compact_return
    (z : TorusPoint) (hz : FullyGeneric z)
    (f : U4 → ℝ) (hf : PointAlt f) (M : ℝ) (hM : 0 ≤ M)
    (hD : ∀ q : U5, |D f q| ≤ M) :
    ∃ (ns : ℕ → ℕ),
      StrictMono ns ∧ Tendsto ns atTop atTop ∧
      ∃ (data : ∀ k : ℕ, FinalReturnDatum z f M (ns k)) (limit : U4),
        Tendsto
            (fun k => (data k).endpoint.toU4
              ((data k).lift.terminal_generic (data k).admissible))
            atTop (𝓝 limit) ∧
          ∃ K : Set U4, IsCompact K ∧
            ∀ k : ℕ,
              (data k).endpoint.toU4
                ((data k).lift.terminal_generic (data k).admissible) ∈ K := by
  obtain ⟨B, q, ns, hns, hnsTop, data, hlim⟩ :=
    fullyGeneric_precompact_return_subsequence z hz f hf M hM hD
  have hlimVal : Tendsto (fun k => ((data k).endpoint : TorusPoint).1)
      atTop (𝓝 q.1) := tendsto_subtype_rng.mp hlim
  by_cases hq : q.IsGeneric
  · let finalData : ∀ k : ℕ, FinalReturnDatum z f M (ns k) :=
      fun k => (data k).toFinal hM
    let u : ℕ → U4 := fun k =>
      (finalData k).endpoint.toU4
        ((finalData k).lift.terminal_generic (finalData k).admissible)
    let qU : U4 := q.toU4 hq
    have hu : Tendsto u atTop (𝓝 qU) := by
      rw [tendsto_subtype_rng]
      change Tendsto (fun k => ((data k).endpoint : TorusPoint).1)
        atTop (𝓝 q.1)
      exact hlimVal
    let K : Set U4 := insert qU (Set.range u)
    have hK : IsCompact K := hu.isCompact_insert_range
    refine ⟨ns, hns, hnsTop, finalData, qU, ?_, K, hK, ?_⟩
    · exact hu
    · intro k
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_range_self k))
  · have hdelta : delta4 q.1 = 0 := not_ne_iff.mp hq
    rcases correction_leaves_divisor q hdelta with hcorr | hcorr
    · let correctionLift : ∀ k : ℕ,
          WordLift correction1Word (data k).endpoint
            (correction1 (data k).endpoint) :=
        fun k => Classical.choice (exists_correction1Lift (data k).endpoint)
      let finalData : ∀ k : ℕ, FinalReturnDatum z f M (ns k) :=
        fun k => (data k).appendCorrection hz hf hM hD
          (correctionLift k) (by simp) (by simp) (by simp)
      let u : ℕ → U4 := fun k =>
        (finalData k).endpoint.toU4
          ((finalData k).lift.terminal_generic (finalData k).admissible)
      let qU : U4 := (correction1 q).toU4 hcorr
      have hcorrLim : Tendsto
          (fun k => correction1 (data k).endpoint) atTop
          (𝓝 (correction1 q)) := by
        exact Tendsto.comp continuous_correction1.continuousAt hlim
      have hcorrLimVal : Tendsto
          (fun k => (correction1 (data k).endpoint : TorusPoint).1) atTop
          (𝓝 (correction1 q).1) := tendsto_subtype_rng.mp hcorrLim
      have hu : Tendsto u atTop (𝓝 qU) := by
        rw [tendsto_subtype_rng]
        change Tendsto
          (fun k => (correction1 (data k).endpoint : TorusPoint).1)
          atTop (𝓝 (correction1 q).1)
        exact hcorrLimVal
      let K : Set U4 := insert qU (Set.range u)
      have hK : IsCompact K := hu.isCompact_insert_range
      refine ⟨ns, hns, hnsTop, finalData, qU, hu, K, hK, ?_⟩
      intro k
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_range_self k))
    · let correctionLift : ∀ k : ℕ,
          WordLift correction2Word (data k).endpoint
            (correction2 (data k).endpoint) :=
        fun k => Classical.choice (exists_correction2Lift (data k).endpoint)
      let finalData : ∀ k : ℕ, FinalReturnDatum z f M (ns k) :=
        fun k => (data k).appendCorrection hz hf hM hD
          (correctionLift k) (by simp) (by simp) (by simp)
      let u : ℕ → U4 := fun k =>
        (finalData k).endpoint.toU4
          ((finalData k).lift.terminal_generic (finalData k).admissible)
      let qU : U4 := (correction2 q).toU4 hcorr
      have hcorrLim : Tendsto
          (fun k => correction2 (data k).endpoint) atTop
          (𝓝 (correction2 q)) := by
        exact Tendsto.comp continuous_correction2.continuousAt hlim
      have hcorrLimVal : Tendsto
          (fun k => (correction2 (data k).endpoint : TorusPoint).1) atTop
          (𝓝 (correction2 q).1) := tendsto_subtype_rng.mp hcorrLim
      have hu : Tendsto u atTop (𝓝 qU) := by
        rw [tendsto_subtype_rng]
        change Tendsto
          (fun k => (correction2 (data k).endpoint : TorusPoint).1)
          atTop (𝓝 (correction2 q).1)
        exact hcorrLimVal
      let K : Set U4 := insert qU (Set.range u)
      have hK : IsCompact K := hu.isCompact_insert_range
      refine ⟨ns, hns, hnsTop, finalData, qU, hu, K, hK, ?_⟩
      intro k
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_range_self k))

/-! ## Iterated defect and continuous local-to-global bound -/

/-- The admissible `T₁` parameter at the `n`-th dilation level. -/
def fullyGenericEdge (z : TorusPoint) (hz : FullyGeneric z) (n : ℕ) : UEdge :=
  ⟨(sourceU^[n]) z, hz.edgeAdmissible_iterate n⟩

/-- The corresponding point of the generic four-point locus. -/
def fullyGenericIterateU4 (z : TorusPoint) (hz : FullyGeneric z)
    (n : ℕ) : U4 :=
  edgeBase (fullyGenericEdge z hz n)

theorem fullyGenericIterateU4_succ (z : TorusPoint) (hz : FullyGeneric z)
    (n : ℕ) :
    fullyGenericIterateU4 z hz (n + 1) =
      edgeSource (fullyGenericEdge z hz n) := by
  apply Subtype.ext
  change ((sourceU^[n + 1]) z).1 = (sourceU ((sourceU^[n]) z)).1
  rw [Function.iterate_succ_apply']

/-- The pointwise first-defect identity along a fully generic dilation orbit. -/
theorem fullyGeneric_one_step_defect
    (z : TorusPoint) (hz : FullyGeneric z)
    (f : U4 → ℝ) (hf : PointAlt f) (n : ℕ) :
    2 * f (fullyGenericIterateU4 z hz n) -
        f (fullyGenericIterateU4 z hz (n + 1)) =
      D f (phi1 (edgeAdm1 (fullyGenericEdge z hz n))) := by
  rw [fullyGenericIterateU4_succ]
  change 2 * f (edgeBase (fullyGenericEdge z hz n)) -
      f (edgeSource (fullyGenericEdge z hz n)) = _
  rw [show edgeBase (fullyGenericEdge z hz n) =
    base1 (edgeAdm1 (fullyGenericEdge z hz n)) by rfl]
  simpa only [T1_edgeAdm1] using
    defect_dilation_one f hf (edgeAdm1 (fullyGenericEdge z hz n))

theorem fullyGeneric_one_step_defect_bound
    (z : TorusPoint) (hz : FullyGeneric z)
    (f : U4 → ℝ) (hf : PointAlt f) (M : ℝ)
    (hD : ∀ q : U5, |D f q| ≤ M) (n : ℕ) :
    |2 * f (fullyGenericIterateU4 z hz n) -
        f (fullyGenericIterateU4 z hz (n + 1))| ≤ M := by
  rw [fullyGeneric_one_step_defect z hz f hf n]
  exact hD _

/-- Exact iteration of the first defect inequality. -/
theorem fullyGeneric_iterated_defect_bound
    (z : TorusPoint) (hz : FullyGeneric z)
    (f : U4 → ℝ) (hf : PointAlt f) (M : ℝ)
    (hD : ∀ q : U5, |D f q| ≤ M) (n : ℕ) :
    |(2 : ℝ) ^ n * f (fullyGenericIterateU4 z hz 0) -
        f (fullyGenericIterateU4 z hz n)| ≤
      ((2 : ℝ) ^ n - 1) * M := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := fullyGeneric_one_step_defect_bound z hz f hf M hD n
      calc
        |(2 : ℝ) ^ (n + 1) * f (fullyGenericIterateU4 z hz 0) -
            f (fullyGenericIterateU4 z hz (n + 1))| =
            |2 * ((2 : ℝ) ^ n * f (fullyGenericIterateU4 z hz 0) -
                f (fullyGenericIterateU4 z hz n)) +
              (2 * f (fullyGenericIterateU4 z hz n) -
                f (fullyGenericIterateU4 z hz (n + 1)))| := by
              congr 1
              rw [pow_succ]
              ring
        _ ≤ |2 * ((2 : ℝ) ^ n * f (fullyGenericIterateU4 z hz 0) -
              f (fullyGenericIterateU4 z hz n))| +
            |2 * f (fullyGenericIterateU4 z hz n) -
              f (fullyGenericIterateU4 z hz (n + 1))| := by
              simpa [Real.norm_eq_abs] using
                norm_add_le
                  (2 * ((2 : ℝ) ^ n * f (fullyGenericIterateU4 z hz 0) -
                    f (fullyGenericIterateU4 z hz n)))
                  (2 * f (fullyGenericIterateU4 z hz n) -
                    f (fullyGenericIterateU4 z hz (n + 1)))
        _ = 2 * |(2 : ℝ) ^ n * f (fullyGenericIterateU4 z hz 0) -
              f (fullyGenericIterateU4 z hz n)| +
            |2 * f (fullyGenericIterateU4 z hz n) -
              f (fullyGenericIterateU4 z hz (n + 1))| := by
              rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        _ ≤ 2 * (((2 : ℝ) ^ n - 1) * M) + M :=
          add_le_add (mul_le_mul_of_nonneg_left ih (by norm_num)) hstep
        _ = ((2 : ℝ) ^ (n + 1) - 1) * M := by
          rw [pow_succ]
          ring

/-- The explicit return-length polynomial is negligible compared with `2ⁿ`. -/
theorem returnLengthBound_div_pow_tendsto_zero :
    Tendsto (fun n : ℕ =>
      (returnLengthBound n : ℝ) / (2 : ℝ) ^ n) atTop (𝓝 0) := by
  have h2 := tendsto_pow_const_mul_const_pow_of_lt_one 2
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have h0 := tendsto_pow_const_mul_const_pow_of_lt_one 0
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hsum := ((h2.const_mul 136).add (h1.const_mul 89)).add
    (h0.const_mul 2)
  convert hsum using 1
  · funext n
    rw [div_eq_mul_inv]
    simp only [one_div, inv_pow, returnLengthBound]
    push_cast
    ring
  · norm_num

def compactReturnUpper (M B : ℝ) (n : ℕ) : ℝ :=
  (((2 : ℝ) ^ n - 1) * M +
      (2 * M * (returnLengthBound n : ℝ) + 4 * M) + B) /
    (2 : ℝ) ^ n

theorem compactReturnUpper_tendsto (M B : ℝ) :
    Tendsto (compactReturnUpper M B) atTop (𝓝 M) := by
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hmain :=
    ((((hone.sub hpow).mul_const M).add
      (returnLengthBound_div_pow_tendsto_zero.const_mul (2 * M))).add
      (hpow.const_mul (4 * M))).add (hpow.const_mul B)
  convert hmain using 1
  · funext n
    change compactReturnUpper M B n =
      (1 - (1 / 2 : ℝ) ^ n) * M +
        (2 * M) * ((returnLengthBound n : ℝ) / (2 : ℝ) ^ n) +
        (4 * M) * (1 / 2 : ℝ) ^ n + B * (1 / 2 : ℝ) ^ n
    rw [show (1 / 2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n by
      rw [one_div_pow]]
    simp only [compactReturnUpper]
    field_simp [pow_ne_zero]
    ring
  · ring

theorem continuous_abs_bounded_on_compact
    (f : U4 → ℝ) (hf : Continuous f) {K : Set U4} (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, |f x| ≤ B := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.norm.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have hxC : |f x| ≤ C := by
    simpa [Real.norm_eq_abs] using hC x hx
  exact hxC.trans (le_max_left _ _)

/-- Continuous local-to-global bound at a fully generic point. -/
theorem continuous_bound_at_fullyGeneric
    (f : U4 → ℝ) (hcont : Continuous f) (hf : PointAlt f)
    (M : ℝ) (hM : 0 ≤ M) (hD : ∀ q : U5, |D f q| ≤ M)
    (z : TorusPoint) (hz : FullyGeneric z) :
    |f (fullyGenericIterateU4 z hz 0)| ≤ M := by
  obtain ⟨ns, hns, hnsTop, data, limit, hlimit, K, hK, hmem⟩ :=
    polynomial_length_compact_return z hz f hf M hM hD
  obtain ⟨B, hBnonneg, hB⟩ := continuous_abs_bounded_on_compact f hcont hK
  have hupper : Tendsto (fun k => compactReturnUpper M B (ns k))
      atTop (𝓝 M) := Tendsto.comp (compactReturnUpper_tendsto M B) hnsTop
  apply ge_of_tendsto' hupper
  intro k
  let d := data k
  let n := ns k
  let x0 := f (fullyGenericIterateU4 z hz 0)
  let xn := f (fullyGenericIterateU4 z hz n)
  let w := f (d.endpoint.toU4 (d.lift.terminal_generic d.admissible))
  have hsource :
      ((sourceU^[n]) z).toU4 (d.lift.initial_generic d.admissible) =
        fullyGenericIterateU4 z hz n := by
    apply Subtype.ext
    rfl
  have hiter : |(2 : ℝ) ^ n * x0 - xn| ≤ ((2 : ℝ) ^ n - 1) * M := by
    exact fullyGeneric_iterated_defect_bound z hz f hf M hD n
  have hreturn : |w - xn| ≤
      2 * M * (returnLengthBound n : ℝ) + 4 * M := by
    simpa [d, n, w, xn, hsource] using d.value_oscillation
  have hw : |w| ≤ B := by
    exact hB _ (hmem k)
  have htotal : |(2 : ℝ) ^ n * x0| ≤
      ((2 : ℝ) ^ n - 1) * M +
        (2 * M * (returnLengthBound n : ℝ) + 4 * M) + B := by
    calc
      |(2 : ℝ) ^ n * x0| =
          |((2 : ℝ) ^ n * x0 - xn) + (xn - w) + w| := by
            congr 1
            ring
      _ ≤ |((2 : ℝ) ^ n * x0 - xn) + (xn - w)| + |w| := by
        simpa [Real.norm_eq_abs] using norm_add_le
          (((2 : ℝ) ^ n * x0 - xn) + (xn - w)) w
      _ ≤ (|(2 : ℝ) ^ n * x0 - xn| + |xn - w|) + |w| := by
        apply add_le_add
        · simpa [Real.norm_eq_abs] using norm_add_le
            ((2 : ℝ) ^ n * x0 - xn) (xn - w)
        · exact le_rfl
      _ ≤ ((2 : ℝ) ^ n - 1) * M +
          (2 * M * (returnLengthBound n : ℝ) + 4 * M) + B := by
        exact add_le_add (add_le_add hiter (by simpa [abs_sub_comm] using hreturn)) hw
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  change |x0| ≤ compactReturnUpper M B n
  rw [compactReturnUpper]
  apply (le_div_iff₀ hpow).2
  simpa [abs_mul, abs_of_pos hpow, mul_comm] using htotal

@[simp]
theorem fullyGenericIterateU4_zero_of_U4 (q : U4)
    (hq : FullyGeneric q.toTorusPoint) :
    fullyGenericIterateU4 q.toTorusPoint hq 0 = q := by
  apply Subtype.ext
  rfl

/-- Once density of the explicitly defined fully generic set is available,
continuity extends the pointwise estimate to all of `U4`. -/
theorem continuous_local_to_global_of_dense_fullyGeneric
    (f : U4 → ℝ) (hcont : Continuous f) (hf : PointAlt f)
    (M : ℝ) (hM : 0 ≤ M) (hD : ∀ q : U5, |D f q| ≤ M)
    (hdense : Dense {q : U4 | FullyGeneric q.toTorusPoint}) :
    ∀ q : U4, |f q| ≤ M := by
  let good : Set U4 := {q | |f q| ≤ M}
  have hgoodClosed : IsClosed good :=
    isClosed_le (hcont.abs) continuous_const
  have hsubset : {q : U4 | FullyGeneric q.toTorusPoint} ⊆ good := by
    intro q hq
    change |f q| ≤ M
    simpa using continuous_bound_at_fullyGeneric f hcont hf M hM hD
      q.toTorusPoint hq
  have hgoodDense : Dense good := hdense.mono hsubset
  have hgood : good = Set.univ := by
    rw [← hgoodClosed.closure_eq, hgoodDense.closure_eq]
  intro q
  change q ∈ good
  rw [hgood]
  exact Set.mem_univ q

/-- Unconditional continuous local-to-global estimate: density is supplied by
the explicit residual-locus construction in `Genericity.lean`. -/
theorem continuous_local_to_global
    (f : U4 → ℝ) (hcont : Continuous f) (hf : PointAlt f)
    (M : ℝ) (hM : 0 ≤ M) (hD : ∀ q : U5, |D f q| ≤ M) :
    ∀ q : U4, |f q| ≤ M :=
  continuous_local_to_global_of_dense_fullyGeneric
    f hcont hf M hM hD fullyGeneric_dense

end
end Pfaffian
end Sp4
