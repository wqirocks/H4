import Sp4.Cohomology.AffineCocycleCombinatorics

/-!
# The six-point affine cocycle identity

This module proves that the thirty-term rational formula has zero six-point
coboundary.  The proof passes through the Pfaffian Plücker identity and checks
normalization invariance of every face.
-/

namespace Sp4.AffineCocycle

open Pfaffian

noncomputable section

theorem matrix6_isSkew (q : Coord6) : IsSkew (matrix6 q) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [matrix6]

def reindexMatrix4 (A : Matrix (Fin 4) (Fin 4) ℂ)
    (σ : Equiv.Perm (Fin 4)) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => A (σ i) (σ j)

theorem isSkew_reindexMatrix4 {A : Matrix (Fin 4) (Fin 4) ℂ}
    (hA : IsSkew A) (σ : Equiv.Perm (Fin 4)) :
    IsSkew (reindexMatrix4 A σ) := by
  intro i j
  exact hA (σ i) (σ j)

theorem pfaffian4_reindex_swap (A : Matrix (Fin 4) (Fin 4) ℂ)
    (hA : IsSkew A) (i j : Fin 4) (hij : i ≠ j) :
    pfaffian4 (reindexMatrix4 A (Equiv.swap i j)) = -pfaffian4 A := by
  have h10 := hA 0 1
  have h20 := hA 0 2
  have h30 := hA 0 3
  have h21 := hA 1 2
  have h31 := hA 1 3
  have h32 := hA 2 3
  clear hA
  fin_cases i <;> fin_cases j <;>
    simp_all [pfaffian4, reindexMatrix4, Equiv.swap_apply_def] <;>
    ring

theorem reindexMatrix4_mul (A : Matrix (Fin 4) (Fin 4) ℂ)
    (σ τ : Equiv.Perm (Fin 4)) :
    reindexMatrix4 A (σ * τ) = reindexMatrix4 (reindexMatrix4 A σ) τ := by
  ext i j
  rfl

theorem pfaffian4_reindex (A : Matrix (Fin 4) (Fin 4) ℂ)
    (hA : IsSkew A) (σ : Equiv.Perm (Fin 4)) :
    pfaffian4 (reindexMatrix4 A σ) =
      (Equiv.Perm.sign σ : ℂ) * pfaffian4 A := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one =>
      have hreindex : reindexMatrix4 A 1 = A := by
        ext i j
        simp [reindexMatrix4]
      rw [hreindex]
      simp
  | mul_swap σ i j hij ih =>
      rw [reindexMatrix4_mul,
        pfaffian4_reindex_swap (reindexMatrix4 A σ)
          (isSkew_reindexMatrix4 hA σ) i j hij,
        ih]
      simp [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]

def bracketTuple6 (A : Matrix (Fin 6) (Fin 6) ℂ) (v : Fin 4 → Fin 6) : ℂ :=
  orderedBracket A (v 0) (v 1) (v 2) (v 3)

def matrix4OfTuple6 (A : Matrix (Fin 6) (Fin 6) ℂ) (v : Fin 4 → Fin 6) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => A (v i) (v j)

theorem isSkew_matrix4OfTuple6 {A : Matrix (Fin 6) (Fin 6) ℂ}
    (hA : IsSkew A) (v : Fin 4 → Fin 6) : IsSkew (matrix4OfTuple6 A v) := by
  intro i j
  exact hA (v i) (v j)

theorem bracketTuple6_reindex (A : Matrix (Fin 6) (Fin 6) ℂ)
    (hA : IsSkew A) (v : Fin 4 → Fin 6) (σ : Equiv.Perm (Fin 4)) :
    bracketTuple6 A (fun i => v (σ i)) =
      (Equiv.Perm.sign σ : ℂ) * bracketTuple6 A v := by
  exact pfaffian4_reindex (matrix4OfTuple6 A v)
    (isSkew_matrix4OfTuple6 hA v) σ

theorem orderedBracket_matrix6_ne_zero_of_lt (q : U6) (a b c d : Fin 6)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    orderedBracket (matrix6 q.1) a b c d ≠ 0 := by
  fin_cases a <;> fin_cases b <;> simp_all
  all_goals fin_cases c <;> simp_all
  all_goals fin_cases d <;> simp_all
  all_goals simp [orderedBracket, matrix6]
  all_goals first
    | simpa [pf0123] using q.2.pf0123_ne
    | simpa [pf0124] using q.2.pf0124_ne
    | simpa [pf0125] using q.2.pf0125_ne
    | simpa [pf0134] using q.2.pf0134_ne
    | simpa [pf0135] using q.2.pf0135_ne
    | simpa [pf0145] using q.2.pf0145_ne
    | simpa [pf0234] using q.2.pf0234_ne
    | simpa [pf0235] using q.2.pf0235_ne
    | simpa [pf0245] using q.2.pf0245_ne
    | simpa [pf0345] using q.2.pf0345_ne
    | simpa [pf1234] using q.2.pf1234_ne
    | simpa [pf1235] using q.2.pf1235_ne
    | simpa [pf1245] using q.2.pf1245_ne
    | simpa [pf1345] using q.2.pf1345_ne
    | simpa [pf2345] using q.2.pf2345_ne

theorem orderedBracket_matrix6_ne_zero (q : U6) (i j k l : Fin 6)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    orderedBracket (matrix6 q.1) i j k l ≠ 0 := by
  let v : Fin 4 → Fin 6 := ![i, j, k, l]
  have hv : Function.Injective v := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [v]
  let s : Finset (Fin 6) := Finset.univ.image v
  have hs : s.card = 4 := by
    rw [Finset.card_image_of_injective _ hv]
    simp
  let evFun : Fin 4 → s := fun a => ⟨v a, by simp [s]⟩
  have hevFun : Function.Injective evFun := by
    intro a b hab
    exact hv (congrArg Subtype.val hab)
  have hevFunBij : Function.Bijective evFun :=
    (Fintype.bijective_iff_injective_and_card evFun).2 ⟨hevFun, by simp [hs]⟩
  let ev : Fin 4 ≃ s := Equiv.ofBijective evFun hevFunBij
  let w : Fin 4 → Fin 6 := s.orderEmbOfFin hs
  let τ : Equiv.Perm (Fin 4) := ev.trans (s.orderIsoOfFin hs).symm
  have hwτ : ∀ a, w (τ a) = v a := by
    intro a
    change ↑(s.orderIsoOfFin hs ((s.orderIsoOfFin hs).symm (ev a))) = v a
    rw [OrderIso.apply_symm_apply]
    rfl
  have hw : bracketTuple6 (matrix6 q.1) w ≠ 0 := by
    exact orderedBracket_matrix6_ne_zero_of_lt q (w 0) (w 1) (w 2) (w 3)
      ((s.orderEmbOfFin hs).strictMono (by decide))
      ((s.orderEmbOfFin hs).strictMono (by decide))
      ((s.orderEmbOfFin hs).strictMono (by decide))
  have hperm := bracketTuple6_reindex (matrix6 q.1) (matrix6_isSkew q.1) w τ
  have hsign : (Equiv.Perm.sign τ : ℂ) ≠ 0 := by
    exact_mod_cast (Equiv.Perm.sign τ).ne_zero
  change bracketTuple6 (matrix6 q.1) v ≠ 0
  rw [show bracketTuple6 (matrix6 q.1) v =
      bracketTuple6 (matrix6 q.1) (fun a => w (τ a)) by
        congr 1
        funext a
        exact (hwτ a).symm,
    hperm]
  exact mul_ne_zero hsign hw

theorem affineDifference_triangle_of_pfaffian6_zero
    (A : Matrix (Fin 6) (Fin 6) ℂ) (hA : IsSkew A)
    (hpf : pfaffian6 A = 0) (σ : Equiv.Perm (Fin 6))
    (h₃ : orderedBracket A (σ 0) (σ 1) (σ 2) (σ 3) ≠ 0)
    (h₄ : orderedBracket A (σ 0) (σ 1) (σ 2) (σ 4) ≠ 0)
    (h₅ : orderedBracket A (σ 0) (σ 1) (σ 2) (σ 5) ≠ 0) :
    affineDifference A (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) -
        affineDifference A (σ 0) (σ 1) (σ 2) (σ 3) (σ 5) +
        affineDifference A (σ 0) (σ 1) (σ 2) (σ 4) (σ 5) = 0 := by
  have hplucker :
      orderedBracket A (σ 0) (σ 1) (σ 3) (σ 4) *
          orderedBracket A (σ 0) (σ 1) (σ 2) (σ 5) -
        orderedBracket A (σ 0) (σ 1) (σ 3) (σ 5) *
          orderedBracket A (σ 0) (σ 1) (σ 2) (σ 4) +
        orderedBracket A (σ 0) (σ 1) (σ 4) (σ 5) *
          orderedBracket A (σ 0) (σ 1) (σ 2) (σ 3) = 0 := by
    have h := bracket_plucker_standard (reindexMatrix6 A σ)
    rw [pfaffian6_reindex A hA σ, hpf] at h
    simpa [reindexMatrix6, orderedBracket] using h
  simp only [affineDifference]
  field_simp [h₃, h₄, h₅]
  linear_combination
    -(A (σ 0) (σ 2) * A (σ 1) (σ 2)) * hplucker

theorem affineDifference_matrix6_triangle (q : U6) (σ : Equiv.Perm (Fin 6)) :
    affineDifference (matrix6 q.1) (σ 0) (σ 1) (σ 2) (σ 3) (σ 4) -
        affineDifference (matrix6 q.1) (σ 0) (σ 1) (σ 2) (σ 3) (σ 5) +
        affineDifference (matrix6 q.1) (σ 0) (σ 1) (σ 2) (σ 4) (σ 5) = 0 := by
  apply affineDifference_triangle_of_pfaffian6_zero
    (matrix6 q.1) (matrix6_isSkew q.1) (by simpa using q.2.pi_zero)
  · apply orderedBracket_matrix6_ne_zero q <;>
      exact σ.injective.ne (by decide)
  · apply orderedBracket_matrix6_ne_zero q <;>
      exact σ.injective.ne (by decide)
  · apply orderedBracket_matrix6_ne_zero q <;>
      exact σ.injective.ne (by decide)

theorem rawBoundarySum6_affineDifference_matrix6_eq_zero (q : U6) :
    rawBoundarySum6 (affineDifference (matrix6 q.1)) = 0 := by
  rw [rawBoundarySum6_eq_fullAlternatingTailSum6]
  apply fullAlternatingTailSum6_eq_zero
  apply fullAlternatingSum6_eq_zero
  · exact affineDifference_swap (matrix6_isSkew q.1)
  · exact affineDifference_matrix6_triangle q

def diagonalScale {n : Type*} (A : Matrix n n ℂ) (d : n → ℂ) : Matrix n n ℂ :=
  fun i j => d i * A i j * d j

theorem orderedBracket_diagonalScale {n : Type*} (A : Matrix n n ℂ)
    (d : n → ℂ) (i j k l : n) :
    orderedBracket (diagonalScale A d) i j k l =
      (d i * d j * d k * d l) * orderedBracket A i j k l := by
  simp only [orderedBracket, diagonalScale]
  ring

theorem affineDifference_diagonalScale {n : Type*} (A : Matrix n n ℂ)
    (d : n → ℂ) (hd : ∀ i, d i ≠ 0) (i j k l m : n) :
    affineDifference (diagonalScale A d) i j k l m =
      affineDifference A i j k l m := by
  simp only [affineDifference, diagonalScale, orderedBracket_diagonalScale]
  let S := d i ^ 2 * d j ^ 2 * d k ^ 2 * d l * d m
  have hS : S ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (pow_ne_zero 2 (hd i)) (pow_ne_zero 2 (hd j)))
          (pow_ne_zero 2 (hd k)))
        (hd l))
      (hd m)
  calc
    _ = S * (-(A i k * A j k * orderedBracket A i j l m)) /
        (S * (orderedBracket A i j k l * orderedBracket A i j k m)) := by
      congr 1 <;> simp only [S] <;> ring
    _ = _ := mul_div_mul_left _ _ hS

def deleteMatrix6 (A : Matrix (Fin 6) (Fin 6) ℂ) (skip : Fin 6) :
    Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => A (skip.succAbove i) (skip.succAbove j)

theorem exists_nonzero_sq_eq {z : ℂ} (hz : z ≠ 0) :
    ∃ a : ℂ, a ≠ 0 ∧ a ^ 2 = z := by
  rcases IsAlgClosed.exists_pow_nat_eq z (n := 2) (by decide) with ⟨a, ha⟩
  refine ⟨a, ?_, ha⟩
  intro haz
  apply hz
  rw [← ha, haz]
  simp

def face5MatrixAt (q : U6) (skip : Fin 6) : Matrix (Fin 5) (Fin 5) ℂ :=
  matrix5 (Pfaffian.face5At skip q).1

def faceScale0 (q : Coord6) (a : ℂ) : Fin 5 → ℂ :=
  ![a, 1 / a, 1 / (a * q.u), 1 / (a * q.v), 1 / (a * q.s)]

theorem face5MatrixAt_zero_scale (q : U6) {a : ℂ}
    (ha : a ≠ 0) (ha2 : a ^ 2 = q.1.w / q.1.u) :
    face5MatrixAt q 0 =
      diagonalScale (deleteMatrix6 (matrix6 q.1) 0) (faceScale0 q.1 a) := by
  have ha2' : a ^ 2 * q.1.u = q.1.w := (eq_div_iff q.2.u_ne).mp ha2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [face5MatrixAt, Pfaffian.face5At, face5_0, face5Coord0,
      faceScale0, diagonalScale, deleteMatrix6, matrix5, matrix6,
      Fin.succAbove] <;>
    field_simp [ha, q.2.u_ne, q.2.v_ne, q.2.s_ne, q.2.w_ne] <;>
    rw [← ha2'] <;> ring

def faceScale12 (a : ℂ) : Fin 5 → ℂ :=
  ![a, 1 / a, 1 / a, 1 / a, 1 / a]

theorem face5MatrixAt_one_scale (q : U6) {a : ℂ}
    (ha : a ≠ 0) (ha2 : a ^ 2 = q.1.w) :
    face5MatrixAt q 1 =
      diagonalScale (deleteMatrix6 (matrix6 q.1) 1) (faceScale12 a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [face5MatrixAt, Pfaffian.face5At, face5_1, face5Coord1,
      faceScale12, diagonalScale, deleteMatrix6, matrix5, matrix6,
      Fin.succAbove] <;>
    field_simp [ha, q.2.w_ne] <;>
    rw [← ha2]

theorem face5MatrixAt_two_scale (q : U6) {a : ℂ}
    (ha : a ≠ 0) (ha2 : a ^ 2 = q.1.u) :
    face5MatrixAt q 2 =
      diagonalScale (deleteMatrix6 (matrix6 q.1) 2) (faceScale12 a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [face5MatrixAt, Pfaffian.face5At, face5_2, face5Coord2,
      faceScale12, diagonalScale, deleteMatrix6, matrix5, matrix6,
      Fin.succAbove] <;>
    field_simp [ha, q.2.u_ne] <;>
    rw [← ha2]

theorem face5MatrixAt_three_scale (q : U6) :
    face5MatrixAt q 3 =
      diagonalScale (deleteMatrix6 (matrix6 q.1) 3) (fun _ => 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [face5MatrixAt, Pfaffian.face5At, face5_3, face5Coord3,
      diagonalScale, deleteMatrix6, matrix5, matrix6, Fin.succAbove]

theorem face5MatrixAt_four_scale (q : U6) :
    face5MatrixAt q 4 =
      diagonalScale (deleteMatrix6 (matrix6 q.1) 4) (fun _ => 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [face5MatrixAt, Pfaffian.face5At, face5_4, face5Coord4,
      diagonalScale, deleteMatrix6, matrix5, matrix6, Fin.succAbove]

theorem face5MatrixAt_five_scale (q : U6) :
    face5MatrixAt q 5 =
      diagonalScale (deleteMatrix6 (matrix6 q.1) 5) (fun _ => 1) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [face5MatrixAt, Pfaffian.face5At, face5_5, face5Coord5,
      diagonalScale, deleteMatrix6, matrix5, matrix6, Fin.succAbove]

theorem exists_face5MatrixAt_scale (q : U6) (skip : Fin 6) :
    ∃ d : Fin 5 → ℂ, (∀ i, d i ≠ 0) ∧
      face5MatrixAt q skip = diagonalScale (deleteMatrix6 (matrix6 q.1) skip) d := by
  fin_cases skip
  · rcases exists_nonzero_sq_eq (div_ne_zero q.2.w_ne q.2.u_ne) with ⟨a, ha, ha2⟩
    refine ⟨faceScale0 q.1 a, ?_, face5MatrixAt_zero_scale q ha ha2⟩
    intro i
    fin_cases i <;> simp [faceScale0, ha, q.2.u_ne, q.2.v_ne, q.2.s_ne]
  · rcases exists_nonzero_sq_eq q.2.w_ne with ⟨a, ha, ha2⟩
    refine ⟨faceScale12 a, ?_, face5MatrixAt_one_scale q ha ha2⟩
    intro i
    fin_cases i <;> simp [faceScale12, ha]
  · rcases exists_nonzero_sq_eq q.2.u_ne with ⟨a, ha, ha2⟩
    refine ⟨faceScale12 a, ?_, face5MatrixAt_two_scale q ha ha2⟩
    intro i
    fin_cases i <;> simp [faceScale12, ha]
  · exact ⟨fun _ => 1, by simp, face5MatrixAt_three_scale q⟩
  · exact ⟨fun _ => 1, by simp, face5MatrixAt_four_scale q⟩
  · exact ⟨fun _ => 1, by simp, face5MatrixAt_five_scale q⟩

theorem affineDifference_face5MatrixAt (q : U6) (skip : Fin 6)
    (i j k l m : Fin 5) :
    affineDifference (face5MatrixAt q skip) i j k l m =
      affineDifference (matrix6 q.1)
        (deletedIndex6 skip i) (deletedIndex6 skip j) (deletedIndex6 skip k)
        (deletedIndex6 skip l) (deletedIndex6 skip m) := by
  rcases exists_face5MatrixAt_scale q skip with ⟨d, hd, hmatrix⟩
  rw [hmatrix, affineDifference_diagonalScale _ d hd]
  rfl

theorem rawAlternationR_face5At (q : U6) (skip : Fin 6) :
    rawAlternationR (matrix5 (Pfaffian.face5At skip q).1) =
      (1 / 120 : ℂ) * rawFaceSum6 (affineDifference (matrix6 q.1)) skip := by
  change (1 / 120 : ℂ) *
      (∑ σ : Equiv.Perm (Fin 5), (Equiv.Perm.sign σ : ℂ) *
        affineDifference (face5MatrixAt q skip)
          (σ 0) (σ 1) (σ 2) (σ 3) (σ 4)) = _
  simp_rw [affineDifference_face5MatrixAt q skip]
  rfl

theorem reducedR_face5At (q : U6) (skip : Fin 6) :
    reducedR (matrix5 (Pfaffian.face5At skip q).1) =
      (1 / 120 : ℂ) * rawFaceSum6 (affineDifference (matrix6 q.1)) skip := by
  rw [← rawAlternationR_eq_reducedR (Pfaffian.face5At skip q)]
  exact rawAlternationR_face5At q skip

/-- The paper's thirty-term affine formula is a genuine five-cocycle on the
generic six-point Pfaffian locus. -/
theorem E_reducedR_apply (q : U6) :
    Pfaffian.E (fun p : U5 => reducedR (matrix5 p.1)) q = 0 := by
  change reducedR (matrix5 (Pfaffian.face5At 0 q).1) -
      reducedR (matrix5 (Pfaffian.face5At 1 q).1) +
      reducedR (matrix5 (Pfaffian.face5At 2 q).1) -
      reducedR (matrix5 (Pfaffian.face5At 3 q).1) +
      reducedR (matrix5 (Pfaffian.face5At 4 q).1) -
      reducedR (matrix5 (Pfaffian.face5At 5 q).1) = 0
  rw [reducedR_face5At q 0, reducedR_face5At q 1,
    reducedR_face5At q 2, reducedR_face5At q 3,
    reducedR_face5At q 4, reducedR_face5At q 5]
  have hraw := rawBoundarySum6_affineDifference_matrix6_eq_zero q
  simp only [rawBoundarySum6, Fin.sum_univ_succ] at hraw
  norm_num at hraw ⊢
  have h3 : (Fin.succ 2 : Fin 6) = 3 := rfl
  have h4 : ((Fin.succ 2).succ : Fin 6) = 4 := rfl
  have h5 : ((Fin.succ 2).succ.succ : Fin 6) = 5 := rfl
  rw [h3, h4, h5] at hraw
  linear_combination (1 / 120 : ℂ) * hraw

theorem E_reducedR :
    Pfaffian.E (fun p : U5 => reducedR (matrix5 p.1)) = 0 := by
  funext q
  exact E_reducedR_apply q

end

end Sp4.AffineCocycle
