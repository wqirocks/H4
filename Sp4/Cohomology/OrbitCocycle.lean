import Sp4.Chains.ParametricTwoCone

/-!
# The affine formula as a cocycle on projective orbit chains

The rational six-point identity is stated in normalized Pfaffian coordinates.
This file transports it back to arbitrary generic projective configurations,
which is the form required by the finite two-cone homotopy.
-/

namespace Sp4

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace AffineCocycle

/-- Six vectors in the four-dimensional symplectic space have vanishing
six-by-six Pfaffian Gram determinant. -/
theorem pfaffian6_gram_eq_zero (v : Fin 6 → SymplecticVector) :
    Pfaffian.pfaffian6 (gram v) = 0 :=
  OrbitChain.pfaffian6_gram_eq_zero v

/-- Every four-bracket of distinct entries of a generic six-configuration is
nonzero. -/
theorem orderedBracket_projectiveGram_ne_zero
    (x : OrbitChain.GenericConfig 6) (i j k l : Fin 6)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    orderedBracket (projectiveGram x.1) i j k l ≠ 0 := by
  let e : Fin 4 → Fin 6 := ![i, j, k, l]
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [e]
  have hdet := generic_principal_gram_det_ne_zero x.2 e he
  have hskew : IsSkew ((projectiveGram x.1).submatrix e e) := by
    intro a b
    exact projectiveGram_isSkew x.1 (e a) (e b)
  rw [OrbitChain.det_skew_four_eq_pfaffian_sq _ hskew] at hdet
  have hpf : Pfaffian.pfaffian4
      ((projectiveGram x.1).submatrix e e) ≠ 0 := by
    intro hzero
    exact hdet (by simp [hzero])
  simpa [Pfaffian.pfaffian4, orderedBracket, e] using hpf

/-- The unnormalized affine alternation has zero simplicial boundary on the
Gram matrix of every generic six-configuration. -/
theorem rawBoundarySum6_projectiveGram_eq_zero
    (x : OrbitChain.GenericConfig 6) :
    rawBoundarySum6 (affineDifference (projectiveGram x.1)) = 0 := by
  rw [rawBoundarySum6_eq_fullAlternatingTailSum6]
  apply fullAlternatingTailSum6_eq_zero
  apply fullAlternatingSum6_eq_zero
  · exact affineDifference_swap
      (show IsSkew (projectiveGram x.1) from projectiveGram_isSkew x.1)
  · intro σ
    apply affineDifference_triangle_of_pfaffian6_zero
      (projectiveGram x.1)
      (show IsSkew (projectiveGram x.1) from projectiveGram_isSkew x.1)
    · exact pfaffian6_gram_eq_zero (projectiveRepresentatives x.1)
    · apply orderedBracket_projectiveGram_ne_zero x <;>
        exact σ.injective.ne (by decide)
    · apply orderedBracket_projectiveGram_ne_zero x <;>
        exact σ.injective.ne (by decide)
    · apply orderedBracket_projectiveGram_ne_zero x <;>
        exact σ.injective.ne (by decide)

end AffineCocycle

namespace Pfaffian

/-- Evaluating the normalized formula on the orbit coordinate of an arbitrary
generic five-configuration recovers the lift-independent 120-term
alternation of its canonical projective Gram matrix. -/
theorem reducedR_orbitCoord5_eq_rawAlternationR
    (x : OrbitChain.GenericConfig 5) :
    AffineCocycle.reducedR (matrix5 (orbitCoord5 x).1) =
      AffineCocycle.rawAlternationR (projectiveGram x.1) := by
  rw [← AffineCocycle.rawAlternationR_eq_reducedR (orbitCoord5 x)]
  let A := projectiveGram x.1
  have hA : IsAdmissibleGram A :=
    generic_projectiveGram_isAdmissible x.2 Fin.castSucc
      (Fin.castSucc_injective 4)
  obtain ⟨d, hd⟩ := exists_matrix5_chi5_diagonalCongruence
    A hA.skew hA.offDiagonal_ne
  change AffineCocycle.rawAlternationR (matrix5 (chi5 A)) =
    AffineCocycle.rawAlternationR A
  rw [hd, rawAlternationR_diagonalCongruence]

/-- Each face value of an arbitrary generic projective six-configuration is
the corresponding unnormalized five-label alternation. -/
theorem reducedR_orbitCoord5_face_eq_rawFaceSum6
    (x : OrbitChain.GenericConfig 6) (skip : Fin 6) :
    AffineCocycle.reducedR
        (matrix5 (orbitCoord5 (OrbitChain.face skip x)).1) =
      (1 / 120 : ℂ) * AffineCocycle.rawFaceSum6
        (AffineCocycle.affineDifference (projectiveGram x.1)) skip := by
  rw [reducedR_orbitCoord5_eq_rawAlternationR]
  obtain ⟨d, hd⟩ := projectiveGram_face_diagonalCongruent skip x
  rw [hd, rawAlternationR_diagonalCongruence]
  rfl

end Pfaffian

namespace MeasureChain

/-- A real-linear scalar component of the complex affine cocycle. -/
def realComponentCocycle (ell : ℂ →ₗ[ℝ] ℝ) (q : Pfaffian.U5) : ℝ :=
  ell (AffineCocycle.reducedR (Pfaffian.matrix5 q.1))

theorem realComponentCocycle_continuous (ell : ℂ →ₗ[ℝ] ℝ) :
    Continuous (realComponentCocycle ell) := by
  exact (LinearMap.toContinuousLinearMap ell).continuous.comp
    Pfaffian.continuous_reducedR_matrix5

theorem realComponentCocycle_stronglyMeasurable (ell : ℂ →ₗ[ℝ] ℝ) :
    StronglyMeasurable (realComponentCocycle ell) :=
  (realComponentCocycle_continuous ell).stronglyMeasurable

theorem realComponentCocycle_isAlternatingFunction5 (ell : ℂ →ₗ[ℝ] ℝ) :
    IsAlternatingFunction5 (realComponentCocycle ell) := by
  intro σ q
  change ell (AffineCocycle.reducedR
      (Pfaffian.matrix5 (Pfaffian.permute5 σ q).1)) =
    OrbitChain.permSign ℝ σ •
      ell (AffineCocycle.reducedR (Pfaffian.matrix5 q.1))
  rw [Pfaffian.reducedR_permute5]
  change ell (OrbitChain.permSign ℝ σ •
      AffineCocycle.reducedR (Pfaffian.matrix5 q.1)) = _
  exact map_smul ell _ _

/-- The normalized affine formula is a pointwise cocycle on arbitrary generic
projective configurations, not only on the chosen `U6` coordinate slice. -/
theorem reducedR_isPointwiseCocycle5 :
    IsPointwiseCocycle5
      (fun q : Pfaffian.U5 ↦
        AffineCocycle.reducedR (Pfaffian.matrix5 q.1)) := by
  intro x
  simp_rw [Pfaffian.reducedR_orbitCoord5_face_eq_rawFaceSum6 x]
  have hraw := AffineCocycle.rawBoundarySum6_projectiveGram_eq_zero x
  calc
    (∑ i : Fin 6, (-1 : ℝ) ^ i.val •
        ((1 / 120 : ℂ) * AffineCocycle.rawFaceSum6
          (AffineCocycle.affineDifference (projectiveGram x.1)) i)) =
        (1 / 120 : ℂ) * AffineCocycle.rawBoundarySum6
          (AffineCocycle.affineDifference (projectiveGram x.1)) := by
      rw [AffineCocycle.rawBoundarySum6, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      simp [Complex.real_smul]
      ring
    _ = 0 := by rw [hraw]; ring

theorem realComponentCocycle_isPointwiseCocycle5 (ell : ℂ →ₗ[ℝ] ℝ) :
    IsPointwiseCocycle5 (realComponentCocycle ell) := by
  intro x
  have hcomplex := reducedR_isPointwiseCocycle5 x
  calc
    (∑ i : Fin 6, (-1 : ℝ) ^ i.val •
        realComponentCocycle ell (Pfaffian.orbitCoord5
          (OrbitChain.face i x))) =
        ∑ i : Fin 6, ell ((-1 : ℝ) ^ i.val •
          AffineCocycle.reducedR (Pfaffian.matrix5
            (Pfaffian.orbitCoord5 (OrbitChain.face i x)).1)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [map_smul]
      rfl
    _ = ell (∑ i : Fin 6, (-1 : ℝ) ^ i.val •
          AffineCocycle.reducedR (Pfaffian.matrix5
            (Pfaffian.orbitCoord5 (OrbitChain.face i x)).1)) := by
      rw [map_sum]
    _ = ell 0 := congrArg ell hcomplex
    _ = 0 := map_zero ell

/-- Evaluation of a scalar component commutes with the finite orbit-chain
pairing. -/
theorem evaluation5_realComponentCocycle
    (ell : ℂ →ₗ[ℝ] ℝ) (z : OrbitChain.Module ℝ 5) :
    evaluation5 (realComponentCocycle ell)
        (realComponentCocycle_isAlternatingFunction5 ell) z =
      ell (evaluation5
        (fun q : Pfaffian.U5 ↦
          AffineCocycle.reducedR (Pfaffian.matrix5 q.1))
        reducedR_isAlternatingFunction5 z) := by
  obtain ⟨c, rfl⟩ := (OrbitChain.relations ℝ 5).mkQ_surjective z
  change rawEvaluation5 (realComponentCocycle ell) c =
    ell (rawEvaluation5
      (fun q : Pfaffian.U5 ↦
        AffineCocycle.reducedR (Pfaffian.matrix5 q.1)) c)
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add x a c hx ha ih =>
      have hs : Finsupp.single x a =
          a • OrbitChain.generator x := by
        ext y
        simp [OrbitChain.generator]
      rw [map_add, map_add, hs, map_smul, map_smul,
        rawEvaluation5_generator, rawEvaluation5_generator,
        map_add, map_smul, ih]
      rfl

/-- On the article's explicit period cycle, a real scalar component evaluates
to that same scalar component of the complex period. -/
theorem evaluation5_realComponentCocycle_periodCycle
    (ell : ℂ →ₗ[ℝ] ℝ) (A B : ℂ)
    (h : OrbitChain.PeriodCycleAdmissible A B) :
    evaluation5 (realComponentCocycle ell)
        (realComponentCocycle_isAlternatingFunction5 ell)
        (OrbitChain.periodCycle A B h) =
      ell (OrbitChain.periodCycleValue A B h) := by
  rw [evaluation5_realComponentCocycle,
    evaluation5_periodCycle_reducedR]

end MeasureChain

end
end Sp4
