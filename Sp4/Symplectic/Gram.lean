import Sp4.Symplectic.Model
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.Bilinear

/-! Generic configurations, Gram matrices, normalization, and orbit classification. -/

namespace Sp4

noncomputable section

open scoped BigOperators Matrix

def IsSkewMatrix {n : Type*} [Neg ℂ] (A : Matrix n n ℂ) : Prop :=
  ∀ i j, A j i = -A i j

def gram {n : Type*} (v : n → SymplecticVector) : Matrix n n ℂ :=
  fun i j => omega (v i) (v j)

theorem gram_isSkew {n : Type*} (v : n → SymplecticVector) : IsSkewMatrix (gram v) := by
  intro i j
  exact omega_skew _ _

def diagonalCongruence {n : Type*} (d : n → ℂ) (A : Matrix n n ℂ) :
    Matrix n n ℂ := fun i j => d i * A i j * d j

theorem gram_smul {n : Type*} (d : n → ℂ) (v : n → SymplecticVector) :
    gram (fun i => d i • v i) = diagonalCongruence d (gram v) := by
  ext i j
  simp [gram, diagonalCongruence]
  ring

theorem gram_symplectic (g : SymplecticGroup) {n : Type*}
    (v : n → SymplecticVector) : gram (fun i => g.1 (v i)) = gram v := by
  ext i j
  exact g.2 _ _

def deleteMatrix {n : ℕ} (i : Fin (n + 1)) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := A.submatrix i.succAbove i.succAbove

theorem gram_delete {n : ℕ} (i : Fin (n + 1))
    (v : Fin (n + 1) → SymplecticVector) :
    gram (FinTuple.delete i v) = deleteMatrix i (gram v) := rfl

def vectorColumns {n : Type*} (v : n → SymplecticVector) :
    Matrix (Fin 4) n ℂ := fun a i => v i a

theorem gram_eq_columns {n : Type*} [Fintype n]
    (v : n → SymplecticVector) :
    gram v = (vectorColumns v)ᵀ * symplecticJ * vectorColumns v := by
  ext i j
  simp [gram, vectorColumns, symplecticJ, omega_apply, Matrix.mul_apply,
    Fin.sum_univ_succ]
  ring

theorem gram_rank_le_four {n : Type*} [Fintype n] (v : n → SymplecticVector) :
    (gram v).rank ≤ 4 := by
  rw [gram_eq_columns]
  calc
    ((vectorColumns v)ᵀ * symplecticJ * vectorColumns v).rank ≤
        ((vectorColumns v)ᵀ * symplecticJ).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin 4) := Matrix.rank_le_card_width _
    _ = 4 := by simp

def projectiveRepresentatives {n : Type*} (l : n → ProjectivePoint) :
    n → SymplecticVector := fun i => (l i).rep

theorem projectiveRepresentatives_ne_zero {n : Type*} (l : n → ProjectivePoint) (i : n) :
    projectiveRepresentatives l i ≠ 0 := (l i).rep_nonzero

def projectiveGram {n : Type*} (l : n → ProjectivePoint) : Matrix n n ℂ :=
  gram (projectiveRepresentatives l)

theorem projectiveGram_isSkew {n : Type*} (l : n → ProjectivePoint) :
    IsSkewMatrix (projectiveGram l) := gram_isSkew _

theorem generic_selected_span {n : ℕ} {l : ProjectiveConfig n} (hl : IsGeneric l)
    (e : Fin 4 → Fin n) (he : Function.Injective e) :
    Submodule.span ℂ (Set.range fun k => projectiveRepresentatives l (e k)) = ⊤ := by
  rw [Submodule.span_range_eq_iSup]
  simpa [projectiveRepresentatives, Projectivization.submodule_eq] using hl.four_spans e he

noncomputable def genericSelectedBasis {n : ℕ} {l : ProjectiveConfig n}
    (hl : IsGeneric l) (e : Fin 4 → Fin n) (he : Function.Injective e) :
    Module.Basis (Fin 4) ℂ SymplecticVector :=
  basisOfTopLeSpanOfCardEqFinrank
    (fun k => projectiveRepresentatives l (e k))
    (le_of_eq (generic_selected_span hl e he).symm)
    (by simp)

@[simp] theorem genericSelectedBasis_apply {n : ℕ} {l : ProjectiveConfig n}
    (hl : IsGeneric l) (e : Fin 4 → Fin n) (he : Function.Injective e) (k : Fin 4) :
    genericSelectedBasis hl e he k = projectiveRepresentatives l (e k) := by
  simp [genericSelectedBasis]

theorem generic_principal_gram_det_ne_zero {n : ℕ} {l : ProjectiveConfig n}
    (hl : IsGeneric l) (e : Fin 4 → Fin n) (he : Function.Injective e) :
    ((projectiveGram l).submatrix e e).det ≠ 0 := by
  let b := genericSelectedBasis hl e he
  have hdet := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp omega_nondegenerate
  have hmatrix : (projectiveGram l).submatrix e e =
      LinearMap.BilinForm.toMatrix b omega := by
    ext i j
    simp [projectiveGram, gram, b]
  rw [hmatrix]
  exact hdet

theorem generic_projectiveGram_rank_eq_four {n : ℕ} {l : ProjectiveConfig n}
    (hl : IsGeneric l) (e : Fin 4 → Fin n) (he : Function.Injective e) :
    (projectiveGram l).rank = 4 := by
  apply le_antisymm (gram_rank_le_four _)
  have hsub := Matrix.rank_submatrix_le (projectiveGram l) e e
  have hdet := generic_principal_gram_det_ne_zero hl e he
  rw [Matrix.rank_of_det_ne_zero hdet] at hsub
  simpa [projectiveGram] using hsub

/-- The matrix locus appearing in Gram classification. -/
structure IsAdmissibleGram {n : Type*} [Fintype n] (A : Matrix n n ℂ) : Prop where
  skew : IsSkewMatrix A
  rank_four : A.rank = 4
  offDiagonal_ne : ∀ i j, i ≠ j → A i j ≠ 0
  principal_four_ne : ∀ (e : Fin 4 → n), Function.Injective e →
    (A.submatrix e e).det ≠ 0

theorem generic_projectiveGram_isAdmissible {n : ℕ} {l : ProjectiveConfig n}
    (hl : IsGeneric l) (e₀ : Fin 4 → Fin n) (he₀ : Function.Injective e₀) :
    IsAdmissibleGram (projectiveGram l) where
  skew := projectiveGram_isSkew l
  rank_four := generic_projectiveGram_rank_eq_four hl e₀ he₀
  offDiagonal_ne i j hij := hl.pairwise_transverse i j hij
  principal_four_ne e he := generic_principal_gram_det_ne_zero hl e he

theorem gram_linearIndependent_of_det_ne_zero
    (v : Fin 4 → SymplecticVector) (hdet : (gram v).det ≠ 0) :
    LinearIndependent ℂ v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hmul : gram v *ᵥ c = 0 := by
    funext j
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    calc
      ∑ x, gram v j x * c x = omega (v j) (∑ x, c x • v x) := by
        simp [gram, map_sum, mul_comm]
      _ = 0 := by rw [hc]; simp
  have hc0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  exact congr_fun hc0 i

/-- A simultaneous choice of nonzero vector representatives of a projective
configuration. -/
structure ProjectiveLift {n : Type*} (l : n → ProjectivePoint) where
  vec : n → SymplecticVector
  ne_zero : ∀ i, vec i ≠ 0
  projectivizes : ∀ i, Projectivization.mk ℂ (vec i) (ne_zero i) = l i

noncomputable def canonicalProjectiveLift {n : Type*} (l : n → ProjectivePoint) :
    ProjectiveLift l where
  vec := projectiveRepresentatives l
  ne_zero := projectiveRepresentatives_ne_zero l
  projectivizes i := Projectivization.mk_rep (l i)

/-- Two systems of projective representatives differ coordinatewise by units. -/
theorem ProjectiveLift.exists_scalars {n : Type*} {l : n → ProjectivePoint}
    (u v : ProjectiveLift l) :
    ∃ d : n → ℂˣ, ∀ i, u.vec i = d i • v.vec i := by
  classical
  have hex : ∀ i, ∃ a : ℂˣ, a • v.vec i = u.vec i := by
    intro i
    apply (Projectivization.mk_eq_mk_iff ℂ _ _ (u.ne_zero i) (v.ne_zero i)).mp
    exact (u.projectivizes i).trans (v.projectivizes i).symm
  choose d hd using hex
  exact ⟨d, fun i => (hd i).symm⟩

/-- Changing projective lifts changes the Gram matrix by diagonal congruence. -/
theorem ProjectiveLift.gram_diagonalCongruent {n : Type*} {l : n → ProjectivePoint}
    (u v : ProjectiveLift l) :
    ∃ d : n → ℂˣ,
      gram u.vec = diagonalCongruence (fun i => (d i : ℂ)) (gram v.vec) := by
  obtain ⟨d, hd⟩ := u.exists_scalars v
  refine ⟨d, ?_⟩
  ext i j
  simp only [gram, diagonalCongruence]
  rw [hd i, hd j]
  simp [Units.smul_def]
  ring

/-- Equal Gram matrices, together with chosen four-element bases, determine a
unique symplectic change of coordinates carrying every vector to its mate. -/
theorem exists_symplectic_of_gram_eq {n : Type*}
    (v w : n → SymplecticVector) (e : Fin 4 → n)
    (bv bw : Module.Basis (Fin 4) ℂ SymplecticVector)
    (hbv : ∀ i, bv i = v (e i)) (hbw : ∀ i, bw i = w (e i))
    (hgram : gram v = gram w) :
    ∃ g : SymplecticGroup, ∀ i, g.1 (v i) = w i := by
  let gLin : SymplecticVector ≃ₗ[ℂ] SymplecticVector :=
    bv.equiv bw (Equiv.refl (Fin 4))
  have g_basis (i : Fin 4) : gLin (v (e i)) = w (e i) := by
    rw [← hbv i, ← hbw i]
    simp [gLin]
  have hpres : ∀ x y, omega (gLin x) (gLin y) = omega x y := by
    have hforms : omega.comp gLin.toLinearMap gLin.toLinearMap = omega := by
      apply LinearMap.ext_basis bv bv
      intro i j
      change omega (gLin (bv i)) (gLin (bv j)) = omega (bv i) (bv j)
      rw [Module.Basis.equiv_apply, Module.Basis.equiv_apply]
      simp only [Equiv.refl_apply]
      have hij := congr_fun (congr_fun hgram (e i)) (e j)
      rw [hbv i, hbv j, hbw i, hbw j]
      exact hij.symm
    intro x y
    have hxy := LinearMap.congr_fun (LinearMap.congr_fun hforms x) y
    exact hxy
  let g : SymplecticGroup := ⟨gLin, hpres⟩
  refine ⟨g, fun k => ?_⟩
  apply eq_of_omega_eq_on_basis bw
  intro i
  calc
    omega (g.1 (v k)) (bw i) = omega (g.1 (v k)) (g.1 (v (e i))) := by
      rw [g_basis, ← hbw]
    _ = omega (v k) (v (e i)) := g.2 _ _
    _ = omega (w k) (w (e i)) := congr_fun (congr_fun hgram k) (e i)
    _ = omega (w k) (bw i) := by rw [hbw]

/-- Two generic projective configurations with the same normalized Gram matrix
lie in the same symplectic orbit. -/
theorem exists_symplectic_smul_of_projectiveGram_eq {n : ℕ}
    (l m : ProjectiveConfig n) (hl : IsGeneric l) (hm : IsGeneric m)
    (e : Fin 4 → Fin n) (he : Function.Injective e)
    (hgram : projectiveGram l = projectiveGram m) :
    ∃ g : SymplecticGroup, g • l = m := by
  let bl := genericSelectedBasis hl e he
  let bm := genericSelectedBasis hm e he
  obtain ⟨g, hg⟩ := exists_symplectic_of_gram_eq
    (projectiveRepresentatives l) (projectiveRepresentatives m) e bl bm
    (by intro i; simp [bl]) (by intro i; simp [bm]) hgram
  refine ⟨g, funext fun i => ?_⟩
  change g.1 • l i = m i
  rw [← Projectivization.mk_rep (l i), ← Projectivization.mk_rep (m i)]
  rw [Projectivization.smul_mk]
  rw [Projectivization.mk_eq_mk_iff']
  exact ⟨1, by simpa [projectiveRepresentatives] using (hg i).symm⟩

/-! ## Realization and the full Gram classification -/

/-- An explicit family of four vectors whose pairings are the six upper-triangular
entries of a four-by-four matrix. -/
def realizeSkewFour (A : Matrix (Fin 4) (Fin 4) ℂ) : Fin 4 → SymplecticVector
  | 0 => ![1, 0, 0, 0]
  | 1 => ![0, A 0 1, 0, 0]
  | 2 => ![-A 1 2 / A 0 1, A 0 2, 1, 0]
  | 3 => ![-A 1 3 / A 0 1, A 0 3, 0,
      (A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2) / A 0 1]

theorem gram_realizeSkewFour (A : Matrix (Fin 4) (Fin 4) ℂ)
    (hA : IsSkewMatrix A) (h01 : A 0 1 ≠ 0) :
    gram (realizeSkewFour A) = A := by
  have hdiag (i : Fin 4) : A i i = 0 := by
    have h := hA i i
    have hadd : A i i + A i i = 0 := by
      calc
        A i i + A i i = -A i i + A i i := congrArg (fun z => z + A i i) h
        _ = 0 := neg_add_cancel _
    have htwo : (2 : ℂ) * A i i = 0 := by
      calc
        (2 : ℂ) * A i i = A i i + A i i := by ring
        _ = 0 := hadd
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [gram, realizeSkewFour, omega_apply, hdiag,
    hA 0 1, hA 0 2, hA 0 3, hA 1 2, hA 1 3, hA 2 3]
  all_goals field_simp [h01]
  all_goals ring

theorem selectedColumns_linearIndependent {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (e : Fin 4 → n)
    (hdet : (A.submatrix e e).det ≠ 0) :
    LinearIndependent ℂ (fun k => A.col (e k)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hmul : A.submatrix e e *ᵥ c = 0 := by
    funext j
    have hj := congr_fun hc (e j)
    simpa [Matrix.mulVec, dotProduct, Matrix.col_apply, mul_comm] using hj
  have hc0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  exact congr_fun hc0 i

theorem span_selectedColumns_eq {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (e : Fin 4 → n)
    (hrank : A.rank = 4) (hdet : (A.submatrix e e).det ≠ 0) :
    Submodule.span ℂ (Set.range fun k => A.col (e k)) =
      Submodule.span ℂ (Set.range A.col) := by
  classical
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_mono
    rintro _ ⟨k, rfl⟩
    exact ⟨e k, rfl⟩
  · rw [finrank_span_eq_card (selectedColumns_linearIndependent A e hdet)]
    simpa [← Matrix.rank_eq_finrank_span_cols] using hrank.symm

/-- Coefficients expressing every column through a fixed nonsingular principal
four-column family. -/
noncomputable def columnCoefficients {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (e : Fin 4 → n)
    (hrank : A.rank = 4) (hdet : (A.submatrix e e).det ≠ 0) : n → Fin 4 → ℂ :=
  fun j => Classical.choose ((Submodule.mem_span_range_iff_exists_fun ℂ).mp <| by
    rw [span_selectedColumns_eq A e hrank hdet]
    exact Submodule.subset_span ⟨j, rfl⟩)

theorem columnCoefficients_spec {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (e : Fin 4 → n)
    (hrank : A.rank = 4) (hdet : (A.submatrix e e).det ≠ 0) (j : n) :
    ∑ k, columnCoefficients A e hrank hdet j k • A.col (e k) = A.col j :=
  Classical.choose_spec ((Submodule.mem_span_range_iff_exists_fun ℂ).mp <| by
    rw [span_selectedColumns_eq A e hrank hdet]
    exact Submodule.subset_span ⟨j, rfl⟩)

def realizedVectors {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (e : Fin 4 → n)
    (hrank : A.rank = 4) (hdet : (A.submatrix e e).det ≠ 0) :
    n → SymplecticVector := fun j =>
  ∑ k, columnCoefficients A e hrank hdet j k •
    realizeSkewFour (A.submatrix e e) k

theorem gram_realizedVectors {n : Type*} [Fintype n]
    (A : Matrix n n ℂ) (e : Fin 4 → n)
    (hskew : IsSkewMatrix A) (hrank : A.rank = 4)
    (hdet : (A.submatrix e e).det ≠ 0)
    (he : Function.Injective e)
    (hoff : ∀ i j, i ≠ j → A i j ≠ 0) :
    gram (realizedVectors A e hrank hdet) = A := by
  classical
  let c := columnCoefficients A e hrank hdet
  let u := realizeSkewFour (A.submatrix e e)
  have hsubskew : IsSkewMatrix (A.submatrix e e) := by
    intro i j
    exact hskew (e i) (e j)
  have he01 : e 0 ≠ e 1 := fun h => (by norm_num : (0 : Fin 4) ≠ 1) (he h)
  have h01 : (A.submatrix e e) 0 1 ≠ 0 := hoff _ _ he01
  have hu : gram u = A.submatrix e e := gram_realizeSkewFour _ hsubskew h01
  have hcol (j : n) : ∑ k, c j k • A.col (e k) = A.col j :=
    columnCoefficients_spec A e hrank hdet j
  have hu_pair (a b : Fin 4) : omega (u a) (u b) = A (e a) (e b) := by
    have hab := congr_fun (congr_fun hu a) b
    exact hab
  have hrealized (j : n) :
      realizedVectors A e hrank hdet j = ∑ k, c j k • u k := rfl
  have hpair_selected (a : Fin 4) (j : n) :
      omega (u a) (realizedVectors A e hrank hdet j) = A (e a) j := by
    rw [hrealized, map_sum]
    simp only [map_smul, smul_eq_mul]
    calc
      ∑ k, c j k * omega (u a) (u k) =
          ∑ k, c j k * A (e a) (e k) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [hu_pair]
      _ = A (e a) j := by
        have hj := congr_fun (hcol j) (e a)
        simpa [Matrix.col_apply, mul_comm] using hj
  ext i j
  simp only [gram]
  rw [hrealized, map_sum]
  simp only [map_smul]
  calc
    ∑ k, c i k * omega (u k) (realizedVectors A e hrank hdet j) =
        ∑ k, c i k * A (e k) j := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hpair_selected]
    _ = -∑ k, c i k * A j (e k) := by
      simp_rw [hskew j]
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = -A j i := by
      have hi := congr_fun (hcol i) j
      simpa [Matrix.col_apply, mul_comm] using congrArg Neg.neg hi
    _ = A i j := (hskew j i).symm

/-- Every admissible matrix is the Gram matrix of a lift of a generic
projective configuration.  The chosen injection identifies the four columns
used as a basis of the matrix column space. -/
theorem IsAdmissibleGram.exists_generic_realization {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsAdmissibleGram A)
    (e : Fin 4 → Fin n) (he : Function.Injective e) :
    ∃ (l : ProjectiveConfig n) (u : ProjectiveLift l),
      IsGeneric l ∧ gram u.vec = A := by
  classical
  let hdet := hA.principal_four_ne e he
  let v : Fin n → SymplecticVector :=
    realizedVectors A e hA.rank_four hdet
  have hvgram : gram v = A :=
    gram_realizedVectors A e hA.skew hA.rank_four hdet he hA.offDiagonal_ne
  have hv_ne (i : Fin n) : v i ≠ 0 := by
    let j : Fin n := if hi : i = e 0 then e 1 else e 0
    have hij : i ≠ j := by
      dsimp [j]
      split_ifs with hi
      · rw [hi]
        exact fun h => (by norm_num : (0 : Fin 4) ≠ 1) (he h)
      · exact hi
    intro hvi
    have hentry := congr_fun (congr_fun hvgram i) j
    apply hA.offDiagonal_ne i j hij
    rw [← hentry]
    simp [gram, hvi]
  let l : ProjectiveConfig n := fun i => Projectivization.mk ℂ (v i) (hv_ne i)
  let u : ProjectiveLift l :=
    { vec := v
      ne_zero := hv_ne
      projectivizes := fun i => rfl }
  refine ⟨l, u, ?_, ?_⟩
  · constructor
    · intro i j hij
      rw [show l i = Projectivization.mk ℂ (v i) (hv_ne i) by rfl,
        show l j = Projectivization.mk ℂ (v j) (hv_ne j) by rfl,
        transverse_mk_iff]
      change gram v i j ≠ 0
      rw [hvgram]
      exact hA.offDiagonal_ne i j hij
    · intro f hf
      have hsubgram : gram (fun k => v (f k)) = A.submatrix f f := by
        ext i j
        exact congr_fun (congr_fun hvgram (f i)) (f j)
      have hli : LinearIndependent ℂ (fun k => v (f k)) := by
        apply gram_linearIndependent_of_det_ne_zero
        rw [hsubgram]
        exact hA.principal_four_ne f hf
      simp only [l, Projectivization.submodule_mk]
      rw [← Submodule.span_range_eq_iSup]
      exact hli.span_eq_top_of_card_eq_finrank (by simp)
  · exact hvgram

/-- An arbitrary projective lift whose Gram matrix is admissible already
represents a generic configuration.  This converse is useful for explicit
coordinate families: admissibility can be checked by polynomial identities,
without repeating the projective spanning argument. -/
theorem ProjectiveLift.isGeneric_of_gram_isAdmissible {n : ℕ}
    {l : ProjectiveConfig n} (u : ProjectiveLift l)
    (hu : IsAdmissibleGram (gram u.vec)) : IsGeneric l := by
  constructor
  · intro i j hij
    rw [← u.projectivizes i, ← u.projectivizes j, transverse_mk_iff]
    exact hu.offDiagonal_ne i j hij
  · intro e he
    simp only [← u.projectivizes, Projectivization.submodule_mk]
    rw [← Submodule.span_range_eq_iSup]
    have hli : LinearIndependent ℂ (fun k ↦ u.vec (e k)) := by
      apply gram_linearIndependent_of_det_ne_zero
      exact hu.principal_four_ne e he
    exact hli.span_eq_top_of_card_eq_finrank (by
      rw [finrank_symplecticVector]
      simp)

theorem ProjectiveLift.selected_span {n : ℕ} {l : ProjectiveConfig n}
    (u : ProjectiveLift l) (hl : IsGeneric l)
    (e : Fin 4 → Fin n) (he : Function.Injective e) :
    Submodule.span ℂ (Set.range fun k => u.vec (e k)) = ⊤ := by
  rw [Submodule.span_range_eq_iSup]
  simpa only [← u.projectivizes, Projectivization.submodule_mk] using
    hl.four_spans e he

noncomputable def ProjectiveLift.selectedBasis {n : ℕ} {l : ProjectiveConfig n}
    (u : ProjectiveLift l) (hl : IsGeneric l)
    (e : Fin 4 → Fin n) (he : Function.Injective e) :
    Module.Basis (Fin 4) ℂ SymplecticVector :=
  basisOfTopLeSpanOfCardEqFinrank
    (fun k => u.vec (e k))
    (le_of_eq (u.selected_span hl e he).symm)
    (by simp)

@[simp] theorem ProjectiveLift.selectedBasis_apply {n : ℕ}
    {l : ProjectiveConfig n} (u : ProjectiveLift l) (hl : IsGeneric l)
    (e : Fin 4 → Fin n) (he : Function.Injective e) (k : Fin 4) :
    u.selectedBasis hl e he k = u.vec (e k) := by
  simp [ProjectiveLift.selectedBasis]

/-- Diagonal congruence of canonical Gram matrices is precisely the remaining
ambiguity before passing to the symplectic orbit of projective configurations. -/
theorem exists_symplectic_smul_of_projectiveGram_diagonalCongruent {n : ℕ}
    (l m : ProjectiveConfig n) (hl : IsGeneric l) (hm : IsGeneric m)
    (e : Fin 4 → Fin n) (he : Function.Injective e)
    (d : Fin n → ℂˣ)
    (hgram : projectiveGram l =
      diagonalCongruence (fun i => (d i : ℂ)) (projectiveGram m)) :
    ∃ g : SymplecticGroup, g • l = m := by
  let ul := canonicalProjectiveLift l
  let w : Fin n → SymplecticVector := fun i => (d i : ℂ) • projectiveRepresentatives m i
  have hw_ne (i : Fin n) : w i ≠ 0 :=
    smul_ne_zero (Units.ne_zero (d i)) (projectiveRepresentatives_ne_zero m i)
  let um : ProjectiveLift m :=
    { vec := w
      ne_zero := hw_ne
      projectivizes := fun i => by
        rw [← Projectivization.mk_rep (m i), Projectivization.mk_eq_mk_iff']
        exact ⟨(d i : ℂ), rfl⟩ }
  have hwgram : gram w =
      diagonalCongruence (fun i => (d i : ℂ)) (projectiveGram m) := by
    rw [gram_smul]
    rfl
  have hulgram : gram ul.vec = gram um.vec := by
    simpa [ul, um, w, projectiveGram, canonicalProjectiveLift] using
      hgram.trans hwgram.symm
  let bl := ul.selectedBasis hl e he
  let bm := um.selectedBasis hm e he
  obtain ⟨g, hg⟩ := exists_symplectic_of_gram_eq ul.vec um.vec e bl bm
    (by intro i; simp [bl]) (by intro i; simp [bm]) hulgram
  refine ⟨g, funext fun i => ?_⟩
  change g.1 • l i = m i
  rw [← ul.projectivizes i, ← um.projectivizes i, Projectivization.smul_mk]
  rw [Projectivization.mk_eq_mk_iff']
  exact ⟨1, by simpa using (hg i).symm⟩

/-- Surjectivity of the Gram-classification map onto diagonal-congruence
classes, stated without constructing a quotient type. -/
theorem IsAdmissibleGram.exists_projectiveGram_diagonalCongruent {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsAdmissibleGram A)
    (e : Fin 4 → Fin n) (he : Function.Injective e) :
    ∃ (l : ProjectiveConfig n), IsGeneric l ∧
      ∃ d : Fin n → ℂˣ,
        projectiveGram l = diagonalCongruence (fun i => (d i : ℂ)) A := by
  obtain ⟨l, u, hl, hu⟩ := hA.exists_generic_realization e he
  obtain ⟨d, hd⟩ := (canonicalProjectiveLift l).gram_diagonalCongruent u
  refine ⟨l, hl, d, ?_⟩
  simpa [projectiveGram, canonicalProjectiveLift, hu] using hd

/-! ## Canonical diagonal normalization -/

/-- The normalization conditions `A₀ⱼ = 1` for `j ≠ 0` and `A₁₂ = 1`.
The index type is written as `Fin (n+3)` so all three distinguished indices exist. -/
structure IsNormalized {n : ℕ} (A : Matrix (Fin (n + 3)) (Fin (n + 3)) ℂ) : Prop where
  firstRow : ∀ j, j ≠ 0 → A 0 j = 1
  twelve : A 1 2 = 1

private theorem finTwo_ne_zero {n : ℕ} : (2 : Fin (n + 3)) ≠ 0 := by
  have hlt : 2 < n + 3 := by omega
  intro h
  have hv := congrArg Fin.val h
  change 2 % (n + 3) = 0 % (n + 3) at hv
  rw [Nat.mod_eq_of_lt hlt] at hv
  simp at hv

/-- Existence of a normalized representative.  The only choice is a square
root in `ℂ`; the uniqueness theorem below shows that the resulting matrix is
independent of that choice. -/
theorem exists_normalized_diagonalCongruence {n : ℕ}
    (A : Matrix (Fin (n + 3)) (Fin (n + 3)) ℂ)
    (hoff : ∀ i j, i ≠ j → A i j ≠ 0) :
    ∃ d : Fin (n + 3) → ℂˣ,
      IsNormalized (diagonalCongruence (fun i => (d i : ℂ)) A) := by
  have h01 : A 0 1 ≠ 0 := hoff 0 1 (by norm_num)
  have h02 : A 0 2 ≠ 0 := hoff 0 2 (by
    intro h
    exact finTwo_ne_zero (h.symm.trans (by rfl)))
  have h12 : A 1 2 ≠ 0 := hoff 1 2 (by
    intro h
    have hv := congrArg Fin.val h
    have hlt : 2 < n + 3 := by omega
    change 1 % (n + 3) = 2 % (n + 3) at hv
    rw [Nat.mod_eq_of_lt (by omega : 1 < n + 3), Nat.mod_eq_of_lt hlt] at hv
    omega)
  let target : ℂ := A 1 2 / (A 0 1 * A 0 2)
  have htarget : target ≠ 0 := div_ne_zero h12 (mul_ne_zero h01 h02)
  obtain ⟨d₀, hd₀sq⟩ := IsAlgClosed.exists_eq_mul_self target
  have hd₀ : d₀ ≠ 0 := by
    intro hz
    apply htarget
    rw [hd₀sq, hz, zero_mul]
  have hd₀mul : (d₀ * d₀) * (A 0 1 * A 0 2) = A 1 2 := by
    apply (eq_div_iff (mul_ne_zero h01 h02)).mp
    exact hd₀sq.symm
  let dc : Fin (n + 3) → ℂ := fun i =>
    if i = 0 then d₀ else 1 / (d₀ * A 0 i)
  have hdc (i : Fin (n + 3)) : dc i ≠ 0 := by
    by_cases hi : i = 0
    · simpa [dc, hi] using hd₀
    · simp [dc, hi, hd₀, hoff 0 i (Ne.symm hi)]
  let d : Fin (n + 3) → ℂˣ := fun i => Units.mk0 (dc i) (hdc i)
  refine ⟨d, ?_⟩
  constructor
  · intro j hj
    change dc 0 * A 0 j * dc j = 1
    simp [dc, hj]
    field_simp [hd₀, hoff 0 j (Ne.symm hj)]
  · change dc 1 * A 1 2 * dc 2 = 1
    simp only [dc, if_neg (by norm_num : (1 : Fin (n + 3)) ≠ 0),
      if_neg finTwo_ne_zero, one_div]
    field_simp [hd₀, h01, h02]
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hd₀mul.symm

/-- A normalized matrix cannot be changed by a nonzero diagonal congruence
and remain normalized.  This is the branch-free uniqueness argument. -/
theorem normalized_diagonalCongruence_unique {n : ℕ}
    (B C : Matrix (Fin (n + 3)) (Fin (n + 3)) ℂ)
    (r : Fin (n + 3) → ℂ) (hr : ∀ i, r i ≠ 0)
    (hB : IsNormalized B) (hC : IsNormalized C)
    (hrel : C = diagonalCongruence r B) : C = B := by
  have hr0j (j : Fin (n + 3)) (hj : j ≠ 0) : r 0 * r j = 1 := by
    have hentry := congr_fun (congr_fun hrel 0) j
    change C 0 j = r 0 * B 0 j * r j at hentry
    rw [hC.firstRow j hj, hB.firstRow j hj] at hentry
    simpa using hentry.symm
  have hr12 : r 1 * r 2 = 1 := by
    have hentry := congr_fun (congr_fun hrel 1) 2
    change C 1 2 = r 1 * B 1 2 * r 2 at hentry
    rw [hC.twelve, hB.twelve] at hentry
    simpa using hentry.symm
  have h01 : r 0 * r 1 = 1 := hr0j 1 (by norm_num)
  have h02 : r 0 * r 2 = 1 := hr0j 2 finTwo_ne_zero
  have h00 : r 0 * r 0 = 1 := by
    calc
      r 0 * r 0 = (r 0 * r 0) * (r 1 * r 2) := by rw [hr12, mul_one]
      _ = (r 0 * r 1) * (r 0 * r 2) := by ring
      _ = 1 := by rw [h01, h02, one_mul]
  have hrprod (i j : Fin (n + 3)) : r i * r j = 1 := by
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = 0
      · subst j
        exact h00
      · exact hr0j j hj
    · by_cases hj : j = 0
      · subst j
        simpa [mul_comm] using hr0j i hi
      · apply mul_left_cancel₀ (mul_ne_zero (hr 0) (hr 0))
        calc
          (r 0 * r 0) * (r i * r j) = (r 0 * r i) * (r 0 * r j) := by ring
          _ = (r 0 * r 0) * 1 := by rw [hr0j i hi, hr0j j hj, h00]
  rw [hrel]
  ext i j
  change r i * B i j * r j = B i j
  calc
    r i * B i j * r j = (r i * r j) * B i j := by ring
    _ = B i j := by rw [hrprod, one_mul]

/-- Hence two normalized representatives in one diagonal-congruence orbit are
literally equal, independently of the square-root choice used for existence. -/
theorem normalized_orbit_unique {n : ℕ}
    (A : Matrix (Fin (n + 3)) (Fin (n + 3)) ℂ)
    (d e : Fin (n + 3) → ℂˣ)
    (hd : IsNormalized (diagonalCongruence (fun i => (d i : ℂ)) A))
    (he : IsNormalized (diagonalCongruence (fun i => (e i : ℂ)) A)) :
    diagonalCongruence (fun i => (d i : ℂ)) A =
      diagonalCongruence (fun i => (e i : ℂ)) A := by
  let r : Fin (n + 3) → ℂ := fun i => ((e i / d i : ℂˣ) : ℂ)
  have hr (i : Fin (n + 3)) : r i ≠ 0 := Units.ne_zero _
  have hrel : diagonalCongruence (fun i => (e i : ℂ)) A =
      diagonalCongruence r (diagonalCongruence (fun i => (d i : ℂ)) A) := by
    ext i j
    simp only [diagonalCongruence, r, Units.val_div_eq_div_val]
    field_simp [Units.ne_zero]
  exact (normalized_diagonalCongruence_unique _ _ r hr hd he hrel).symm

end
end Sp4
