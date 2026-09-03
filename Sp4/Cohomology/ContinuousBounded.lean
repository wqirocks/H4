import Sp4.Symplectic.Model
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Homogeneous continuous bounded cohomology in degree four

This file defines, rather than postulates, the continuous bounded cochain complex
used in the last line of the article.  A degree-`q` cochain on a topological group
`G` is a bounded continuous real function on `G ^ (q + 1)`.  We take the subspace
fixed by diagonal left translation and use the usual alternating deletion
coboundary.

For the final theorem we instantiate this construction on the matrix groups
`Sp(4, ℂ)` and `SL(2, ℂ)`, both with their matrix-coordinate topology.  Mathlib
already supplies the topological-group structure of the latter.  The inverse in
the symplectic matrix group is the polynomial map `A ↦ -J Aᵀ J`; this gives the
short topological-group proof below.

The only adjacent-differential relation needed by the paper is the map from
degree three through degree five.  `coboundary_squared_three` checks its thirty
summands explicitly, using the twice-deletion identity, before the quotient
`H4` is formed.
-/

namespace Sp4
namespace ContinuousBounded

noncomputable section

open scoped BoundedContinuousFunction

/-- The standard complex symplectic matrix group of rank two. -/
abbrev MatrixSp4C := Matrix.symplecticGroup (Fin 2) ℂ

/-- The complex rank-one special linear group used for restriction. -/
abbrev MatrixSL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ

/-- The matrix-coordinate topology makes `Sp(4, ℂ)` a topological group. -/
instance : IsTopologicalGroup MatrixSp4C where
  continuous_mul := continuous_induced_rng.mpr
    ((continuous_induced_dom.comp continuous_fst).mul
      (continuous_induced_dom.comp continuous_snd))
  continuous_inv := continuous_induced_rng.mpr <| by
    rw [show (Subtype.val ∘ fun a : MatrixSp4C ↦ a⁻¹) =
      fun (a : MatrixSp4C) ↦ (-Matrix.J (Fin 2) ℂ) *
        Matrix.transpose (a : Matrix _ _ ℂ) *
        Matrix.J (Fin 2) ℂ by
      funext a
      exact _root_.SymplecticGroup.coe_inv a]
    exact (continuous_const.mul continuous_induced_dom.matrix_transpose).mul continuous_const

/-- Homogeneous bounded continuous real cochains in degree `q`. -/
abbrev Cochain (G : Type*) [TopologicalSpace G] (q : ℕ) :=
  (Fin (q + 1) → G) →ᵇ ℝ

/-- Deletion of one homogeneous coordinate, as a continuous map. -/
def deleteContinuous {G : Type*} [TopologicalSpace G] (q : ℕ)
    (i : Fin (q + 2)) : C((Fin (q + 2) → G), (Fin (q + 1) → G)) :=
  ⟨fun x ↦ FinTuple.delete i x,
    continuous_pi fun j ↦ continuous_apply (i.succAbove j)⟩

/-- Pullback along the `i`-th deletion map. -/
def face {G : Type*} [TopologicalSpace G] (q : ℕ) (i : Fin (q + 2)) :
    Cochain G q →ₗ[ℝ] Cochain G (q + 1) :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ (deleteContinuous q i)).toLinearMap

@[simp]
theorem face_apply {G : Type*} [TopologicalSpace G] (q : ℕ) (i : Fin (q + 2))
    (F : Cochain G q) (x : Fin (q + 2) → G) :
    face q i F x = F (FinTuple.delete i x) :=
  rfl

/-- The homogeneous alternating coboundary. -/
def coboundary {G : Type*} [TopologicalSpace G] (q : ℕ) :
    Cochain G q →ₗ[ℝ] Cochain G (q + 1) :=
  ∑ i : Fin (q + 2), (-1 : ℝ) ^ i.1 • face q i

@[simp]
theorem coboundary_apply {G : Type*} [TopologicalSpace G] (q : ℕ)
    (F : Cochain G q) (x : Fin (q + 2) → G) :
    coboundary q F x =
      ∑ i : Fin (q + 2), (-1 : ℝ) ^ i.1 * F (FinTuple.delete i x) := by
  simp [coboundary]

/-- Cochains invariant under simultaneous left translation of every entry. -/
def InvariantCochains (G : Type*) [Group G] [TopologicalSpace G] (q : ℕ) :
    Submodule ℝ (Cochain G q) where
  carrier := {F | ∀ (g : G) (x : Fin (q + 1) → G),
    F (fun j ↦ g * x j) = F x}
  zero_mem' := by simp
  add_mem' := by
    intro F H hF hH g x
    simp only [BoundedContinuousFunction.coe_add, Pi.add_apply, hF g x, hH g x]
  smul_mem' := by
    intro c F hF g x
    simp only [BoundedContinuousFunction.coe_smul, hF g x]

/-- The coboundary restricted to invariant cochains. -/
def invariantCoboundary {G : Type*} [Group G] [TopologicalSpace G] (q : ℕ) :
    InvariantCochains G q →ₗ[ℝ] InvariantCochains G (q + 1) where
  toFun F := ⟨coboundary q F.1, by
    intro g x
    simp only [coboundary_apply]
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    have h := F.2 g (FinTuple.delete i x)
    exact h⟩
  map_add' F H := by
    apply Subtype.ext
    exact map_add (coboundary q) F.1 H.1
  map_smul' c F := by
    apply Subtype.ext
    exact map_smul (coboundary q) c F.1

@[simp]
theorem invariantCoboundary_coe {G : Type*} [Group G] [TopologicalSpace G]
    (q : ℕ) (F : InvariantCochains G q) :
    (invariantCoboundary q F).1 = coboundary q F.1 :=
  rfl

/-- The degree-three-to-five instance of `d ∘ d = 0`, checked directly. -/
theorem coboundary_squared_three {G : Type*} [TopologicalSpace G]
    (F : Cochain G 3) : coboundary 4 (coboundary 3 F) = 0 := by
  ext x
  simp only [coboundary_apply]
  norm_num [Fin.sum_univ_succ]
  have h01 : FinTuple.delete (0 : Fin 5) (FinTuple.delete (0 : Fin 6) x) =
      FinTuple.delete (0 : Fin 5) (FinTuple.delete (1 : Fin 6) x) := by
    funext k
    fin_cases k <;> rfl
  have h02 : FinTuple.delete (1 : Fin 5) (FinTuple.delete (0 : Fin 6) x) =
      FinTuple.delete (0 : Fin 5) (FinTuple.delete (2 : Fin 6) x) := by
    funext k
    fin_cases k <;> rfl
  have h03 : FinTuple.delete (2 : Fin 5) (FinTuple.delete (0 : Fin 6) x) =
      FinTuple.delete (0 : Fin 5)
        (FinTuple.delete (Fin.succ (2 : Fin 5)) x) := by
    funext k
    fin_cases k <;> rfl
  have h04 : FinTuple.delete (Fin.succ (2 : Fin 4))
      (FinTuple.delete (0 : Fin 6) x) =
      FinTuple.delete (0 : Fin 5)
        (FinTuple.delete (Fin.succ (Fin.succ (2 : Fin 4))) x) := by
    funext k
    fin_cases k <;> rfl
  have h05 : FinTuple.delete (Fin.succ (Fin.succ (2 : Fin 3)))
      (FinTuple.delete (0 : Fin 6) x) =
      FinTuple.delete (0 : Fin 5)
        (FinTuple.delete (Fin.succ (Fin.succ (Fin.succ (2 : Fin 3)))) x) := by
    funext k
    fin_cases k <;> rfl
  have h12 : FinTuple.delete (1 : Fin 5) (FinTuple.delete (1 : Fin 6) x) =
      FinTuple.delete (1 : Fin 5) (FinTuple.delete (2 : Fin 6) x) := by
    funext k
    fin_cases k <;> rfl
  have h13 : FinTuple.delete (2 : Fin 5) (FinTuple.delete (1 : Fin 6) x) =
      FinTuple.delete (1 : Fin 5)
        (FinTuple.delete (Fin.succ (2 : Fin 5)) x) := by
    funext k
    fin_cases k <;> rfl
  have h14 : FinTuple.delete (Fin.succ (2 : Fin 4))
      (FinTuple.delete (1 : Fin 6) x) =
      FinTuple.delete (1 : Fin 5)
        (FinTuple.delete (Fin.succ (Fin.succ (2 : Fin 4))) x) := by
    funext k
    fin_cases k <;> rfl
  have h15 : FinTuple.delete (Fin.succ (Fin.succ (2 : Fin 3)))
      (FinTuple.delete (1 : Fin 6) x) =
      FinTuple.delete (1 : Fin 5)
        (FinTuple.delete (Fin.succ (Fin.succ (Fin.succ (2 : Fin 3)))) x) := by
    funext k
    fin_cases k <;> rfl
  have h23 : FinTuple.delete (2 : Fin 5) (FinTuple.delete (2 : Fin 6) x) =
      FinTuple.delete (2 : Fin 5)
        (FinTuple.delete (Fin.succ (2 : Fin 5)) x) := by
    funext k
    fin_cases k <;> rfl
  have h24 : FinTuple.delete (Fin.succ (2 : Fin 4))
      (FinTuple.delete (2 : Fin 6) x) =
      FinTuple.delete (2 : Fin 5)
        (FinTuple.delete (Fin.succ (Fin.succ (2 : Fin 4))) x) := by
    funext k
    fin_cases k <;> rfl
  have h25 : FinTuple.delete (Fin.succ (Fin.succ (2 : Fin 3)))
      (FinTuple.delete (2 : Fin 6) x) =
      FinTuple.delete (2 : Fin 5)
        (FinTuple.delete (Fin.succ (Fin.succ (Fin.succ (2 : Fin 3)))) x) := by
    funext k
    fin_cases k <;> rfl
  have h34 : FinTuple.delete (Fin.succ (2 : Fin 4))
      (FinTuple.delete (Fin.succ (2 : Fin 5)) x) =
      FinTuple.delete (Fin.succ (2 : Fin 4))
        (FinTuple.delete (Fin.succ (Fin.succ (2 : Fin 4))) x) := by
    funext k
    fin_cases k <;> rfl
  have h35 : FinTuple.delete (Fin.succ (Fin.succ (2 : Fin 3)))
      (FinTuple.delete (Fin.succ (2 : Fin 5)) x) =
      FinTuple.delete (Fin.succ (2 : Fin 4))
        (FinTuple.delete (Fin.succ (Fin.succ (Fin.succ (2 : Fin 3)))) x) := by
    funext k
    fin_cases k <;> rfl
  have h45 : FinTuple.delete (Fin.succ (Fin.succ (2 : Fin 3)))
      (FinTuple.delete (Fin.succ (Fin.succ (2 : Fin 4))) x) =
      FinTuple.delete (Fin.succ (Fin.succ (2 : Fin 3)))
        (FinTuple.delete (Fin.succ (Fin.succ (Fin.succ (2 : Fin 3)))) x) := by
    funext k
    fin_cases k <;> rfl
  rw [h01, h02, h03, h04, h05, h12, h13, h14, h15, h23, h24, h25,
    h34, h35, h45]
  ring

theorem invariantCoboundary_squared_three {G : Type*} [Group G] [TopologicalSpace G]
    (F : InvariantCochains G 3) :
    invariantCoboundary 4 (invariantCoboundary 3 F) = 0 := by
  apply Subtype.ext
  exact coboundary_squared_three F.1

/-- Degree-four invariant continuous bounded cocycles. -/
def Cocycles4 (G : Type*) [Group G] [TopologicalSpace G] :
    Submodule ℝ (InvariantCochains G 4) :=
  LinearMap.ker (invariantCoboundary 4)

instance cocycles4AddCommGroup (G : Type*) [Group G] [TopologicalSpace G] :
    AddCommGroup (Cocycles4 G) := by
  exact @Submodule.addCommGroup ℝ (InvariantCochains G 4) inferInstance
    inferInstance inferInstance (Cocycles4 G)

/-- Every degree-three coboundary is a degree-four cocycle. -/
def boundaryToCocycles {G : Type*} [Group G] [TopologicalSpace G] :
    InvariantCochains G 3 →ₗ[ℝ] Cocycles4 G :=
  (invariantCoboundary 3).codRestrict (Cocycles4 G) fun F ↦
    invariantCoboundary_squared_three F

/-- Degree-four invariant continuous bounded boundaries. -/
def Boundaries4 (G : Type*) [Group G] [TopologicalSpace G] :
    Submodule ℝ (Cocycles4 G) :=
  LinearMap.range boundaryToCocycles

/-- Fourth continuous bounded cohomology with trivial real coefficients. -/
abbrev H4 (G : Type*) [Group G] [TopologicalSpace G] :=
  (Cocycles4 G : Type _) ⧸ Boundaries4 G

abbrev H4Sp4C := H4 MatrixSp4C
abbrev H4SL2C := H4 MatrixSL2C

/-! ## The standard rank-one block inclusion -/

/-- Put a two-by-two matrix on the first symplectic plane and fix the second
plane.  Relative to the `e₁,e₂,f₁,f₂` block order, this is the standard
rank-one inclusion used by Blatz. -/
def rankOneBlock (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks
    !![A 0 0, 0; 0, 1]
    !![A 0 1, 0; 0, 0]
    !![A 1 0, 0; 0, 0]
    !![A 1 1, 0; 0, 1]

@[simp]
theorem rankOneBlock_one :
    rankOneBlock (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;> simp [rankOneBlock, Matrix.fromBlocks]

@[simp]
theorem rankOneBlock_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    rankOneBlock (A * B) = rankOneBlock A * rankOneBlock B := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
      simp [rankOneBlock, Matrix.fromBlocks, Matrix.mul_apply, Fin.sum_univ_two]

/-- A determinant-one two-by-two block preserves the rank-two symplectic form. -/
theorem rankOneBlock_mem_symplectic (A : MatrixSL2C) :
    rankOneBlock A.1 ∈ Matrix.symplecticGroup (Fin 2) ℂ := by
  have hdet : A.1 0 0 * A.1 1 1 - A.1 0 1 * A.1 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.2
  rw [_root_.SymplecticGroup.mem_iff]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
      simp [rankOneBlock, Matrix.J, Matrix.fromBlocks, Matrix.mul_apply,
        Fin.sum_univ_two] <;> ring_nf
  · linear_combination -hdet
  · linear_combination hdet

/-- The standard rank-one inclusion as a group homomorphism. -/
def rankOneInclusionMonoidHom : MatrixSL2C →* MatrixSp4C where
  toFun A := ⟨rankOneBlock A.1, rankOneBlock_mem_symplectic A⟩
  map_one' := Subtype.ext rankOneBlock_one
  map_mul' A B := Subtype.ext (rankOneBlock_mul A.1 B.1)

theorem continuous_rankOneBlock : Continuous rankOneBlock := by
  apply continuous_matrix
  intro i j
  rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;>
      simp [rankOneBlock, Matrix.fromBlocks] <;> fun_prop

/-- The standard inclusion `SL(2, ℂ) = Sp(2, ℂ) → Sp(4, ℂ)` as a
continuous group homomorphism. -/
def rankOneInclusion : MatrixSL2C →ₜ* MatrixSp4C where
  toFun := rankOneInclusionMonoidHom
  map_one' := rankOneInclusionMonoidHom.map_one
  map_mul' := rankOneInclusionMonoidHom.map_mul
  continuous_toFun := by
    exact continuous_induced_rng.mpr
      (continuous_rankOneBlock.comp continuous_induced_dom)

/-! ## Restriction along a continuous group homomorphism -/

variable {H G : Type*} [Group H] [Group G]
  [TopologicalSpace H] [TopologicalSpace G]

/-- Apply a continuous group homomorphism in every homogeneous coordinate. -/
def mapTupleContinuous (iota : H →ₜ* G) (q : ℕ) :
    C((Fin (q + 1) → H), (Fin (q + 1) → G)) :=
  ⟨fun x j ↦ iota (x j),
    continuous_pi fun j ↦ iota.toContinuousMap.continuous.comp (continuous_apply j)⟩

/-- Cochain restriction is precomposition by the coordinatewise homomorphism. -/
def restrictCochain (iota : H →ₜ* G) (q : ℕ) :
    Cochain G q →ₗ[ℝ] Cochain H q :=
  (BoundedContinuousFunction.compContinuousCLM ℝ ℝ
    (mapTupleContinuous iota q)).toLinearMap

@[simp]
theorem restrictCochain_apply (iota : H →ₜ* G) (q : ℕ)
    (F : Cochain G q) (x : Fin (q + 1) → H) :
    restrictCochain iota q F x = F (fun j ↦ iota (x j)) :=
  rfl

/-- Restriction preserves diagonal invariance. -/
def restrictInvariant (iota : H →ₜ* G) (q : ℕ) :
    InvariantCochains G q →ₗ[ℝ] InvariantCochains H q where
  toFun F := ⟨restrictCochain iota q F.1, by
    intro h x
    change F.1 (fun j ↦ iota (h * x j)) = F.1 (fun j ↦ iota (x j))
    simpa only [map_mul] using F.2 (iota h) (fun j ↦ iota (x j))⟩
  map_add' F K := by
    apply Subtype.ext
    exact map_add (restrictCochain iota q) F.1 K.1
  map_smul' c F := by
    apply Subtype.ext
    exact map_smul (restrictCochain iota q) c F.1

/-- Restriction commutes with the homogeneous coboundary. -/
theorem restrictInvariant_coboundary (iota : H →ₜ* G) (q : ℕ)
    (F : InvariantCochains G q) :
    restrictInvariant iota (q + 1) (invariantCoboundary q F) =
      invariantCoboundary q (restrictInvariant iota q F) := by
  apply Subtype.ext
  apply BoundedContinuousFunction.ext
  intro x
  change coboundary q F.1 (fun j ↦ iota (x j)) =
    coboundary q (restrictCochain iota q F.1) x
  simp only [coboundary_apply, restrictCochain_apply]
  apply Finset.sum_congr rfl
  intro j hj
  congr 2

/-- Restriction on degree-four cocycles. -/
def restrictCocycles4 (iota : H →ₜ* G) :
    Cocycles4 G →ₗ[ℝ] Cocycles4 H where
  toFun F := ⟨restrictInvariant iota 4 F.1, by
    change invariantCoboundary 4 (restrictInvariant iota 4 F.1) = 0
    rw [← restrictInvariant_coboundary]
    rw [F.2, map_zero]⟩
  map_add' F K := by
    apply Subtype.ext
    exact map_add (restrictInvariant iota 4) F.1 K.1
  map_smul' c F := by
    apply Subtype.ext
    exact map_smul (restrictInvariant iota 4) c F.1

theorem restrictCocycles4_maps_boundaries (iota : H →ₜ* G) :
    Boundaries4 G ≤ (Boundaries4 H).comap (restrictCocycles4 iota) := by
  intro z hz
  rcases hz with ⟨F, rfl⟩
  refine ⟨restrictInvariant iota 3 F, ?_⟩
  apply Subtype.ext
  exact (restrictInvariant_coboundary iota 3 F).symm

/-- The actual map on fourth continuous bounded cohomology induced by a
continuous group homomorphism. -/
def restrictionH4 (iota : H →ₜ* G) : H4 G →ₗ[ℝ] H4 H :=
  (Boundaries4 G).mapQ (Boundaries4 H) (restrictCocycles4 iota)
    (restrictCocycles4_maps_boundaries iota)

/-- Restriction from `Sp(4, ℂ)` to its standard rank-one subgroup. -/
abbrev rankOneRestrictionH4 : H4Sp4C →ₗ[ℝ] H4SL2C :=
  restrictionH4 rankOneInclusion

end
end ContinuousBounded
end Sp4
