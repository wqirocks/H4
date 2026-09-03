import Sp4.Basic.ComplexAlgebra
import Sp4.Basic.FinTuple
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# The fixed four-dimensional complex symplectic model

This file fixes the basis `(e₁,f₁,e₂,f₂)`, the matrix and sign convention
for the symplectic form, the symplectic group, and its projective action.  It also
contains the tuple-level genericity predicate used by Gram classification.
-/

namespace Sp4

open scoped LinearAlgebra.Projectivization

/-- The fixed complex vector space `ℂ⁴`. -/
abbrev SymplecticVector := Fin 4 → ℂ

/-- The projective three-space of complex lines in the fixed symplectic space. -/
abbrev ProjectivePoint := Projectivization ℂ SymplecticVector

/-- Matrix of the symplectic form in the ordered basis `(e₁,f₁,e₂,f₂)`. -/
def symplecticJ : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 0, 0;
     -1, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, -1, 0]

/-- The fixed complex-bilinear symplectic form. -/
def omega : LinearMap.BilinForm ℂ SymplecticVector := symplecticJ.toBilin'

theorem omega_apply (v w : SymplecticVector) :
    omega v w = v 0 * w 1 - v 1 * w 0 + v 2 * w 3 - v 3 * w 2 := by
  simp [omega, symplecticJ, Matrix.toBilin'_apply, Fin.sum_univ_succ]
  ring

theorem omega_isAlt : omega.IsAlt := by
  intro v
  rw [omega_apply]
  ring

theorem omega_skew (v w : SymplecticVector) : omega w v = -omega v w := by
  rw [omega_apply, omega_apply]
  ring

theorem symplecticJ_det : symplecticJ.det = 1 := by
  simp [symplecticJ, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

/-- Coordinate proof that the fixed symplectic form separates vectors on both sides. -/
theorem omega_nondegenerate : omega.Nondegenerate := by
  have hleft : omega.SeparatingLeft := by
    intro v hv
    have h0 : v 0 = 0 := by
      simpa [omega_apply] using hv (Pi.single (1 : Fin 4) 1)
    have h1 : v 1 = 0 := by
      have h : -v 1 = 0 := by
        simpa [omega_apply] using hv (Pi.single (0 : Fin 4) 1)
      exact neg_eq_zero.mp h
    have h2 : v 2 = 0 := by
      simpa [omega_apply] using hv (Pi.single (3 : Fin 4) 1)
    have h3 : v 3 = 0 := by
      have h : -v 3 = 0 := by
        simpa [omega_apply] using hv (Pi.single (2 : Fin 4) 1)
      exact neg_eq_zero.mp h
    funext i
    fin_cases i <;> assumption
  refine ⟨hleft, ?_⟩
  intro v hv
  apply hleft v
  intro w
  calc
    omega v w = -omega w v := by rw [omega_skew]
    _ = 0 := by rw [hv w]; simp

/-- `Sp(4,ℂ)` as the subgroup of linear equivalences preserving `omega`. -/
def SymplecticGroup : Subgroup (SymplecticVector ≃ₗ[ℂ] SymplecticVector) where
  carrier := {g | ∀ v w, omega (g v) (g w) = omega v w}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh v w
    change omega (g (h v)) (g (h w)) = omega v w
    rw [hg, hh]
  inv_mem' := by
    intro g hg v w
    have h := hg (g⁻¹ v) (g⁻¹ w)
    simpa using h.symm

@[simp] theorem SymplecticGroup.preserves (g : SymplecticGroup)
    (v w : SymplecticVector) : omega (g.1 v) (g.1 w) = omega v w :=
  g.2 v w

/-- The central symplectic map `-I`. -/
def centralNeg : SymplecticGroup :=
  ⟨LinearEquiv.neg ℂ, by
    intro v w
    simp only [LinearEquiv.neg_apply]
    simp⟩

@[simp] theorem centralNeg_apply (v : SymplecticVector) : centralNeg.1 v = -v := rfl

@[simp] theorem centralNeg_smul_projective (p : ProjectivePoint) : centralNeg • p = p := by
  induction p using Projectivization.ind with
  | h v hv =>
      change (LinearEquiv.neg ℂ : SymplecticVector ≃ₗ[ℂ] SymplecticVector) •
        Projectivization.mk ℂ v hv = Projectivization.mk ℂ v hv
      rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
      exact ⟨-1, by simp⟩

/-- A linear automorphism fixing every complex line is a homothety. -/
theorem linearEquiv_eq_smul_of_projective_fixed
    (g : SymplecticVector ≃ₗ[ℂ] SymplecticVector)
    (hfix : ∀ p : ProjectivePoint, g • p = p) :
    ∃ c : ℂ, ∀ v : SymplecticVector, g v = c • v := by
  let f : SymplecticVector →ₗ[ℂ] SymplecticVector := g.toLinearMap
  obtain ⟨c, hc⟩ := f.exists_eq_smul_id_of_forall_notLinearIndependent fun v => by
    by_cases hv : v = 0
    · simp [hv, linearIndependent_fin2]
    · simpa [LinearIndependent.pair_iff' hv, Projectivization.mk_eq_mk_iff'] using!
        hfix (Projectivization.mk ℂ v hv)
  refine ⟨c, fun v => ?_⟩
  have hv := LinearMap.congr_fun hc v
  simpa [f] using hv

/-- The kernel of the projective action of `Sp(4,ℂ)` is exactly `{I,-I}`. -/
theorem symplectic_fixes_projective_iff (g : SymplecticGroup) :
    (∀ p : ProjectivePoint, g • p = p) ↔ g = 1 ∨ g = centralNeg := by
  constructor
  · intro hfix
    obtain ⟨c, hc⟩ := linearEquiv_eq_smul_of_projective_fixed g.1 hfix
    have hpair := g.2 (Pi.single (0 : Fin 4) 1) (Pi.single (1 : Fin 4) 1)
    rw [hc, hc] at hpair
    have hc2 : c * c = 1 := by
      simpa [omega_apply] using hpair
    rcases mul_self_eq_one_iff.mp hc2 with hc1 | hcneg
    · left
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      simpa [hc1] using hc v
    · right
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      simpa [hcneg] using hc v
  · rintro (rfl | rfl) p
    · simp
    · exact centralNeg_smul_projective p

/-- Transversality of two projective lines, evaluated on the canonical nonzero
representatives supplied by projectivization. -/
def Transverse (l m : ProjectivePoint) : Prop := omega l.rep m.rep ≠ 0

/-- Transversality is independent of the nonzero representatives. -/
theorem transverse_mk_iff (v w : SymplecticVector) (hv : v ≠ 0) (hw : w ≠ 0) :
    Transverse (Projectivization.mk ℂ v hv) (Projectivization.mk ℂ w hw) ↔
      omega v w ≠ 0 := by
  rcases Projectivization.exists_smul_eq_mk_rep ℂ v hv with ⟨a, ha⟩
  rcases Projectivization.exists_smul_eq_mk_rep ℂ w hw with ⟨b, hb⟩
  unfold Transverse
  rw [← ha, ← hb]
  simp [Units.smul_def]

theorem Transverse.symm {l m : ProjectivePoint} (h : Transverse l m) : Transverse m l := by
  intro hzero
  apply h
  rw [omega_skew, hzero, neg_zero]

theorem not_transverse_self (l : ProjectivePoint) : ¬Transverse l l := by
  intro h
  exact h (omega_isAlt l.rep)

theorem transverse_smul_iff (g : SymplecticGroup) (l m : ProjectivePoint) :
    Transverse (g • l) (g • m) ↔ Transverse l m := by
  induction l using Projectivization.ind with
  | h v hv =>
      induction m using Projectivization.ind with
      | h w hw =>
          change Transverse (g.1 • Projectivization.mk ℂ v hv)
            (g.1 • Projectivization.mk ℂ w hw) ↔ _
          rw [Projectivization.smul_mk, Projectivization.smul_mk,
            transverse_mk_iff, transverse_mk_iff]
          simpa [LinearEquiv.smul_def] using not_congr (g.2 v w)

theorem projective_submodule_smul
    (g : SymplecticVector ≃ₗ[ℂ] SymplecticVector) (p : ProjectivePoint) :
    (g • p).submodule = p.submodule.map g.toLinearMap := by
  induction p using Projectivization.ind with
  | h v hv =>
      simp [Projectivization.submodule_mk, Projectivization.smul_mk,
        ← Submodule.span_image]

/-- Ordered configurations of projective lines. -/
abbrev ProjectiveConfig (n : ℕ) := FinTuple ProjectivePoint n

/-- Pairwise transversality and spanning by every ordered selection of four
distinct lines. -/
structure IsGeneric {n : ℕ} (l : ProjectiveConfig n) : Prop where
  pairwise_transverse : ∀ i j, i ≠ j → Transverse (l i) (l j)
  four_spans : ∀ (e : Fin 4 → Fin n), Function.Injective e →
    (⨆ k, (l (e k)).submodule) = ⊤

/-- Deleting one point preserves genericity. -/
theorem IsGeneric.delete {n : ℕ} {l : ProjectiveConfig (n + 1)}
    (hl : IsGeneric l) (i : Fin (n + 1)) : IsGeneric (FinTuple.delete i l) := by
  constructor
  · intro a b hab
    exact hl.pairwise_transverse _ _ (Fin.succAbove_right_injective.ne hab)
  · intro e he
    let e' : Fin 4 → Fin (n + 1) := fun k => i.succAbove (e k)
    have he' : Function.Injective e' := Fin.succAbove_right_injective.comp he
    change (⨆ k, (l (i.succAbove (e k))).submodule) = ⊤
    simpa [e'] using hl.four_spans e' he'

/-- Genericity is invariant under the symplectic action. -/
theorem IsGeneric.smul {n : ℕ} {l : ProjectiveConfig n}
    (hl : IsGeneric l) (g : SymplecticGroup) : IsGeneric (g • l) := by
  constructor
  · intro i j hij
    exact (transverse_smul_iff g (l i) (l j)).2 (hl.pairwise_transverse i j hij)
  · intro e he
    change (⨆ k, (g.1 • l (e k)).submodule) = ⊤
    simp_rw [projective_submodule_smul g.1]
    rw [← Submodule.map_iSup, hl.four_spans e he]
    rw [Submodule.map_top, LinearMap.range_eq_top]
    exact g.1.surjective

theorem generic_smul_iff {n : ℕ} (g : SymplecticGroup) (l : ProjectiveConfig n) :
    IsGeneric (g • l) ↔ IsGeneric l := by
  constructor
  · intro h
    simpa using h.smul g⁻¹
  · intro h
    exact h.smul g

/-- The fixed symplectic space has complex dimension four. -/
theorem finrank_symplecticVector : Module.finrank ℂ SymplecticVector = 4 := by
  simp [SymplecticVector]

/-- Pairings against a basis determine a vector. -/
theorem eq_of_omega_eq_on_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℂ SymplecticVector) (v w : SymplecticVector)
    (h : ∀ i, omega v (b i) = omega w (b i)) : v = w := by
  have hmaps : omega v = omega w := LinearMap.ext_on_range b.span_eq h
  apply sub_eq_zero.mp
  apply omega_nondegenerate.1 (v - w)
  intro y
  have hy := LinearMap.congr_fun hmaps y
  simpa using sub_eq_zero.mpr hy

end Sp4
