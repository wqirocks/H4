import Sp4.Symplectic.Topology
import Sp4.Symplectic.TwoFree
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Low-cardinality projective stabilizers

This file carries out the matrix calculation for the stabilizers of the
standard transverse pair and strong triple.  In the ordered symplectic basis
`(e₁,f₁,e₂,f₂)`, the pair stabilizer is the block group
`ℂˣ × SL(2,ℂ)`.  The triple stabilizer will be obtained by imposing the third
projective-line equation on this explicit parameterization.
-/

namespace Sp4
namespace ProjectiveStabilizers

noncomputable section

open scoped LinearAlgebra.Projectivization
open TwoFree

abbrev Plane := Fin 2 → ℂ
abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ

/-- Split `ℂ⁴` into the two symplectic coordinate planes. -/
def planesEquiv : SymplecticVector ≃ₗ[ℂ] Plane × Plane where
  toFun v := (![v 0, v 1], ![v 2, v 3])
  invFun p := ![p.1 0, p.1 1, p.2 0, p.2 1]
  left_inv v := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_add' v w := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_smul' c v := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

@[simp]
theorem planesEquiv_apply_snd_zero (v : SymplecticVector) :
    (planesEquiv v).2 0 = v 2 := rfl

@[simp]
theorem planesEquiv_apply_snd_one (v : SymplecticVector) :
    (planesEquiv v).2 1 = v 3 := rfl

/-- The determinant alternating form on one coordinate plane. -/
def planeOmega (v w : Plane) : ℂ := v 0 * w 1 - v 1 * w 0

theorem omega_eq_planeOmega (v w : SymplecticVector) :
    omega v w = planeOmega (planesEquiv v).1 (planesEquiv w).1 +
      planeOmega (planesEquiv v).2 (planesEquiv w).2 := by
  simp [omega_apply, planeOmega, planesEquiv]
  ring

/-- Hyperbolic scaling on the first symplectic plane. -/
def hyperbolicScale (a : ℂˣ) : Plane ≃ₗ[ℂ] Plane where
  toFun v := ![(a : ℂ) * v 0, (↑a⁻¹ : ℂ) * v 1]
  invFun v := ![(↑a⁻¹ : ℂ) * v 0, (a : ℂ) * v 1]
  left_inv v := by
    funext i
    fin_cases i <;> simp
  right_inv v := by
    funext i
    fin_cases i <;> simp
  map_add' v w := by
    funext i
    fin_cases i <;> simp [mul_add]
  map_smul' c v := by
    funext i
    fin_cases i <;> simp <;> ring

@[simp]
theorem hyperbolicScale_apply_zero (a : ℂˣ) (v : Plane) :
    hyperbolicScale a v 0 = (a : ℂ) * v 0 := rfl

@[simp]
theorem hyperbolicScale_apply_one (a : ℂˣ) (v : Plane) :
    hyperbolicScale a v 1 = (↑a⁻¹ : ℂ) * v 1 := rfl

theorem planeOmega_hyperbolicScale (a : ℂˣ) (v w : Plane) :
    planeOmega (hyperbolicScale a v) (hyperbolicScale a w) =
      planeOmega v w := by
  change
    (a.val * v 0) * (a.inv * w 1) -
        (a.inv * v 1) * (a.val * w 0) =
      v 0 * w 1 - v 1 * w 0
  calc
    _ = (a.val * a.inv) * (v 0 * w 1) -
          (a.inv * a.val) * (v 1 * w 0) := by ring
    _ = _ := by rw [a.val_inv, a.inv_val]; simp

/-- A determinant-one two-by-two matrix preserves `planeOmega`. -/
theorem planeOmega_SL2C (B : SL2C) (v w : Plane) :
    planeOmega (Matrix.SpecialLinearGroup.toLin' B v)
        (Matrix.SpecialLinearGroup.toLin' B w) = planeOmega v w := by
  have hdet : B.1 0 0 * B.1 1 1 - B.1 0 1 * B.1 1 0 = 1 := by
    have h := B.2
    rw [Matrix.det_fin_two] at h
    exact h
  simp only [planeOmega, Matrix.SpecialLinearGroup.toLin'_apply,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  change
    (B.1 0 0 * v 0 + B.1 0 1 * v 1) *
          (B.1 1 0 * w 0 + B.1 1 1 * w 1) -
        (B.1 1 0 * v 0 + B.1 1 1 * v 1) *
          (B.1 0 0 * w 0 + B.1 0 1 * w 1) =
      v 0 * w 1 - v 1 * w 0
  calc
    _ = (B.1 0 0 * B.1 1 1 - B.1 0 1 * B.1 1 0) *
          (v 0 * w 1 - v 1 * w 0) := by ring
    _ = _ := by rw [hdet, one_mul]

/-- The block-diagonal linear equivalence associated to
`(a,B) ∈ ℂˣ × SL(2,ℂ)`. -/
def pairBlockEquiv (p : ℂˣ × SL2C) :
    SymplecticVector ≃ₗ[ℂ] SymplecticVector :=
  planesEquiv |>.trans
    ((hyperbolicScale p.1).prodCongr
      (Matrix.SpecialLinearGroup.toLin' p.2)) |>.trans
    planesEquiv.symm

theorem pairBlockEquiv_preserves (p : ℂˣ × SL2C)
    (v w : SymplecticVector) :
    omega (pairBlockEquiv p v) (pairBlockEquiv p w) = omega v w := by
  rw [omega_eq_planeOmega, omega_eq_planeOmega]
  change
    planeOmega (hyperbolicScale p.1 (planesEquiv v).1)
        (hyperbolicScale p.1 (planesEquiv w).1) +
      planeOmega (Matrix.SpecialLinearGroup.toLin' p.2 (planesEquiv v).2)
        (Matrix.SpecialLinearGroup.toLin' p.2 (planesEquiv w).2) = _
  rw [planeOmega_hyperbolicScale, planeOmega_SL2C]

/-- The block element, bundled in `Sp(4,ℂ)`. -/
def pairBlock (p : ℂˣ × SL2C) : SymplecticGroup :=
  ⟨pairBlockEquiv p, pairBlockEquiv_preserves p⟩

@[simp]
theorem pairBlock_apply_zero (p : ℂˣ × SL2C) (v : SymplecticVector) :
    (pairBlock p).1 v 0 = (p.1 : ℂ) * v 0 := rfl

@[simp]
theorem pairBlock_apply_one (p : ℂˣ × SL2C) (v : SymplecticVector) :
    (pairBlock p).1 v 1 = (↑p.1⁻¹ : ℂ) * v 1 := rfl

@[simp]
theorem pairBlock_apply_two (p : ℂˣ × SL2C) (v : SymplecticVector) :
    (pairBlock p).1 v 2 = p.2 0 0 * v 2 + p.2 0 1 * v 3 := by
  simp [pairBlock, pairBlockEquiv, planesEquiv,
    Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
    dotProduct, Fin.sum_univ_two]

@[simp]
theorem pairBlock_apply_three (p : ℂˣ × SL2C) (v : SymplecticVector) :
    (pairBlock p).1 v 3 = p.2 1 0 * v 2 + p.2 1 1 * v 3 := by
  simp [pairBlock, pairBlockEquiv, planesEquiv,
    Matrix.SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply,
    dotProduct, Fin.sum_univ_two]

@[simp]
theorem pairBlock_one : pairBlock (1 : ℂˣ × SL2C) = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  funext i
  fin_cases i <;>
    simp [pairBlock_apply_zero, pairBlock_apply_one, pairBlock_apply_two,
      pairBlock_apply_three]

theorem pairBlock_mul (p q : ℂˣ × SL2C) :
    pairBlock (p * q) = pairBlock p * pairBlock q := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  funext i
  fin_cases i
  · simp [pairBlock_apply_zero]
    ring
  · simp [pairBlock_apply_one]
    ring
  · simp [pairBlock_apply_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · simp [pairBlock_apply_three, Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- The explicit block construction as a homomorphism into `Sp(4,ℂ)`. -/
def pairBlockHom : (ℂˣ × SL2C) →* SymplecticGroup where
  toFun := pairBlock
  map_one' := pairBlock_one
  map_mul' := pairBlock_mul

/-- The continuous-linear operator underlying a block element. -/
def pairBlockCLM (p : ℂˣ × SL2C) :
    SymplecticVector →L[ℂ] SymplecticVector :=
  LinearMap.toContinuousLinearMap (pairBlock p).1.toLinearMap

theorem continuous_pairBlockCLM : Continuous pairBlockCLM := by
  have hinv : Continuous (fun p : ℂˣ × SL2C => (↑p.1⁻¹ : ℂ)) :=
    Units.continuous_coe_inv.comp continuous_fst
  have hinv' : Continuous (fun p : ℂˣ × SL2C => (↑p.1 : ℂ)⁻¹) := by
    simpa only [Units.val_inv_eq_inv_val] using hinv
  let E := ContinuousLinearEquiv.piRing (𝕜 := ℂ)
    (E := SymplecticVector) (Fin 4)
  rw [E.toHomeomorph.isEmbedding.continuous_iff]
  change Continuous (fun p => E (pairBlockCLM p))
  have heq : (fun p => E (pairBlockCLM p)) =
      (fun p i => (pairBlock p).1 (Pi.single i 1)) := by
    funext p i
    exact LinearEquiv.piRing_apply ℂ (pairBlockCLM p).toLinearMap i
  rw [heq]
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [pairBlock_apply_zero, pairBlock_apply_one, pairBlock_apply_two,
      pairBlock_apply_three] <;>
    first | exact hinv' | fun_prop

/-- The explicit block homomorphism is continuous for the operator topology
on `Sp(4,ℂ)`. -/
theorem continuous_pairBlock : Continuous pairBlock := by
  rw [continuous_induced_rng]
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun p =>
      (symplecticContinuousEquiv (pairBlock p)).toContinuousLinearMap)
    have heq : (fun p =>
        (symplecticContinuousEquiv (pairBlock p)).toContinuousLinearMap) =
        pairBlockCLM := by
      funext p
      apply ContinuousLinearMap.ext
      intro v
      rfl
    rw [heq]
    exact continuous_pairBlockCLM
  · have heq :
        (fun p : ℂˣ × SL2C =>
          (↑(symplecticOperatorUnit (pairBlock p))⁻¹ :
            SymplecticVector →L[ℂ] SymplecticVector)) =
        (fun p => pairBlockCLM p⁻¹) := by
      funext p
      rw [show (symplecticOperatorUnit (pairBlock p))⁻¹ =
          symplecticOperatorUnit (pairBlock p⁻¹) by
        exact (symplecticOperatorHom.map_inv (pairBlock p)).symm.trans
          (congrArg symplecticOperatorUnit (pairBlockHom.map_inv p).symm)]
      apply ContinuousLinearMap.ext
      intro v
      rfl
    change Continuous (fun p : ℂˣ × SL2C =>
      (↑(symplecticOperatorUnit (pairBlock p))⁻¹ :
        SymplecticVector →L[ℂ] SymplecticVector))
    rw [heq]
    exact continuous_pairBlockCLM.comp continuous_inv

/-- Every matrix coefficient of a symplectic transformation varies
continuously in the chosen operator topology. -/
theorem continuous_symplectic_coordinate (v : SymplecticVector) (i : Fin 4) :
    Continuous (fun g : SymplecticGroup => g.1 v i) := by
  change Continuous (fun g : SymplecticGroup =>
    ((symplecticOperatorUnit g :
      SymplecticVector →L[ℂ] SymplecticVector) v) i)
  have hop : Continuous symplecticOperatorUnit := continuous_induced_dom
  have hval : Continuous (fun g : SymplecticGroup =>
      (symplecticOperatorUnit g :
        SymplecticVector →L[ℂ] SymplecticVector)) :=
    Units.continuous_val.comp hop
  exact (continuous_apply i).comp
    ((ContinuousLinearMap.apply ℂ SymplecticVector v).continuous.comp hval)

/-- The ordered transverse pair whose stabilizer is computed below. -/
def standardPair : ProjectiveConfig 2 :=
  ![Projectivization.mk ℂ e1 e1_ne_zero,
    Projectivization.mk ℂ f1 f1_ne_zero]

/-- The projective stabilizer of the standard ordered transverse pair. -/
abbrev PairStabilizer := MulAction.stabilizer SymplecticGroup standardPair

theorem pairBlock_smul_standardPair (p : ℂˣ × SL2C) :
    pairBlock p • standardPair = standardPair := by
  funext i
  fin_cases i
  · change (pairBlock p).1 • Projectivization.mk ℂ e1 e1_ne_zero =
      Projectivization.mk ℂ e1 e1_ne_zero
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨(p.1 : ℂ), ?_⟩
    funext j
    fin_cases j <;> simp [e1, pairBlock_apply_zero, pairBlock_apply_one,
      pairBlock_apply_two, pairBlock_apply_three]
  · change (pairBlock p).1 • Projectivization.mk ℂ f1 f1_ne_zero =
      Projectivization.mk ℂ f1 f1_ne_zero
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨(↑p.1⁻¹ : ℂ), ?_⟩
    funext j
    fin_cases j <;> simp [f1, pairBlock_apply_zero, pairBlock_apply_one,
      pairBlock_apply_two, pairBlock_apply_three]

/-- The block homomorphism, with its image restricted to the pair
stabilizer. -/
def pairStabilizerHom : (ℂˣ × SL2C) →* PairStabilizer where
  toFun p := ⟨pairBlock p, pairBlock_smul_standardPair p⟩
  map_one' := by
    apply Subtype.ext
    exact pairBlock_one
  map_mul' p q := by
    apply Subtype.ext
    exact pairBlock_mul p q

theorem pairBlockHom_injective : Function.Injective pairBlockHom := by
  intro p q hpq
  apply Prod.ext
  · apply Units.ext
    have h := congrArg
      (fun g : SymplecticGroup => g.1 e1 0) hpq
    simpa [pairBlockHom, e1, pairBlock_apply_zero] using h
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j
    · have h := congrArg
        (fun g : SymplecticGroup => g.1 (Pi.single (2 : Fin 4) 1) 2) hpq
      simpa [pairBlockHom, pairBlock_apply_two] using h
    · have h := congrArg
        (fun g : SymplecticGroup => g.1 (Pi.single (3 : Fin 4) 1) 2) hpq
      simpa [pairBlockHom, pairBlock_apply_two] using h
    · have h := congrArg
        (fun g : SymplecticGroup => g.1 (Pi.single (2 : Fin 4) 1) 3) hpq
      simpa [pairBlockHom, pairBlock_apply_three] using h
    · have h := congrArg
        (fun g : SymplecticGroup => g.1 (Pi.single (3 : Fin 4) 1) 3) hpq
      simpa [pairBlockHom, pairBlock_apply_three] using h

theorem pairStabilizerHom_injective :
    Function.Injective pairStabilizerHom := by
  intro p q h
  apply pairBlockHom_injective
  exact congrArg Subtype.val h

/-- The remaining two vectors of the ordered symplectic coordinate basis. -/
def e2 : SymplecticVector := ![0, 0, 1, 0]

theorem e2_ne_zero : e2 ≠ 0 := by
  intro h
  have h2 := congrFun h (2 : Fin 4)
  simpa [e2] using h2

/-- A linear map on `ℂ⁴` is determined by the ordered coordinate basis. -/
theorem linearEquiv_eq_of_basis
    {g h : SymplecticVector ≃ₗ[ℂ] SymplecticVector}
    (h0 : g e1 = h e1) (h1 : g f1 = h f1)
    (h2 : g e2 = h e2) (h3 : g f2 = h f2) : g = h := by
  apply LinearEquiv.ext
  intro v
  have hv : v = v 0 • e1 + v 1 • f1 + v 2 • e2 + v 3 • f2 := by
    funext i
    fin_cases i <;> simp [e1, f1, e2, f2]
  rw [hv]
  simp only [map_add, map_smul]
  rw [h0, h1, h2, h3]

/-- Projective fixation of the standard pair supplies nonzero scalar
eigenvalues whose product is one. -/
theorem pairStabilizer_scalars (g : PairStabilizer) :
    ∃ a b : ℂ, a ≠ 0 ∧ b ≠ 0 ∧
      a • e1 = g.1.1 e1 ∧ b • f1 = g.1.1 f1 ∧ a * b = 1 := by
  have h0 := congrFun g.2 (0 : Fin 2)
  have h1 := congrFun g.2 (1 : Fin 2)
  change g.1.1 • Projectivization.mk ℂ e1 e1_ne_zero =
    Projectivization.mk ℂ e1 e1_ne_zero at h0
  change g.1.1 • Projectivization.mk ℂ f1 f1_ne_zero =
    Projectivization.mk ℂ f1 f1_ne_zero at h1
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at h0 h1
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  have ha' : a • e1 = g.1.1 e1 := by
    simpa [LinearEquiv.smul_def] using ha
  have hb' : b • f1 = g.1.1 f1 := by
    simpa [LinearEquiv.smul_def] using hb
  have ha0 : a ≠ 0 := by
    intro ha0
    apply e1_ne_zero
    apply g.1.1.injective
    rw [← ha', ha0, zero_smul, map_zero]
  have hb0 : b ≠ 0 := by
    intro hb0
    apply f1_ne_zero
    apply g.1.1.injective
    rw [← hb', hb0, zero_smul, map_zero]
  have hab : a * b = 1 := by
    have hp := g.1.2 e1 f1
    rw [← ha', ← hb'] at hp
    simpa [omega_apply, e1, f1] using hp
  exact ⟨a, b, ha0, hb0, ha', hb', hab⟩

/-- A pair stabilizer preserves the second symplectic coordinate plane. -/
theorem pairStabilizer_lower_coordinates (g : PairStabilizer)
    {a b : ℂ} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : a • e1 = g.1.1 e1) (hb : b • f1 = g.1.1 f1) :
    g.1.1 e2 0 = 0 ∧ g.1.1 e2 1 = 0 ∧
      g.1.1 f2 0 = 0 ∧ g.1.1 f2 1 = 0 := by
  have he2one : g.1.1 e2 1 = 0 := by
    have hp := g.1.2 e1 e2
    rw [← ha] at hp
    have hz : a * g.1.1 e2 1 = 0 := by
      simpa [omega_apply, e1, e2] using hp
    exact (mul_eq_zero.mp hz).resolve_left ha0
  have he2zero : g.1.1 e2 0 = 0 := by
    have hp := g.1.2 f1 e2
    rw [← hb] at hp
    have hz : b * g.1.1 e2 0 = 0 := by
      simpa [omega_apply, f1, e2] using hp
    exact (mul_eq_zero.mp hz).resolve_left hb0
  have hf2one : g.1.1 f2 1 = 0 := by
    have hp := g.1.2 e1 f2
    rw [← ha] at hp
    have hz : a * g.1.1 f2 1 = 0 := by
      simpa [omega_apply, e1, f2] using hp
    exact (mul_eq_zero.mp hz).resolve_left ha0
  have hf2zero : g.1.1 f2 0 = 0 := by
    have hp := g.1.2 f1 f2
    rw [← hb] at hp
    have hz : b * g.1.1 f2 0 = 0 := by
      simpa [omega_apply, f1, f2] using hp
    exact (mul_eq_zero.mp hz).resolve_left hb0
  exact ⟨he2zero, he2one, hf2zero, hf2one⟩

/-- The lower-right two-by-two matrix of a symplectic transformation.  Its
columns are the lower coordinates of the images of `e₂` and `f₂`. -/
def lowerBlockMatrix (g : SymplecticGroup) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![g.1 e2 2, g.1 f2 2;
     g.1 e2 3, g.1 f2 3]

theorem pairStabilizer_lowerBlock_det (g : PairStabilizer) :
    (lowerBlockMatrix g.1).det = 1 := by
  obtain ⟨a, b, ha0, hb0, ha, hb, _⟩ := pairStabilizer_scalars g
  obtain ⟨he20, he21, hf20, hf21⟩ :=
    pairStabilizer_lower_coordinates g ha0 hb0 ha hb
  have hp := g.1.2 e2 f2
  rw [omega_apply, he20, he21, hf20, hf21] at hp
  simp only [zero_mul, sub_zero, zero_add] at hp
  rw [Matrix.det_fin_two]
  change
    g.1.1 e2 2 * g.1.1 f2 3 - g.1.1 f2 2 * g.1.1 e2 3 = 1
  calc
    _ = g.1.1 e2 2 * g.1.1 f2 3 -
        g.1.1 e2 3 * g.1.1 f2 2 := by ring
    _ = 1 := by simpa [omega_apply, e2, f2] using hp

/-- The determinant-one lower block extracted from a pair stabilizer. -/
def lowerBlock (g : PairStabilizer) : SL2C :=
  ⟨lowerBlockMatrix g.1, pairStabilizer_lowerBlock_det g⟩

theorem pairStabilizerHom_surjective :
    Function.Surjective pairStabilizerHom := by
  intro g
  obtain ⟨a, b, ha0, hb0, ha, hb, hab⟩ := pairStabilizer_scalars g
  obtain ⟨he20, he21, hf20, hf21⟩ :=
    pairStabilizer_lower_coordinates g ha0 hb0 ha hb
  let ua : ℂˣ := Units.mk0 a ha0
  let B : SL2C := lowerBlock g
  let p : ℂˣ × SL2C := (ua, B)
  have hb_inv : b = (↑ua⁻¹ : ℂ) := by
    apply Units.eq_inv_of_mul_eq_one_left
    exact hab
  have hE1 : g.1.1 e1 = (pairBlock p).1 e1 := by
    rw [← ha]
    funext i
    fin_cases i <;>
      simp [p, ua, e1, pairBlock_apply_zero, pairBlock_apply_one,
        pairBlock_apply_two, pairBlock_apply_three]
  have hF1 : g.1.1 f1 = (pairBlock p).1 f1 := by
    rw [← hb, hb_inv]
    funext i
    fin_cases i <;>
      simp [p, f1, pairBlock_apply_zero, pairBlock_apply_one,
        pairBlock_apply_two, pairBlock_apply_three]
  have hE2 : g.1.1 e2 = (pairBlock p).1 e2 := by
    funext i
    fin_cases i
    · simpa [e2, pairBlock_apply_zero] using he20
    · simpa [e2, pairBlock_apply_one] using he21
    · simp [p, B, lowerBlock, lowerBlockMatrix, e2, pairBlock_apply_two]
    · simp [p, B, lowerBlock, lowerBlockMatrix, e2, pairBlock_apply_three]
  have hF2 : g.1.1 f2 = (pairBlock p).1 f2 := by
    funext i
    fin_cases i
    · simpa [f2, pairBlock_apply_zero] using hf20
    · simpa [f2, pairBlock_apply_one] using hf21
    · simp [p, B, lowerBlock, lowerBlockMatrix, f2, pairBlock_apply_two]
    · simp [p, B, lowerBlock, lowerBlockMatrix, f2, pairBlock_apply_three]
  refine ⟨p, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact (linearEquiv_eq_of_basis hE1 hF1 hE2 hF2).symm

/-- Algebraic identification of the standard pair stabilizer. -/
noncomputable def pairStabilizerEquiv :
    (ℂˣ × SL2C) ≃* PairStabilizer :=
  MulEquiv.ofBijective pairStabilizerHom
    ⟨pairStabilizerHom_injective, pairStabilizerHom_surjective⟩

/-- The two diagonal matrix coefficients of a pair stabilizer multiply to
one. -/
theorem pairStabilizer_diagonal_product (g : PairStabilizer) :
    g.1.1 e1 0 * g.1.1 f1 1 = 1 := by
  obtain ⟨a, b, _, _, ha, hb, hab⟩ := pairStabilizer_scalars g
  have haCoord : g.1.1 e1 0 = a := by
    rw [← ha]
    simp [e1]
  have hbCoord : g.1.1 f1 1 = b := by
    rw [← hb]
    simp [f1]
  rw [haCoord, hbCoord, hab]

/-- Recover the first hyperbolic scaling parameter directly from two matrix
coefficients. -/
def pairFirstUnit (g : PairStabilizer) : ℂˣ where
  val := g.1.1 e1 0
  inv := g.1.1 f1 1
  val_inv := pairStabilizer_diagonal_product g
  inv_val := by
    rw [mul_comm]
    exact pairStabilizer_diagonal_product g

/-- The coordinate inverse of the block parameterization. -/
def pairCoordinates (g : PairStabilizer) : ℂˣ × SL2C :=
  (pairFirstUnit g, lowerBlock g)

@[simp]
theorem pairFirstUnit_pairStabilizerHom (p : ℂˣ × SL2C) :
    pairFirstUnit (pairStabilizerHom p) = p.1 := by
  apply Units.ext
  simp [pairFirstUnit, pairStabilizerHom, e1, pairBlock_apply_zero]

@[simp]
theorem lowerBlock_pairStabilizerHom (p : ℂˣ × SL2C) :
    lowerBlock (pairStabilizerHom p) = p.2 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerBlock, lowerBlockMatrix, pairStabilizerHom, e2, f2,
      pairBlock_apply_two, pairBlock_apply_three]

theorem pairCoordinates_leftInverse :
    Function.LeftInverse pairCoordinates pairStabilizerHom := by
  intro p
  apply Prod.ext <;> simp [pairCoordinates]

theorem pairCoordinates_rightInverse :
    Function.RightInverse pairCoordinates pairStabilizerHom := by
  intro g
  obtain ⟨p, rfl⟩ := pairStabilizerHom_surjective g
  exact congrArg pairStabilizerHom (pairCoordinates_leftInverse p)

/-- The algebraic isomorphism with an explicit coordinate inverse. -/
def pairStabilizerExplicitEquiv :
    (ℂˣ × SL2C) ≃* PairStabilizer where
  toFun := pairStabilizerHom
  invFun := pairCoordinates
  left_inv := pairCoordinates_leftInverse
  right_inv := pairCoordinates_rightInverse
  map_mul' := pairStabilizerHom.map_mul

theorem continuous_pairStabilizerHom : Continuous pairStabilizerHom :=
  continuous_induced_rng.mpr continuous_pairBlock

theorem continuous_pairFirstUnit : Continuous pairFirstUnit := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun g : PairStabilizer => g.1.1 e1 0)
    exact (continuous_symplectic_coordinate e1 0).comp continuous_subtype_val
  · change Continuous (fun g : PairStabilizer => g.1.1 f1 1)
    exact (continuous_symplectic_coordinate f1 1).comp continuous_subtype_val

theorem continuous_lowerBlock : Continuous lowerBlock := by
  apply continuous_induced_rng.mpr
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [lowerBlock, lowerBlockMatrix, Matrix.cons_val_zero,
      Matrix.cons_val_one]
  · exact (continuous_symplectic_coordinate e2 2).comp continuous_subtype_val
  · exact (continuous_symplectic_coordinate f2 2).comp continuous_subtype_val
  · exact (continuous_symplectic_coordinate e2 3).comp continuous_subtype_val
  · exact (continuous_symplectic_coordinate f2 3).comp continuous_subtype_val

theorem continuous_pairCoordinates : Continuous pairCoordinates :=
  continuous_pairFirstUnit.prodMk continuous_lowerBlock

/-- The required topological group isomorphism for the pair stabilizer. -/
def pairStabilizerContinuousEquiv :
    (ℂˣ × SL2C) ≃ₜ* PairStabilizer :=
  { pairStabilizerExplicitEquiv with
    continuous_toFun := continuous_pairStabilizerHom
    continuous_invFun := continuous_pairCoordinates }

/-! ## The strong-triple stabilizer -/

/-- The two-element subgroup of complex units characterized intrinsically by
`ε² = 1`.  Over `ℂ` these are exactly `±1`. -/
def ComplexSign : Subgroup ℂˣ where
  carrier := {ε | ε ^ 2 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro ε δ hε hδ
    change (ε * δ) ^ 2 = 1
    rw [mul_pow, hε, hδ, one_mul]
  inv_mem' := by
    intro ε hε
    change ε⁻¹ ^ 2 = 1
    rw [inv_pow, hε, inv_one]

theorem complexSign_eq_one_or_neg_one (ε : ComplexSign) :
    ε.1 = 1 ∨ ε.1 = -1 := by
  have hpow : ε.1 ^ 2 = (1 : ℂˣ) := ε.2
  have hmul : ε.1 * ε.1 = (1 : ℂˣ) := by
    simpa only [pow_two] using hpow
  have hval := congrArg (fun u : ℂˣ => (u : ℂ)) hmul
  change (ε.1 : ℂ) * (ε.1 : ℂ) = 1 at hval
  rcases mul_self_eq_one_iff.mp hval with h | h
  · left
    exact Units.ext h
  · right
    apply Units.ext
    simpa using h

/-- The `SL(2,ℂ)` block
`ε [[1,t],[0,1]]` occurring in the triple stabilizer. -/
def tripleSLBlock (s : ComplexSign × Multiplicative ℂ) : SL2C := by
  let ε : ℂ := (s.1.1 : ℂ)
  let t : ℂ := s.2.toAdd
  refine ⟨!![ε, ε * t; 0, ε], ?_⟩
  have hεunits : s.1.1 ^ 2 = (1 : ℂˣ) := s.1.2
  have hε : ε ^ 2 = (1 : ℂ) := by
    exact congrArg (fun u : ℂˣ => (u : ℂ)) hεunits
  rw [Matrix.det_fin_two]
  simpa [ε, t, pow_two] using hε

/-- Embed sign/additive parameters into the pair-stabilizer parameters. -/
def triplePair (s : ComplexSign × Multiplicative ℂ) : ℂˣ × SL2C :=
  (s.1.1, tripleSLBlock s)

@[simp]
theorem triplePair_one :
    triplePair (1 : ComplexSign × Multiplicative ℂ) = 1 := by
  apply Prod.ext
  · rfl
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [triplePair, tripleSLBlock]

theorem triplePair_mul (s r : ComplexSign × Multiplicative ℂ) :
    triplePair (s * r) = triplePair s * triplePair r := by
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change (tripleSLBlock (s * r)).1 =
      (tripleSLBlock s).1 * (tripleSLBlock r).1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [tripleSLBlock, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring

/-- The sign/additive parameter group as a homomorphism into the pair
parameters. -/
def triplePairHom :
    (ComplexSign × Multiplicative ℂ) →* (ℂˣ × SL2C) where
  toFun := triplePair
  map_one' := triplePair_one
  map_mul' := triplePair_mul

/-- The corresponding symplectic block homomorphism. -/
def tripleBlockHom :
    (ComplexSign × Multiplicative ℂ) →* SymplecticGroup :=
  pairBlockHom.comp triplePairHom

theorem tripleBlock_smul_standardTriple
    (s : ComplexSign × Multiplicative ℂ) :
    tripleBlockHom s • standardTriple = standardTriple := by
  have hε2 : s.1.1 * s.1.1 = (1 : ℂˣ) := by
    have hpow : s.1.1 ^ 2 = (1 : ℂˣ) := s.1.2
    rw [pow_two] at hpow
    exact hpow
  have hεinv : s.1.1⁻¹ = s.1.1 :=
    inv_eq_of_mul_eq_one_right hε2
  have hεinvval : (↑s.1.1⁻¹ : ℂ) = (s.1.1 : ℂ) :=
    congrArg (fun u : ℂˣ => (u : ℂ)) hεinv
  funext i
  fin_cases i
  · exact congrFun (pairBlock_smul_standardPair (triplePair s)) 0
  · exact congrFun (pairBlock_smul_standardPair (triplePair s)) 1
  · change (pairBlock (triplePair s)).1 •
        Projectivization.mk ℂ e1_add_f1_add_e2
          e1_add_f1_add_e2_ne_zero =
      Projectivization.mk ℂ e1_add_f1_add_e2
        e1_add_f1_add_e2_ne_zero
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨(s.1.1 : ℂ), ?_⟩
    funext j
    fin_cases j <;>
      simp [triplePair, tripleSLBlock, e1_add_f1_add_e2,
        pairBlock_apply_zero, pairBlock_apply_one, pairBlock_apply_two,
        pairBlock_apply_three, hεinvval]

/-- The projective stabilizer of the standard strong ordered triple. -/
abbrev TripleStabilizer :=
  MulAction.stabilizer SymplecticGroup standardTriple

/-- The explicit sign/additive block map into the triple stabilizer. -/
def tripleStabilizerHom :
    (ComplexSign × Multiplicative ℂ) →* TripleStabilizer where
  toFun s := ⟨tripleBlockHom s, tripleBlock_smul_standardTriple s⟩
  map_one' := by
    apply Subtype.ext
    exact tripleBlockHom.map_one
  map_mul' s r := by
    apply Subtype.ext
    exact tripleBlockHom.map_mul s r

theorem triplePair_injective : Function.Injective triplePair := by
  intro s r h
  have hε : s.1.1 = r.1.1 := congrArg Prod.fst h
  apply Prod.ext
  · exact Subtype.ext hε
  · apply Multiplicative.ext
    have ht := congrArg (fun p : ℂˣ × SL2C => p.2 0 1) h
    simp only [triplePair, tripleSLBlock] at ht
    rw [hε] at ht
    exact mul_left_cancel₀ (Units.ne_zero r.1.1) ht

theorem tripleStabilizerHom_injective :
    Function.Injective tripleStabilizerHom := by
  intro s r h
  apply triplePair_injective
  apply pairBlockHom_injective
  exact congrArg Subtype.val h

/-- Forgetting the third fixed line sends the triple stabilizer into the pair
stabilizer. -/
def tripleToPair (g : TripleStabilizer) : PairStabilizer := by
  refine ⟨g.1, ?_⟩
  funext i
  fin_cases i
  · exact congrFun g.2 0
  · exact congrFun g.2 1

/-- The forgetful map on stabilizers is a group homomorphism. -/
def tripleToPairHom : TripleStabilizer →* PairStabilizer where
  toFun := tripleToPair
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' g h := by
    apply Subtype.ext
    rfl

/-- Solving the third-line equation inside the explicit pair block gives
exactly a sign and one additive complex parameter. -/
theorem triplePair_exists_of_fixes_third
    (p : ℂˣ × SL2C)
    (hfix : pairBlock p •
        Projectivization.mk ℂ e1_add_f1_add_e2
          e1_add_f1_add_e2_ne_zero =
      Projectivization.mk ℂ e1_add_f1_add_e2
        e1_add_f1_add_e2_ne_zero) :
    ∃ s : ComplexSign × Multiplicative ℂ, triplePair s = p := by
  change (pairBlock p).1 •
      Projectivization.mk ℂ e1_add_f1_add_e2
        e1_add_f1_add_e2_ne_zero = _ at hfix
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at hfix
  obtain ⟨c, hc⟩ := hfix
  have hc' : c • e1_add_f1_add_e2 =
      (pairBlock p).1 e1_add_f1_add_e2 := by
    simpa [LinearEquiv.smul_def] using hc
  have h0 := congrFun hc' (0 : Fin 4)
  have h1 := congrFun hc' (1 : Fin 4)
  have h2 := congrFun hc' (2 : Fin 4)
  have h3 := congrFun hc' (3 : Fin 4)
  simp [e1_add_f1_add_e2, pairBlock_apply_zero,
    pairBlock_apply_one, pairBlock_apply_two, pairBlock_apply_three]
    at h0 h1 h2 h3
  have hau : p.1 = p.1⁻¹ := by
    apply Units.ext
    simpa using h0.symm.trans h1
  have hauMul : p.1 * p.1 = (1 : ℂˣ) := by
    calc
      p.1 * p.1 = p.1 * p.1⁻¹ := congrArg (fun u : ℂˣ => p.1 * u) hau
      _ = 1 := mul_inv_cancel p.1
  have hauSq : p.1 ^ 2 = (1 : ℂˣ) := by
    simpa only [pow_two] using hauMul
  let ε : ComplexSign := ⟨p.1, hauSq⟩
  have hB00 : p.2 0 0 = (p.1 : ℂ) := h2.symm.trans h0
  have hB10 : p.2 1 0 = 0 := h3.symm
  have hdet : p.2 0 0 * p.2 1 1 - p.2 0 1 * p.2 1 0 = 1 := by
    have hd := p.2.2
    rw [Matrix.det_fin_two] at hd
    exact hd
  have hprod : (p.1 : ℂ) * p.2 1 1 = 1 := by
    rw [hB00, hB10, mul_zero, sub_zero] at hdet
    exact hdet
  have hB11inv : p.2 1 1 = (↑p.1⁻¹ : ℂ) :=
    Units.eq_inv_of_mul_eq_one_left hprod
  have hauval : (↑p.1⁻¹ : ℂ) = (p.1 : ℂ) :=
    congrArg (fun u : ℂˣ => (u : ℂ)) hau.symm
  have hB11 : p.2 1 1 = (p.1 : ℂ) := hB11inv.trans hauval
  have hauMulVal : (p.1 : ℂ) * (p.1 : ℂ) = 1 :=
    congrArg (fun u : ℂˣ => (u : ℂ)) hauMul
  let t : ℂ := (p.1 : ℂ) * p.2 0 1
  have hB01 : (p.1 : ℂ) * t = p.2 0 1 := by
    calc
      (p.1 : ℂ) * t =
          ((p.1 : ℂ) * (p.1 : ℂ)) * p.2 0 1 := by ring
      _ = p.2 0 1 := by rw [hauMulVal, one_mul]
  let s : ComplexSign × Multiplicative ℂ := (ε, Multiplicative.ofAdd t)
  refine ⟨s, ?_⟩
  apply Prod.ext
  · rfl
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [s, ε, triplePair, tripleSLBlock] using hB00.symm
    · simpa [s, ε, t, triplePair, tripleSLBlock] using hB01
    · simpa [s, ε, triplePair, tripleSLBlock] using hB10.symm
    · simpa [s, ε, triplePair, tripleSLBlock] using hB11.symm

theorem tripleStabilizerHom_surjective :
    Function.Surjective tripleStabilizerHom := by
  intro g
  obtain ⟨p, hp⟩ := pairStabilizerHom_surjective (tripleToPair g)
  have hpg : pairBlock p = g.1 := congrArg Subtype.val hp
  have hfix : pairBlock p •
        Projectivization.mk ℂ e1_add_f1_add_e2
          e1_add_f1_add_e2_ne_zero =
      Projectivization.mk ℂ e1_add_f1_add_e2
        e1_add_f1_add_e2_ne_zero := by
    rw [hpg]
    exact congrFun g.2 2
  obtain ⟨s, hs⟩ := triplePair_exists_of_fixes_third p hfix
  refine ⟨s, ?_⟩
  apply Subtype.ext
  change pairBlock (triplePair s) = g.1
  rw [hs, hpg]

/-- Algebraic identification of the standard strong-triple stabilizer. -/
noncomputable def tripleStabilizerEquiv :
    (ComplexSign × Multiplicative ℂ) ≃* TripleStabilizer :=
  MulEquiv.ofBijective tripleStabilizerHom
    ⟨tripleStabilizerHom_injective, tripleStabilizerHom_surjective⟩

theorem continuous_tripleSLBlock : Continuous tripleSLBlock := by
  apply continuous_induced_rng.mpr
  change Continuous (fun s : ComplexSign × Multiplicative ℂ =>
    (!![(s.1.1 : ℂ), (s.1.1 : ℂ) * s.2.toAdd;
       0, (s.1.1 : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ))
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_triplePair : Continuous triplePair :=
  (continuous_subtype_val.comp continuous_fst).prodMk continuous_tripleSLBlock

theorem continuous_tripleStabilizerHom : Continuous tripleStabilizerHom :=
  continuous_induced_rng.mpr
    (continuous_pairBlock.comp continuous_triplePair)

theorem continuous_tripleToPair : Continuous tripleToPair :=
  continuous_induced_rng.mpr continuous_subtype_val

/-- The scaling coordinate read from a triple stabilizer again squares to
one. -/
theorem tripleCoordinate_sq (g : TripleStabilizer) :
    (pairCoordinates (tripleToPair g)).1 ^ 2 = (1 : ℂˣ) := by
  let p := pairCoordinates (tripleToPair g)
  have hpg : pairBlock p = g.1 := by
    exact congrArg Subtype.val
      (pairCoordinates_rightInverse (tripleToPair g))
  have hfix : pairBlock p •
        Projectivization.mk ℂ e1_add_f1_add_e2
          e1_add_f1_add_e2_ne_zero =
      Projectivization.mk ℂ e1_add_f1_add_e2
        e1_add_f1_add_e2_ne_zero := by
    rw [hpg]
    exact congrFun g.2 2
  obtain ⟨s, hs⟩ := triplePair_exists_of_fixes_third p hfix
  have hfirst : s.1.1 = p.1 := congrArg Prod.fst hs
  have hsquare : s.1.1 ^ 2 = (1 : ℂˣ) := s.1.2
  simpa only [p, hfirst] using hsquare

/-- The sign coordinate recovered from a triple stabilizer. -/
def tripleSignCoordinate (g : TripleStabilizer) : ComplexSign :=
  ⟨(pairCoordinates (tripleToPair g)).1, tripleCoordinate_sq g⟩

/-- The additive coordinate recovered from the upper-right entry of the
lower block. -/
def tripleAddCoordinate (g : TripleStabilizer) : ℂ :=
  ((pairCoordinates (tripleToPair g)).1 : ℂ) *
    (pairCoordinates (tripleToPair g)).2 0 1

/-- The explicit coordinate inverse for the triple block map. -/
def tripleCoordinates (g : TripleStabilizer) :
    ComplexSign × Multiplicative ℂ :=
  (tripleSignCoordinate g, Multiplicative.ofAdd (tripleAddCoordinate g))

theorem tripleCoordinates_leftInverse :
    Function.LeftInverse tripleCoordinates tripleStabilizerHom := by
  intro s
  have hp : pairCoordinates
      (tripleToPair (tripleStabilizerHom s)) = triplePair s := by
    change pairCoordinates (pairStabilizerHom (triplePair s)) = triplePair s
    exact pairCoordinates_leftInverse (triplePair s)
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst hp
  · apply Multiplicative.ext
    simp only [tripleCoordinates, tripleAddCoordinate,
      toAdd_ofAdd]
    rw [hp]
    change (s.1.1 : ℂ) * tripleSLBlock s 0 1 = s.2.toAdd
    change (s.1.1 : ℂ) * ((s.1.1 : ℂ) * s.2.toAdd) = s.2.toAdd
    have hpow : s.1.1 ^ 2 = (1 : ℂˣ) := s.1.2
    have hmulUnits : s.1.1 * s.1.1 = (1 : ℂˣ) := by
      simpa only [pow_two] using hpow
    have hmul : (s.1.1 : ℂ) * (s.1.1 : ℂ) = 1 :=
      congrArg (fun u : ℂˣ => (u : ℂ)) hmulUnits
    calc
      _ = ((s.1.1 : ℂ) * (s.1.1 : ℂ)) * s.2.toAdd := by ring
      _ = s.2.toAdd := by rw [hmul, one_mul]

theorem tripleCoordinates_rightInverse :
    Function.RightInverse tripleCoordinates tripleStabilizerHom := by
  intro g
  obtain ⟨s, rfl⟩ := tripleStabilizerHom_surjective g
  exact congrArg tripleStabilizerHom (tripleCoordinates_leftInverse s)

/-- Algebraic triple-stabilizer isomorphism with the explicit inverse. -/
def tripleStabilizerExplicitEquiv :
    (ComplexSign × Multiplicative ℂ) ≃* TripleStabilizer where
  toFun := tripleStabilizerHom
  invFun := tripleCoordinates
  left_inv := tripleCoordinates_leftInverse
  right_inv := tripleCoordinates_rightInverse
  map_mul' := tripleStabilizerHom.map_mul

theorem continuous_tripleSignCoordinate : Continuous tripleSignCoordinate := by
  apply continuous_induced_rng.mpr
  change Continuous (fun g : TripleStabilizer =>
    (pairCoordinates (tripleToPair g)).1)
  exact continuous_fst.comp
    (continuous_pairCoordinates.comp continuous_tripleToPair)

theorem continuous_tripleAddCoordinate : Continuous tripleAddCoordinate := by
  have hp : Continuous (fun g : TripleStabilizer =>
      pairCoordinates (tripleToPair g)) :=
    continuous_pairCoordinates.comp continuous_tripleToPair
  have hu : Continuous (fun g : TripleStabilizer =>
      ((pairCoordinates (tripleToPair g)).1 : ℂ)) :=
    Units.continuous_val.comp (continuous_fst.comp hp)
  have hB : Continuous (fun g : TripleStabilizer =>
      ((pairCoordinates (tripleToPair g)).2 :
        Matrix (Fin 2) (Fin 2) ℂ)) :=
    continuous_subtype_val.comp (continuous_snd.comp hp)
  have hB01 : Continuous (fun g : TripleStabilizer =>
      (pairCoordinates (tripleToPair g)).2 0 1) :=
    (continuous_apply 1).comp ((continuous_apply 0).comp hB)
  exact hu.mul hB01

theorem continuous_tripleCoordinates : Continuous tripleCoordinates :=
  continuous_tripleSignCoordinate.prodMk
    (continuous_ofAdd.comp continuous_tripleAddCoordinate)

/-- The required topological group isomorphism for the strong-triple
stabilizer. -/
def tripleStabilizerContinuousEquiv :
    (ComplexSign × Multiplicative ℂ) ≃ₜ* TripleStabilizer :=
  { tripleStabilizerExplicitEquiv with
    continuous_toFun := continuous_tripleStabilizerHom
    continuous_invFun := continuous_tripleCoordinates }

/-! ## The three degree-one face coordinates -/

/-- The first split coordinate of a triple stabilizer.  This is the sign
`ε` in the article's presentation `H ≅ {±1} × (ℂ,+)`. -/
def tripleSplitUnit (g : TripleStabilizer) : ℂˣ :=
  (tripleSignCoordinate g).1

/-- For deletion of the first line, the first remaining line is `[f₁]`,
so its eigenvalue is `ε⁻¹`; for the other two deletions the first
remaining line is `[e₁]`, so its eigenvalue is `ε`.  This intrinsic
definition is independent of any choice of transporter to the standard
ordered pair. -/
def tripleFaceUnit (i : Fin 3) (g : TripleStabilizer) : ℂˣ :=
  if i = 0 then (tripleSplitUnit g)⁻¹ else tripleSplitUnit g

@[simp]
theorem tripleFaceUnit_zero (g : TripleStabilizer) :
    tripleFaceUnit 0 g = (tripleSplitUnit g)⁻¹ := by
  simp [tripleFaceUnit]

@[simp]
theorem tripleFaceUnit_one (g : TripleStabilizer) :
    tripleFaceUnit 1 g = tripleSplitUnit g := by
  simp [tripleFaceUnit]

@[simp]
theorem tripleFaceUnit_two (g : TripleStabilizer) :
    tripleFaceUnit 2 g = tripleSplitUnit g := by
  simp [tripleFaceUnit]

/-- The split coordinate acts on `e₁` by its defining scalar. -/
theorem triple_apply_e1 (g : TripleStabilizer) :
    g.1.1 e1 = (tripleSplitUnit g : ℂ) • e1 := by
  let p := pairCoordinates (tripleToPair g)
  have hpg : pairBlock p = g.1 :=
    congrArg Subtype.val (pairCoordinates_rightInverse (tripleToPair g))
  rw [← hpg]
  funext j
  fin_cases j <;>
    simp [p, tripleSplitUnit, tripleSignCoordinate, pairCoordinates, e1,
      pairBlock_apply_zero, pairBlock_apply_one, pairBlock_apply_two,
      pairBlock_apply_three]

/-- The split coordinate acts on `f₁` by its inverse. -/
theorem triple_apply_f1 (g : TripleStabilizer) :
    g.1.1 f1 = ((tripleSplitUnit g)⁻¹ : ℂ) • f1 := by
  let p := pairCoordinates (tripleToPair g)
  have hpg : pairBlock p = g.1 :=
    congrArg Subtype.val (pairCoordinates_rightInverse (tripleToPair g))
  rw [← hpg]
  funext j
  fin_cases j <;>
    simp [p, tripleSplitUnit, tripleSignCoordinate, pairCoordinates, f1,
      pairBlock_apply_zero, pairBlock_apply_one, pairBlock_apply_two,
      pairBlock_apply_three]

/-- A representative vector for each line of the standard strong triple. -/
def standardTripleVector : Fin 3 → SymplecticVector :=
  ![e1, f1, e1_add_f1_add_e2]

/-- Exact coordinate-free version of the article's three-row face table: on
the first line of the ordered pair left after deleting `i`, a triple
stabilizer acts by `tripleFaceUnit i`. -/
theorem tripleFaceUnit_action_firstRemaining (i : Fin 3)
    (g : TripleStabilizer) :
    g.1.1 (standardTripleVector (i.succAbove (0 : Fin 2))) =
      (tripleFaceUnit i g : ℂ) •
        standardTripleVector (i.succAbove (0 : Fin 2)) := by
  fin_cases i
  · simpa [standardTripleVector] using triple_apply_f1 g
  · simpa [standardTripleVector] using triple_apply_e1 g
  · simpa [standardTripleVector] using triple_apply_e1 g

/-- Every complex sign has modulus one. -/
theorem complexSign_norm (s : ComplexSign) : ‖(s.1 : ℂ)‖ = 1 := by
  rcases complexSign_eq_one_or_neg_one s with hs | hs
  · rw [hs]
    norm_num
  · rw [hs]
    norm_num

/-- All three exact face coordinates have modulus one. -/
theorem tripleFaceUnit_norm (i : Fin 3) (g : TripleStabilizer) :
    ‖(tripleFaceUnit i g : ℂ)‖ = 1 := by
  fin_cases i
  · simp [tripleSplitUnit, complexSign_norm]
  · exact complexSign_norm (tripleSignCoordinate g)
  · exact complexSign_norm (tripleSignCoordinate g)

/-- Pulling the degree-one generator `a ↦ log ‖a‖` of the pair
stabilizer back along any of the three face embeddings gives this function. -/
def tripleFaceLog (i : Fin 3) (g : TripleStabilizer) : ℝ :=
  Real.log ‖(tripleFaceUnit i g : ℂ)‖

/-- The original matrix computation: every one of the three pulled-back
logarithmic characters is identically zero. -/
@[simp]
theorem tripleFaceLog_eq_zero (i : Fin 3) (g : TripleStabilizer) :
    tripleFaceLog i g = 0 := by
  rw [tripleFaceLog, tripleFaceUnit_norm, Real.log_one]

/-! ## First cohomology of the triple stabilizer -/

/-- Continuous real characters of a topological group, realized as a linear
subspace of continuous functions. -/
def ContinuousRealCharacters (J : Type*) [TopologicalSpace J] [Group J] :
    Submodule ℝ C(J, ℝ) where
  carrier := {f | ∀ x y, f (x * y) = f x + f y}
  zero_mem' := by
    intro x y
    simp
  add_mem' := by
    intro f g hf hg x y
    change f (x * y) + g (x * y) =
      (f x + g x) + (f y + g y)
    rw [hf, hg]
    ring
  smul_mem' := by
    intro r f hf x y
    change r * f (x * y) = r * f x + r * f y
    rw [hf]
    ring

@[simp]
theorem ContinuousRealCharacters.map_one
    {J : Type*} [TopologicalSpace J] [Group J]
    (f : ContinuousRealCharacters J) : f.1 1 = 0 := by
  have h := f.2 (1 : J) 1
  rw [one_mul] at h
  linarith

/-- Restrict a triple-stabilizer character to its additive complex factor. -/
def restrictTripleCharacter
    (f : ContinuousRealCharacters TripleStabilizer) : ℂ →+ ℝ where
  toFun z := f.1 (tripleStabilizerHom
    (1, Multiplicative.ofAdd z))
  map_zero' := by
    change f.1 (tripleStabilizerHom
      (1 : ComplexSign × Multiplicative ℂ)) = 0
    rw [tripleStabilizerHom.map_one]
    exact ContinuousRealCharacters.map_one f
  map_add' z w := by
    rw [show tripleStabilizerHom
        (1, Multiplicative.ofAdd (z + w)) =
          tripleStabilizerHom (1, Multiplicative.ofAdd z) *
            tripleStabilizerHom (1, Multiplicative.ofAdd w) by
      rw [← tripleStabilizerHom.map_mul]
      apply congrArg tripleStabilizerHom
      apply Prod.ext
      · simp
      · apply Multiplicative.ext
        rfl]
    exact f.2 _ _

theorem continuous_restrictTripleCharacter
    (f : ContinuousRealCharacters TripleStabilizer) :
    Continuous (restrictTripleCharacter f) := by
  exact f.1.continuous.comp
    (continuous_tripleStabilizerHom.comp
      (continuous_const.prodMk
        (continuous_ofAdd.comp continuous_id)))

/-- A continuous additive character of the complex vector group is
automatically real-linear. -/
def tripleCharacterToComplexDual :
    ContinuousRealCharacters TripleStabilizer →ₗ[ℝ] (ℂ →ₗ[ℝ] ℝ) where
  toFun f :=
    (restrictTripleCharacter f).toRealLinearMap
      (continuous_restrictTripleCharacter f) |>.toLinearMap
  map_add' f g := by
    ext z
    rfl
  map_smul' r f := by
    ext z
    rfl

@[simp]
theorem tripleCharacterToComplexDual_apply
    (f : ContinuousRealCharacters TripleStabilizer) (z : ℂ) :
    tripleCharacterToComplexDual f z =
      f.1 (tripleStabilizerHom (1, Multiplicative.ofAdd z)) :=
  rfl

theorem tripleAddCoordinate_mul (g h : TripleStabilizer) :
    tripleAddCoordinate (g * h) =
      tripleAddCoordinate g + tripleAddCoordinate h := by
  have hc := tripleStabilizerExplicitEquiv.symm.map_mul g h
  exact congrArg (fun p : ComplexSign × Multiplicative ℂ ↦ p.2.toAdd) hc

@[simp]
theorem tripleAddCoordinate_tripleStabilizerHom
    (s : ComplexSign × Multiplicative ℂ) :
    tripleAddCoordinate (tripleStabilizerHom s) = s.2.toAdd := by
  have h := tripleCoordinates_leftInverse s
  exact congrArg (fun p : ComplexSign × Multiplicative ℂ ↦ p.2.toAdd) h

/-- Extend a real-linear functional on `ℂ` across the finite sign factor. -/
def tripleCharacterOfComplexDual (ell : ℂ →ₗ[ℝ] ℝ) :
    ContinuousRealCharacters TripleStabilizer := by
  refine ⟨⟨fun g ↦ ell (tripleAddCoordinate g), ?_⟩, ?_⟩
  · exact ell.continuous_of_finiteDimensional.comp
      continuous_tripleAddCoordinate
  · intro g h
    change ell (tripleAddCoordinate (g * h)) =
      ell (tripleAddCoordinate g) + ell (tripleAddCoordinate h)
    rw [tripleAddCoordinate_mul, map_add]

@[simp]
theorem tripleCharacterOfComplexDual_apply
    (ell : ℂ →ₗ[ℝ] ℝ) (g : TripleStabilizer) :
    (tripleCharacterOfComplexDual ell).1 g =
      ell (tripleAddCoordinate g) :=
  rfl

theorem tripleCharacter_sign_zero
    (f : ContinuousRealCharacters TripleStabilizer)
    (s : ComplexSign) :
    f.1 (tripleStabilizerHom (s, 1)) = 0 := by
  let a : TripleStabilizer := tripleStabilizerHom (s, 1)
  have ha2 : a * a = 1 := by
    change tripleStabilizerHom (s, 1) *
        tripleStabilizerHom (s, 1) = 1
    rw [← tripleStabilizerHom.map_mul]
    have hs2 : s * s = 1 := by
      apply Subtype.ext
      change s.1 * s.1 = (1 : ℂˣ)
      have hsPow : s.1 ^ 2 = (1 : ℂˣ) := s.2
      simpa only [pow_two] using hsPow
    rw [show (s, (1 : Multiplicative ℂ)) * (s, 1) =
        (1 : ComplexSign × Multiplicative ℂ) by
      apply Prod.ext
      · exact hs2
      · simp]
    exact tripleStabilizerHom.map_one
  have h := f.2 a a
  rw [ha2, ContinuousRealCharacters.map_one f] at h
  linarith

theorem tripleCharacter_decompose
    (f : ContinuousRealCharacters TripleStabilizer)
    (s : ComplexSign × Multiplicative ℂ) :
    f.1 (tripleStabilizerHom s) =
      f.1 (tripleStabilizerHom (1, s.2)) := by
  have hdecomp : tripleStabilizerHom s =
      tripleStabilizerHom (s.1, 1) *
        tripleStabilizerHom (1, s.2) := by
    rw [← tripleStabilizerHom.map_mul]
    simp
  rw [hdecomp, f.2, tripleCharacter_sign_zero, zero_add]

/-- The continuous-character calculation
`H¹({±1}×(ℂ,+);ℝ) ≅ Hom_ℝ(ℂ,ℝ)`, proved here on the explicit
triple-stabilizer isomorphism. -/
def tripleCharactersEquivComplexDual :
    ContinuousRealCharacters TripleStabilizer ≃ₗ[ℝ] (ℂ →ₗ[ℝ] ℝ) where
  toFun := tripleCharacterToComplexDual
  invFun := tripleCharacterOfComplexDual
  left_inv := by
    intro f
    apply Subtype.ext
    apply ContinuousMap.ext
    intro g
    obtain ⟨s, rfl⟩ := tripleStabilizerHom_surjective g
    rw [tripleCharacterOfComplexDual_apply,
      tripleCharacterToComplexDual_apply,
      tripleAddCoordinate_tripleStabilizerHom]
    exact (tripleCharacter_decompose f s).symm
  right_inv := by
    intro ell
    ext z
    rw [tripleCharacterToComplexDual_apply,
      tripleCharacterOfComplexDual_apply,
      tripleAddCoordinate_tripleStabilizerHom]
    rfl
  map_add' := tripleCharacterToComplexDual.map_add
  map_smul' := tripleCharacterToComplexDual.map_smul

/-! ## The conull-orbit algebra: transitivity -/

/-- The projective stabilizer of the standard line.  This is the maximal
parabolic denoted `Q` in the article. -/
abbrev LineStabilizer :=
  MulAction.stabilizer SymplecticGroup (standardPair 0)

/-- The open algebraic locus of ordered transverse pairs. -/
abbrev TransversePair :=
  {x : ProjectiveConfig 2 // Transverse (x 0) (x 1)}

/-- A transverse ordered pair can be completed to a strong ordered triple.
The third vector is chosen outside the pair span and outside the two
symplectic hyperplanes.  This is the missing linear-algebra step needed to
reduce pair transitivity to the already proved strong-triple transitivity. -/
theorem transverse_pair_exists_strongTriple
    (l m : ProjectivePoint) (hlm : Transverse l m) :
    ∃ z : StrongTriple, z.1 0 = l ∧ z.1 1 = m := by
  let x : ProjectiveConfig 3 := ![l, m, l]
  let family : Unit → ProjectiveConfig 3 := fun _ => x
  obtain ⟨v, hv⟩ := exists_vector_avoiding_apexBad family
  have hv0 : v ≠ 0 := by
    simpa [apexBadSubmodule] using hv none
  have hvl : omega v l.rep ≠ 0 := by
    have h := hv (some (Sum.inl ((), (0 : Fin 3))))
    simpa [family, x, apexBadSubmodule, LinearMap.mem_ker] using h
  have hvm : omega v m.rep ≠ 0 := by
    have h := hv (some (Sum.inl ((), (1 : Fin 3))))
    simpa [family, x, apexBadSubmodule, LinearMap.mem_ker] using h
  have hvspan : v ∉ projectiveTripleSpan x id := by
    simpa [family, apexBadSubmodule] using
      hv (some (Sum.inr ((), id)))
  let p : ProjectivePoint := Projectivization.mk ℂ v hv0
  let z0 : ProjectiveConfig 3 := ![l, m, p]
  let u : ProjectiveLift z0 := {
    vec := ![l.rep, m.rep, v]
    ne_zero := by
      intro i
      fin_cases i
      · exact l.rep_nonzero
      · exact m.rep_nonzero
      · exact hv0
    projectivizes := by
      intro i
      fin_cases i
      · exact Projectivization.mk_rep l
      · exact Projectivization.mk_rep m
      · rfl }
  have hlmLI : LinearIndependent ℂ
      (![l.rep, m.rep] : Fin 2 → SymplecticVector) := by
    rw [linearIndependent_fin2]
    constructor
    · exact m.rep_nonzero
    · intro a ha
      by_cases ha0 : a = 0
      · apply l.rep_nonzero
        simpa [ha0] using ha.symm
      · apply hlm
        have hpair : a * omega l.rep m.rep = 0 := by
          calc
            a * omega l.rep m.rep = omega l.rep (a • m.rep) := by simp
            _ = omega l.rep l.rep := congrArg (fun w => omega l.rep w) ha
            _ = 0 := omega_isAlt _
        exact (mul_eq_zero.mp hpair).resolve_left ha0
  have hvspan' : v ∉ Submodule.span ℂ
      (Set.range (![l.rep, m.rep] : Fin 2 → SymplecticVector)) := by
    intro hmem
    apply hvspan
    rw [show projectiveTripleSpan x id = Submodule.span ℂ
        (Set.range (![l.rep, m.rep] : Fin 2 → SymplecticVector)) by
      simp [projectiveTripleSpan, x, Projectivization.submodule_eq,
        Submodule.span_insert, sup_comm]]
    exact hmem
  have huLI : LinearIndependent ℂ u.vec := by
    have h := hlmLI.finSnoc hvspan'
    simpa [u, Fin.snoc] using h
  have hzGeneric : IsGeneric z0 := by
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact False.elim (hij rfl)
      · exact hlm
      · simpa [z0, p] using
          (transverse_mk_iff v l.rep hv0 l.rep_nonzero).2 hvl |>.symm
      · exact hlm.symm
      · exact False.elim (hij rfl)
      · simpa [z0, p] using
          (transverse_mk_iff v m.rep hv0 m.rep_nonzero).2 hvm |>.symm
      · simpa [z0, p] using
          (transverse_mk_iff v l.rep hv0 l.rep_nonzero).2 hvl
      · simpa [z0, p] using
          (transverse_mk_iff v m.rep hv0 m.rep_nonzero).2 hvm
      · exact False.elim (hij rfl)
    · intro e he
      have hcard := Fintype.card_le_of_injective e he
      norm_num at hcard
  have hzIndependent : TriplesIndependent z0 := by
    intro e he
    have hli : LinearIndependent ℂ (fun k => u.vec (e k)) :=
      huLI.comp e he
    have heq : projectiveTripleSpan z0 e = Submodule.span ℂ
        (Set.range fun k => u.vec (e k)) := by
      rw [projectiveTripleSpan, Submodule.span_range_eq_iSup]
      congr 1
      funext k
      rw [← u.projectivizes (e k), Projectivization.submodule_mk]
    rw [heq, finrank_span_eq_card hli, Fintype.card_fin]
  exact ⟨⟨z0, hzGeneric, hzIndependent⟩, rfl, rfl⟩

/-- `Sp(4,ℂ)` acts transitively on the ordered transverse-pair locus. -/
theorem transversePair_transitive (x : TransversePair) :
    ∃ g : SymplecticGroup, g • x.1 = standardPair := by
  obtain ⟨z, hz0, hz1⟩ :=
    transverse_pair_exists_strongTriple (x.1 0) (x.1 1) x.2
  obtain ⟨g, hg⟩ := exists_smul_eq_standardTriple z
  refine ⟨g, funext fun i => ?_⟩
  fin_cases i
  · have h0 := congrFun hg 0
    change g • z.1 0 = standardTriple 0 at h0
    simpa [hz0, standardTriple, standardPair] using h0
  · have h1 := congrFun hg 1
    change g • z.1 1 = standardTriple 1 at h1
    simpa [hz1, standardTriple, standardPair] using h1

/-- `Sp(4,ℂ)` acts transitively on complex projective three-space. -/
theorem projective_transitive (l : ProjectivePoint) :
    ∃ g : SymplecticGroup, g • l = standardPair 0 := by
  obtain ⟨v, hv⟩ := SetLike.exists_not_mem_of_ne_top
    (LinearMap.ker (omega.flip l.rep)) (symplecticKernel_ne_top l) rfl
  have hv0 : v ≠ 0 := by
    intro h
    apply hv
    simp [h]
  let m : ProjectivePoint := Projectivization.mk ℂ v hv0
  have hlm : Transverse l m := by
    rw [← Projectivization.mk_rep l, transverse_mk_iff]
    intro hzero
    apply hv
    rw [LinearMap.mem_ker]
    simp [omega_skew, hzero]
  obtain ⟨z, hz0, _hz1⟩ := transverse_pair_exists_strongTriple l m hlm
  obtain ⟨g, hg⟩ := exists_smul_eq_standardTriple z
  refine ⟨g, ?_⟩
  have h0 := congrFun hg 0
  change g • z.1 0 = standardTriple 0 at h0
  simpa [hz0, standardTriple, standardPair] using h0

end
end ProjectiveStabilizers
end Sp4
