import Sp4.Cohomology.CentralPrism
import Sp4.Cohomology.Stabilizers
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# The contact grading and positive Levi weights

This file kernel-checks the article-specific linear algebra used before the
continuous Hochschild--Serre input.  The nilradical of the line parabolic has
contact grading

`u = u₁ ⊕ u₂`, with complex dimensions two and one,

and the split central coordinate `r` acts with weights `r` on `u₁` and
`r²` on `u₂`.  Consequently the underlying real dual has exponent list
`1,1,1,1,2,2`; every nonzero exterior degree has strictly positive exponent.
The final theorem combines the resulting inverse for `z - 1` with the
internally proved central prism.
-/

namespace Sp4
namespace ParabolicWeights

noncomputable section

open scoped BigOperators
open scoped LinearAlgebra.Projectivization
open ProjectiveStabilizers TwoFree

/-- The degree-one layer in the contact grading. -/
abbrev ContactLayerOne := Fin 2 → ℂ

/-- The central degree-two layer in the contact grading. -/
abbrev ContactLayerTwo := ℂ

/-- A coordinate model of the complex three-dimensional Heisenberg
nilradical. -/
abbrev ContactNilradical := ContactLayerOne × ContactLayerTwo

/-- The alternating bracket from the degree-one layer to the centre. -/
def contactBracket (x y : ContactLayerOne) : ContactLayerTwo :=
  x 0 * y 1 - x 1 * y 0

@[simp]
theorem contactBracket_self (x : ContactLayerOne) :
    contactBracket x x = 0 := by
  simp only [contactBracket]
  ring

theorem contactBracket_skew (x y : ContactLayerOne) :
    contactBracket y x = -contactBracket x y := by
  simp only [contactBracket]
  ring

/-- The bracket fills the whole one-dimensional central layer, expressing
`[u₁,u₁]=u₂` in the chosen coordinates. -/
theorem contactBracket_surjective :
    Function.Surjective
      (fun p : ContactLayerOne × ContactLayerOne ↦
        contactBracket p.1 p.2) := by
  intro z
  refine ⟨(![1, 0], ![0, z]), ?_⟩
  simp [contactBracket]

@[simp]
theorem finrank_contactLayerOne :
    Module.finrank ℂ ContactLayerOne = 2 := by
  simp [ContactLayerOne]

@[simp]
theorem finrank_contactLayerTwo :
    Module.finrank ℂ ContactLayerTwo = 1 := by
  simp [ContactLayerTwo]

@[simp]
theorem finrank_contactNilradical :
    Module.finrank ℂ ContactNilradical = 3 := by
  simp [ContactNilradical]

/-- The split-centre action in the contact grading. -/
def contactScale (r : ℝ) : ContactNilradical →ₗ[ℂ] ContactNilradical where
  toFun x :=
    ((fun i ↦ (r : ℂ) * x.1 i), (r : ℂ) ^ 2 * x.2)
  map_add' x y := by
    apply Prod.ext
    · funext i
      simp only [Prod.fst_add, Pi.add_apply]
      ring
    · simp only [Prod.snd_add]
      ring
  map_smul' c x := by
    apply Prod.ext
    · funext i
      change (r : ℂ) * (c * x.1 i) = c * ((r : ℂ) * x.1 i)
      ring
    · change (r : ℂ) ^ 2 * (c * x.2) =
        c * ((r : ℂ) ^ 2 * x.2)
      ring

@[simp]
theorem contactScale_layerOne (r : ℝ) (x : ContactNilradical)
    (i : Fin 2) :
    (contactScale r x).1 i = (r : ℂ) * x.1 i :=
  rfl

@[simp]
theorem contactScale_layerTwo (r : ℝ) (x : ContactNilradical) :
    (contactScale r x).2 = (r : ℂ) ^ 2 * x.2 :=
  rfl

/-- Compatibility of the weights `r,r,r²` with the Heisenberg bracket. -/
theorem contactBracket_scale (r : ℝ) (x y : ContactLayerOne) :
    contactBracket (fun i ↦ (r : ℂ) * x i)
        (fun i ↦ (r : ℂ) * y i) =
      (r : ℂ) ^ 2 * contactBracket x y := by
  simp only [contactBracket]
  ring

/-! ## The contact coordinates inside the actual line parabolic -/

/-- The underlying triangular transformation attached to Heisenberg
coordinates `(v,z)`.  In the ordered basis `(e₁,f₁,e₂,f₂)` it sends
`f₁` to `f₁ + v₀e₂ + v₁f₂ + z e₁` and sends a vector `w` in the second
symplectic plane to `w + ω(v,w)e₁`. -/
def lineUnipotentTransform (u : ContactNilradical)
    (x : SymplecticVector) : SymplecticVector :=
  ![x 0 + u.2 * x 1 - u.1 1 * x 2 + u.1 0 * x 3,
    x 1,
    x 2 + u.1 0 * x 1,
    x 3 + u.1 1 * x 1]

/-- The triangular transformation is invertible, with inverse obtained by
negating both Heisenberg coordinates. -/
def lineUnipotentEquiv (u : ContactNilradical) :
    SymplecticVector ≃ₗ[ℂ] SymplecticVector where
  toFun := lineUnipotentTransform u
  invFun := lineUnipotentTransform (-u)
  left_inv x := by
    funext i
    fin_cases i <;> simp [lineUnipotentTransform] <;> ring
  right_inv x := by
    funext i
    fin_cases i <;> simp [lineUnipotentTransform] <;> ring
  map_add' x y := by
    funext i
    fin_cases i <;> simp [lineUnipotentTransform] <;> ring
  map_smul' c x := by
    funext i
    fin_cases i <;> simp [lineUnipotentTransform] <;> ring

theorem lineUnipotentEquiv_preserves (u : ContactNilradical)
    (x y : SymplecticVector) :
    omega (lineUnipotentEquiv u x) (lineUnipotentEquiv u y) = omega x y := by
  change omega (lineUnipotentTransform u x)
      (lineUnipotentTransform u y) = omega x y
  simp [omega_apply, lineUnipotentTransform]
  ring

/-- The concrete element of `Sp(4,ℂ)` represented by Heisenberg coordinates. -/
def lineUnipotent (u : ContactNilradical) : SymplecticGroup :=
  ⟨lineUnipotentEquiv u, lineUnipotentEquiv_preserves u⟩

@[simp]
theorem lineUnipotent_apply_zero (u : ContactNilradical)
    (x : SymplecticVector) :
    (lineUnipotent u).1 x 0 =
      x 0 + u.2 * x 1 - u.1 1 * x 2 + u.1 0 * x 3 := rfl

@[simp]
theorem lineUnipotent_apply_one (u : ContactNilradical)
    (x : SymplecticVector) : (lineUnipotent u).1 x 1 = x 1 := rfl

@[simp]
theorem lineUnipotent_apply_two (u : ContactNilradical)
    (x : SymplecticVector) :
    (lineUnipotent u).1 x 2 = x 2 + u.1 0 * x 1 := rfl

@[simp]
theorem lineUnipotent_apply_three (u : ContactNilradical)
    (x : SymplecticVector) :
    (lineUnipotent u).1 x 3 = x 3 + u.1 1 * x 1 := rfl

/-- The Heisenberg product in contact coordinates. -/
def contactProduct (u v : ContactNilradical) : ContactNilradical :=
  (u.1 + v.1, u.2 + v.2 + contactBracket u.1 v.1)

@[simp]
theorem lineUnipotent_zero : lineUnipotent 0 = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;> simp [lineUnipotent, lineUnipotentEquiv,
    lineUnipotentTransform]

theorem lineUnipotent_contactProduct (u v : ContactNilradical) :
    lineUnipotent (contactProduct u v) = lineUnipotent u * lineUnipotent v := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [lineUnipotent, lineUnipotentEquiv, lineUnipotentTransform,
      contactProduct, contactBracket] <;> ring

theorem lineUnipotent_inv (u : ContactNilradical) :
    (lineUnipotent u)⁻¹ = lineUnipotent (-u) := by
  apply inv_eq_of_mul_eq_one_left
  rw [← lineUnipotent_contactProduct]
  have hproduct : contactProduct (-u) u = 0 := by
    apply Prod.ext
    · simp [contactProduct]
    · simp [contactProduct, contactBracket]
      ring
  rw [hproduct, lineUnipotent_zero]

theorem lineUnipotent_injective : Function.Injective lineUnipotent := by
  intro u v huv
  apply Prod.ext
  · funext i
    fin_cases i
    · have h := congrArg (fun g : SymplecticGroup => g.1 f1 2) huv
      simpa [f1] using h
    · have h := congrArg (fun g : SymplecticGroup => g.1 f1 3) huv
      simpa [f1] using h
  · have h := congrArg (fun g : SymplecticGroup => g.1 f1 0) huv
    simpa [f1] using h

/-- The actual Heisenberg subgroup of `Sp(4,ℂ)` obtained from the contact
coordinates. -/
def lineUnipotentRadical : Subgroup SymplecticGroup where
  carrier := Set.range lineUnipotent
  one_mem' := ⟨0, lineUnipotent_zero⟩
  mul_mem' := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨contactProduct u v, lineUnipotent_contactProduct u v⟩
  inv_mem' := by
    rintro _ ⟨u, rfl⟩
    exact ⟨-u, lineUnipotent_inv u |>.symm⟩

theorem lineUnipotent_fixes_standardLine (u : ContactNilradical) :
    lineUnipotent u • standardPair 0 = standardPair 0 := by
  change (lineUnipotent u).1 • Projectivization.mk ℂ e1 e1_ne_zero =
    Projectivization.mk ℂ e1 e1_ne_zero
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  funext i
  fin_cases i <;> simp [e1, lineUnipotent, lineUnipotentEquiv,
    lineUnipotentTransform]

/-- The coordinate subgroup lies in the concrete projective-line stabilizer
`Q` used on the first page of the article's double complex. -/
theorem lineUnipotentRadical_le_lineStabilizer :
    lineUnipotentRadical ≤ ProjectiveStabilizers.LineStabilizer := by
  rintro _ ⟨u, rfl⟩
  exact lineUnipotent_fixes_standardLine u

/-! ## The full Heisenberg--Levi decomposition of the line parabolic -/

/-- The nonzero scalar by which an element of the projective-line
stabilizer acts on the standard line. -/
theorem lineStabilizer_scalar
    (g : ProjectiveStabilizers.LineStabilizer) :
    ∃ a : ℂ, a ≠ 0 ∧ a • e1 = g.1.1 e1 := by
  have h0 := g.2
  change g.1.1 • Projectivization.mk ℂ e1 e1_ne_zero =
    Projectivization.mk ℂ e1 e1_ne_zero at h0
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at h0
  obtain ⟨a, ha⟩ := h0
  have ha' : a • e1 = g.1.1 e1 := by
    simpa [LinearEquiv.smul_def] using ha
  have ha0 : a ≠ 0 := by
    intro ha0
    apply e1_ne_zero
    apply g.1.1.injective
    rw [← ha', ha0, zero_smul, map_zero]
  exact ⟨a, ha0, ha'⟩

/-- The full Levi action on the Heisenberg coordinates.  If the Levi
parameter is `(a,B)`, its degree-one action is `v ↦ a Bv` and its central
action is `z ↦ a²z`. -/
def contactLeviAction (p : ℂˣ × SL2C) (u : ContactNilradical) :
    ContactNilradical :=
  (![p.1.1 * (p.2.1 0 0 * u.1 0 + p.2.1 0 1 * u.1 1),
      p.1.1 * (p.2.1 1 0 * u.1 0 + p.2.1 1 1 * u.1 1)],
    p.1.1 ^ 2 * u.2)

/-- Direct matrix verification that the explicit Levi normalizes the
Heisenberg subgroup, with the action displayed in `contactLeviAction`. -/
theorem pairBlock_mul_lineUnipotent
    (p : ℂˣ × SL2C) (u : ContactNilradical) :
    pairBlock p * lineUnipotent u =
      lineUnipotent (contactLeviAction p u) * pairBlock p := by
  have hdet : p.2.1 0 0 * p.2.1 1 1 -
      p.2.1 0 1 * p.2.1 1 0 = 1 := by
    have h := p.2.2
    rw [Matrix.det_fin_two] at h
    exact h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i
  · simp [pairBlock_apply_zero, pairBlock_apply_one,
      pairBlock_apply_two, pairBlock_apply_three,
      lineUnipotent, lineUnipotentEquiv, lineUnipotentTransform,
      contactLeviAction]
    field_simp
    linear_combination
      (u.1 1 * x 2 - u.1 0 * x 3) * hdet
  · simp [pairBlock_apply_zero, pairBlock_apply_one,
      pairBlock_apply_two, pairBlock_apply_three,
      lineUnipotent, lineUnipotentEquiv, lineUnipotentTransform,
      contactLeviAction]
  · simp [pairBlock_apply_zero, pairBlock_apply_one,
      pairBlock_apply_two, pairBlock_apply_three,
      lineUnipotent, lineUnipotentEquiv, lineUnipotentTransform,
      contactLeviAction]
    field_simp
    ring
  · simp [pairBlock_apply_zero, pairBlock_apply_one,
      pairBlock_apply_two, pairBlock_apply_three,
      lineUnipotent, lineUnipotentEquiv, lineUnipotentTransform,
      contactLeviAction]
    field_simp
    ring

/-- The standard pair stabilizer is the concrete Levi subgroup of the line
parabolic. -/
def pairStabilizerToLine :
    PairStabilizer →* ProjectiveStabilizers.LineStabilizer where
  toFun l := ⟨l.1, congrFun l.2 0⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem pairStabilizerToLine_injective :
    Function.Injective pairStabilizerToLine := by
  intro l m h
  apply Subtype.ext
  exact congrArg
    (fun q : ProjectiveStabilizers.LineStabilizer => q.1) h

/-- Every element of the concrete Levi normalizes the coordinate
Heisenberg subgroup. -/
theorem pairStabilizer_normalizes_lineUnipotent
    (l : PairStabilizer) (u : ContactNilradical) :
    ∃ v : ContactNilradical,
      l.1 * lineUnipotent u * l.1⁻¹ = lineUnipotent v := by
  obtain ⟨p, rfl⟩ := pairStabilizerHom_surjective l
  refine ⟨contactLeviAction p u, ?_⟩
  change pairBlock p * lineUnipotent u * (pairBlock p)⁻¹ = _
  rw [pairBlock_mul_lineUnipotent]
  simp

/-- The explicit Heisenberg subgroup meets the Levi subgroup trivially. -/
theorem lineUnipotent_inter_pairStabilizer
    (u : ContactNilradical) (l : PairStabilizer)
    (h : lineUnipotent u = l.1) : u = 0 := by
  obtain ⟨_a, b, _ha0, _hb0, _ha, hb, _hab⟩ :=
    pairStabilizer_scalars l
  have hv := congrArg (fun g : SymplecticGroup => g.1 f1) h
  rw [← hb] at hv
  apply Prod.ext
  · funext i
    fin_cases i
    · have hi := congrArg (fun x : SymplecticVector => x 2) hv
      simpa [lineUnipotent, lineUnipotentEquiv,
        lineUnipotentTransform, f1] using hi
    · have hi := congrArg (fun x : SymplecticVector => x 3) hv
      simpa [lineUnipotent, lineUnipotentEquiv,
        lineUnipotentTransform, f1] using hi
  · have hi := congrArg (fun x : SymplecticVector => x 0) hv
    simpa [lineUnipotent, lineUnipotentEquiv,
      lineUnipotentTransform, f1] using hi

/-- Every element of the actual projective-line stabilizer factors as a
Heisenberg element followed by an element of the standard Levi. -/
theorem lineStabilizer_factorization
    (g : ProjectiveStabilizers.LineStabilizer) :
    ∃ u : ContactNilradical, ∃ l : PairStabilizer,
      g.1 = lineUnipotent u * l.1 := by
  obtain ⟨a, ha0, ha⟩ := lineStabilizer_scalar g
  have hab : a * g.1.1 f1 1 = 1 := by
    have hp := g.1.2 e1 f1
    rw [← ha] at hp
    simpa [omega_apply, e1, f1] using hp
  have hab' : a * g.1.1 ![0, 1, 0, 0] 1 = 1 := by
    simpa [f1] using hab
  have hb' : g.1.1 ![0, 1, 0, 0] 1 = a⁻¹ :=
    eq_inv_of_mul_eq_one_right hab'
  let u : ContactNilradical :=
    (![a * g.1.1 f1 2, a * g.1.1 f1 3], a * g.1.1 f1 0)
  let l0 : SymplecticGroup := lineUnipotent (-u) * g.1
  have hl0 : l0 • standardPair = standardPair := by
    funext i
    fin_cases i
    · change l0.1 • Projectivization.mk ℂ e1 e1_ne_zero =
        Projectivization.mk ℂ e1 e1_ne_zero
      rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
      refine ⟨a, ?_⟩
      change a • e1 = (lineUnipotent (-u)).1 (g.1.1 e1)
      rw [← ha]
      funext j
      fin_cases j <;>
        simp [lineUnipotent, lineUnipotentEquiv,
          lineUnipotentTransform, e1]
    · change l0.1 • Projectivization.mk ℂ f1 f1_ne_zero =
        Projectivization.mk ℂ f1 f1_ne_zero
      rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
      refine ⟨g.1.1 f1 1, ?_⟩
      change g.1.1 f1 1 • f1 =
        (lineUnipotent (-u)).1 (g.1.1 f1)
      funext j
      fin_cases j <;>
        simp [lineUnipotent, lineUnipotentEquiv,
          lineUnipotentTransform, u, f1, hb'] <;>
        field_simp [ha0] <;> ring
  let l : PairStabilizer := ⟨l0, hl0⟩
  refine ⟨u, l, ?_⟩
  change g.1 = lineUnipotent u * (lineUnipotent (-u) * g.1)
  rw [← mul_assoc, ← lineUnipotent_contactProduct]
  have hproduct : contactProduct u (-u) = 0 := by
    apply Prod.ext
    · simp [contactProduct]
    · simp [contactProduct, contactBracket]
      ring
  rw [hproduct, lineUnipotent_zero, one_mul]

/-- The Heisenberg--Levi factorization is unique. -/
theorem lineStabilizer_factorization_unique
    {u v : ContactNilradical} {l m : PairStabilizer}
    (h : lineUnipotent u * l.1 = lineUnipotent v * m.1) :
    u = v ∧ l = m := by
  let k : PairStabilizer := m * l⁻¹
  have hcross : lineUnipotent (contactProduct (-v) u) = k.1 := by
    rw [lineUnipotent_contactProduct]
    change lineUnipotent (-v) * lineUnipotent u = m.1 * l.1⁻¹
    calc
      lineUnipotent (-v) * lineUnipotent u =
          (lineUnipotent (-v) *
            (lineUnipotent u * l.1)) * l.1⁻¹ := by
              simp [mul_assoc]
      _ = (lineUnipotent (-v) *
            (lineUnipotent v * m.1)) * l.1⁻¹ := by rw [h]
      _ = m.1 * l.1⁻¹ := by
        rw [← lineUnipotent_inv v]
        simp
  have hkzero : contactProduct (-v) u = 0 :=
    lineUnipotent_inter_pairStabilizer _ k hcross
  have huv1 : u.1 = v.1 := by
    funext i
    have hi := congrFun (congrArg Prod.fst hkzero) i
    simp [contactProduct] at hi
    linear_combination hi
  have huv2 : u.2 = v.2 := by
    have hz := congrArg Prod.snd hkzero
    simp [contactProduct, huv1, contactBracket] at hz
    linear_combination hz
  have huv : u = v := Prod.ext huv1 huv2
  refine ⟨huv, ?_⟩
  subst v
  apply Subtype.ext
  exact mul_left_cancel h

/-- Algebraic Levi decomposition of the concrete line parabolic: every
element has one and only one coordinate pair `(u,l)` with `q = u l`. -/
theorem lineStabilizer_unique_factorization
    (g : ProjectiveStabilizers.LineStabilizer) :
    ∃! p : ContactNilradical × PairStabilizer,
      g.1 = lineUnipotent p.1 * p.2.1 := by
  obtain ⟨u, l, hul⟩ := lineStabilizer_factorization g
  refine ⟨(u, l), hul, ?_⟩
  rintro ⟨v, m⟩ hvm
  have hparts := lineStabilizer_factorization_unique
    (hul.symm.trans hvm)
  exact Prod.ext hparts.1.symm hparts.2.symm

/-- The coordinate Heisenberg subgroup, now regarded as a subgroup of the
actual line parabolic. -/
def lineUnipotentRadicalInQ :
    Subgroup ProjectiveStabilizers.LineStabilizer :=
  lineUnipotentRadical.comap
    ProjectiveStabilizers.LineStabilizer.subtype

/-- The explicit Heisenberg subgroup is normal in the actual line
parabolic.  Together with unique factorization, this proves the concrete
semidirect-product structure used by Hochschild--Serre. -/
theorem lineUnipotentRadicalInQ_normal :
    lineUnipotentRadicalInQ.Normal := by
  constructor
  intro n hn g
  change n.1 ∈ lineUnipotentRadical at hn
  obtain ⟨u, hu⟩ := hn
  obtain ⟨v, l, hg⟩ := lineStabilizer_factorization g
  obtain ⟨w, hw⟩ := pairStabilizer_normalizes_lineUnipotent l u
  change g.1 * n.1 * g.1⁻¹ ∈ lineUnipotentRadical
  rw [← hu, hg]
  have heq :
      (lineUnipotent v * l.1) * lineUnipotent u *
          (lineUnipotent v * l.1)⁻¹ =
        lineUnipotent v *
          (l.1 * lineUnipotent u * l.1⁻¹) *
            (lineUnipotent v)⁻¹ := by
    group
  rw [heq, hw]
  exact lineUnipotentRadical.mul_mem
    (lineUnipotentRadical.mul_mem
      ⟨v, rfl⟩ ⟨w, rfl⟩)
    (lineUnipotentRadical.inv_mem ⟨v, rfl⟩)

/-- Regard a nonzero real number as a complex unit. -/
def realScaleUnit (r : ℝ) (hr : r ≠ 0) : ℂˣ :=
  Units.mk0 (r : ℂ) (by exact_mod_cast hr)

/-- The concrete Levi element
`a_r = diag(r,r⁻¹,1,1)` in the stabilizer of the standard transverse pair. -/
def lineLeviScale (r : ℝ) (hr : r ≠ 0) : PairStabilizer :=
  pairStabilizerHom (realScaleUnit r hr, 1)

/-- The element `a_r` is central in the explicit Levi
`ℂˣ × SL(2,ℂ)`. -/
theorem lineLeviScale_centralInLevi (r : ℝ) (hr : r ≠ 0)
    (g : PairStabilizer) :
    lineLeviScale r hr * g = g * lineLeviScale r hr := by
  obtain ⟨p, rfl⟩ := pairStabilizerHom_surjective g
  change pairStabilizerHom (realScaleUnit r hr, 1) *
      pairStabilizerHom p =
    pairStabilizerHom p * pairStabilizerHom (realScaleUnit r hr, 1)
  rw [← pairStabilizerHom.map_mul, ← pairStabilizerHom.map_mul]
  apply congrArg pairStabilizerHom
  apply Prod.ext
  · exact mul_comm _ _
  · simp

/-- The same Levi element, viewed in the line parabolic `Q`. -/
def lineLeviScaleInQ (r : ℝ) (hr : r ≠ 0) :
    ProjectiveStabilizers.LineStabilizer :=
  ⟨(lineLeviScale r hr).1, congrFun (lineLeviScale r hr).2 0⟩

/-- Direct matrix verification of the contact weights: moving `a_r` past a
unipotent element scales the degree-one layer by `r` and the centre by `r²`. -/
theorem lineLeviScale_mul_lineUnipotent (r : ℝ) (hr : r ≠ 0)
    (u : ContactNilradical) :
    (lineLeviScale r hr).1 * lineUnipotent u =
      lineUnipotent (contactScale r u) * (lineLeviScale r hr).1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [lineLeviScale, realScaleUnit, pairStabilizerHom,
      lineUnipotent, lineUnipotentEquiv, lineUnipotentTransform,
      contactScale, pairBlock_apply_zero, pairBlock_apply_one,
      pairBlock_apply_two, pairBlock_apply_three] <;>
    field_simp [hr] <;> ring

/-- Equivalently, conjugation by the actual matrix `a_r` induces exactly the
abstract contact scaling used in the exterior-weight calculation. -/
theorem lineLeviScale_conj_lineUnipotent (r : ℝ) (hr : r ≠ 0)
    (u : ContactNilradical) :
    (lineLeviScale r hr).1 * lineUnipotent u *
        ((lineLeviScale r hr).1)⁻¹ =
      lineUnipotent (contactScale r u) := by
  rw [lineLeviScale_mul_lineUnipotent r hr u]
  simp

/-! ## Exterior-dual weights -/

/-- The six real coordinate directions in the underlying real dual. -/
abbrev RealDualDirection := Fin 6

/-- Four real directions come from the two complex coordinates of `u₁`,
and two come from the one complex coordinate of `u₂`. -/
def dualWeightExponent (i : RealDualDirection) : ℕ :=
  if i.val < 4 then 1 else 2

theorem dualWeightExponent_eq_one (i : RealDualDirection)
    (hi : i.val < 4) : dualWeightExponent i = 1 := by
  simp [dualWeightExponent, hi]

theorem dualWeightExponent_eq_two (i : RealDualDirection)
    (hi : 4 ≤ i.val) : dualWeightExponent i = 2 := by
  simp [dualWeightExponent, Nat.not_lt.mpr hi]

theorem dualWeightExponent_pos (i : RealDualDirection) :
    0 < dualWeightExponent i := by
  unfold dualWeightExponent
  split <;> omega

/-- Coordinate basis for real exterior degree `s`. -/
abbrev ExteriorBasis (s : ℕ) :=
  {A : Finset RealDualDirection // A.card = s}

/-- The exponent of an exterior-dual basis vector is the sum of the exponents
of its constituent real dual directions. -/
def exteriorExponent {s : ℕ} (A : ExteriorBasis s) : ℕ :=
  ∑ i ∈ A.1, dualWeightExponent i

/-- Every basis vector in a positive exterior degree has positive exponent. -/
theorem exteriorExponent_pos {s : ℕ} (hs : 0 < s)
    (A : ExteriorBasis s) : 0 < exteriorExponent A := by
  have hcard : 0 < A.1.card := by
    simpa [A.2] using hs
  calc
    0 < A.1.card := hcard
    _ = ∑ _i ∈ A.1, (1 : ℕ) := by simp
    _ ≤ ∑ i ∈ A.1, dualWeightExponent i := by
      apply Finset.sum_le_sum
      intro i hi
      exact dualWeightExponent_pos i

/-- The concrete real coordinate model for the `s`-th exterior dual. -/
abbrev ExteriorWeightSpace (s : ℕ) := ExteriorBasis s → ℝ

/-- The eigenvalue of the dual action at an exterior basis vector. -/
def exteriorDualScale (r : ℝ) {s : ℕ} (A : ExteriorBasis s) : ℝ :=
  (r ^ exteriorExponent A)⁻¹

theorem exteriorDualScale_ne_one (r : ℝ) (hr : 1 < r)
    {s : ℕ} (hs : 0 < s) (A : ExteriorBasis s) :
    exteriorDualScale r A ≠ 1 := by
  apply inv_ne_one.mpr
  exact ne_of_gt (one_lt_pow₀ hr
    (Nat.ne_of_gt (exteriorExponent_pos hs A)))

theorem exteriorDualScale_sub_one_ne_zero (r : ℝ) (hr : 1 < r)
    {s : ℕ} (hs : 0 < s) (A : ExteriorBasis s) :
    exteriorDualScale r A - 1 ≠ 0 :=
  sub_ne_zero.mpr (exteriorDualScale_ne_one r hr hs A)

/-- The diagonal action on the real exterior-dual coordinate model. -/
def exteriorDualAction (r : ℝ) (s : ℕ) :
    ExteriorWeightSpace s →ₗ[ℝ] ExteriorWeightSpace s where
  toFun f A := exteriorDualScale r A * f A
  map_add' f g := by
    funext A
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext A
    change exteriorDualScale r A * (c * f A) =
      c * (exteriorDualScale r A * f A)
    ring

/-- In every positive exterior degree, the diagonal map `T_r - 1` is an
explicit real-linear equivalence. -/
def exteriorCentralDifferenceEquiv (r : ℝ) (hr : 1 < r)
    (s : ℕ) (hs : 0 < s) :
    ExteriorWeightSpace s ≃ₗ[ℝ] ExteriorWeightSpace s where
  toFun f A := (exteriorDualScale r A - 1) * f A
  invFun f A := (exteriorDualScale r A - 1)⁻¹ * f A
  left_inv f := by
    funext A
    change (exteriorDualScale r A - 1)⁻¹ *
      ((exteriorDualScale r A - 1) * f A) = f A
    rw [← mul_assoc, inv_mul_cancel₀
      (exteriorDualScale_sub_one_ne_zero r hr hs A), one_mul]
  right_inv f := by
    funext A
    change (exteriorDualScale r A - 1) *
      ((exteriorDualScale r A - 1)⁻¹ * f A) = f A
    rw [← mul_assoc, mul_inv_cancel₀
      (exteriorDualScale_sub_one_ne_zero r hr hs A), one_mul]
  map_add' f g := by
    funext A
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext A
    change (exteriorDualScale r A - 1) * (c * f A) =
      c * ((exteriorDualScale r A - 1) * f A)
    ring

theorem exteriorCentralDifferenceEquiv_toLinearMap
    (r : ℝ) (hr : 1 < r) (s : ℕ) (hs : 0 < s) :
    (exteriorCentralDifferenceEquiv r hr s hs).toLinearMap =
      exteriorDualAction r s - LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext A
  change (exteriorDualScale r A - 1) * f A =
    exteriorDualScale r A * f A - f A
  ring

theorem exteriorCentralDifference_bijective
    (r : ℝ) (hr : 1 < r) (s : ℕ) (hs : 0 < s) :
    Function.Bijective
      (exteriorDualAction r s -
        (LinearMap.id : ExteriorWeightSpace s →ₗ[ℝ]
          ExteriorWeightSpace s)) := by
  rw [← exteriorCentralDifferenceEquiv_toLinearMap r hr s hs]
  exact (exteriorCentralDifferenceEquiv r hr s hs).bijective

/-- A typed certificate collecting precisely the article-specific input to
the continuous Hochschild--Serre theorem.  The fixed value `r = 2` avoids any
existential choice.  Every field is proved below from the concrete matrices,
the Heisenberg law, and the explicit exterior weights. -/
structure LineParabolicWeightCertificate : Prop where
  unipotentParameter_injective : Function.Injective lineUnipotent
  unipotent_liesInLineParabolic :
    lineUnipotentRadical ≤ ProjectiveStabilizers.LineStabilizer
  leviEmbedding_injective : Function.Injective pairStabilizerToLine
  uniqueHeisenbergLeviFactorization :
    ∀ g : ProjectiveStabilizers.LineStabilizer,
      ∃! p : ContactNilradical × PairStabilizer,
        g.1 = lineUnipotent p.1 * p.2.1
  unipotent_normalInLineParabolic : lineUnipotentRadicalInQ.Normal
  leviElement_centralInLevi :
    ∀ g : PairStabilizer,
      lineLeviScale 2 (by norm_num) * g =
        g * lineLeviScale 2 (by norm_num)
  conjugation_hasContactWeights :
    ∀ u : ContactNilradical,
      (lineLeviScale 2 (by norm_num)).1 * lineUnipotent u *
          ((lineLeviScale 2 (by norm_num)).1)⁻¹ =
        lineUnipotent (contactScale 2 u)
  positiveExteriorExponent :
    ∀ {s : ℕ}, 0 < s → ∀ A : ExteriorBasis s,
      0 < exteriorExponent A
  centralDifference_bijective :
    ∀ (s : ℕ), 0 < s →
      Function.Bijective (exteriorDualAction 2 s -
        (LinearMap.id : ExteriorWeightSpace s →ₗ[ℝ]
          ExteriorWeightSpace s))

/-- The concrete `Sp(4,ℂ)` line parabolic satisfies the full weight
certificate required by Hochschild--Serre. -/
theorem concreteLineParabolicWeightCertificate :
    LineParabolicWeightCertificate where
  unipotentParameter_injective := lineUnipotent_injective
  unipotent_liesInLineParabolic := lineUnipotentRadical_le_lineStabilizer
  leviEmbedding_injective := pairStabilizerToLine_injective
  uniqueHeisenbergLeviFactorization := lineStabilizer_unique_factorization
  unipotent_normalInLineParabolic := lineUnipotentRadicalInQ_normal
  leviElement_centralInLevi := lineLeviScale_centralInLevi 2 (by norm_num)
  conjugation_hasContactWeights :=
    lineLeviScale_conj_lineUnipotent 2 (by norm_num)
  positiveExteriorExponent := fun hs A => exteriorExponent_pos hs A
  centralDifference_bijective := fun s hs =>
    exteriorCentralDifference_bijective 2 (by norm_num) s hs

/-! ## Combination with the central prism -/

universe uJ

/-- If a central group element acts through the displayed positive contact
weights, the central-prism theorem kills continuous cohomology in every
degree.  This is exactly the row-vanishing input used before applying the
external continuous Hochschild--Serre spectral sequence. -/
theorem continuousCohomology_eq_zero_of_contact_weights
    {J : Type uJ} [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    (r : ℝ) (hr : 1 < r) (s : ℕ) (hs : 0 < s)
    [DistribMulAction J (ExteriorWeightSpace s)]
    [SMulCommClass J ℝ (ExteriorWeightSpace s)]
    [ContinuousConstSMul J (ExteriorWeightSpace s)]
    (z : J) (hz : CentralPrism.IsCentral z)
    (hweight : ∀ (f : ExteriorWeightSpace s) (A : ExteriorBasis s),
      (z • f) A = exteriorDualScale r A * f A)
    (q : ℕ)
    (a : CentralPrism.ContinuousCohomology
      (J := J) (V := ExteriorWeightSpace s) q) :
    a = 0 := by
  let A : ExteriorWeightSpace s ≃L[ℝ] ExteriorWeightSpace s :=
    (exteriorCentralDifferenceEquiv r hr s hs).toContinuousLinearEquiv
  refine CentralPrism.continuousCohomology_eq_zero_of_central_difference
    hz A ?_ q a
  apply LinearMap.ext
  intro f
  funext B
  change (exteriorDualScale r B - 1) * f B = (z • f) B - f B
  rw [hweight]
  ring

end
end ParabolicWeights
end Sp4
