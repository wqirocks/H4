import Sp4.Symplectic.Gram

/-!
# Explicit normalized Pfaffian loci

This file starts the kernel-checked affine model independently of all measure and
cohomology infrastructure.  In particular, every denominator used by a face map is
carried by membership in the source subtype.
-/

namespace Sp4

namespace Pfaffian

noncomputable section

/-! ## Four-point coordinates -/

/-- Ambient affine coordinates for the normalized four-point Gram matrix. -/
@[ext]
structure Coord4 where
  x : ℂ
  y : ℂ
deriving DecidableEq

/-- Coordinate identification used to transport the standard metric topology
from `ℂ × ℂ` to the affine four-point chart. -/
def coord4EquivProd : Coord4 ≃ ℂ × ℂ where
  toFun q := (q.x, q.y)
  invFun q := ⟨q.1, q.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

/-! We transport the normed complex vector-space structure as well as the topology.
This makes the ordinary Fréchet derivative available for the explicit submersion
certificates used by fibre integration. -/
instance : NormedAddCommGroup Coord4 := coord4EquivProd.normedAddCommGroup

instance : Module ℂ Coord4 := coord4EquivProd.module ℂ

instance : NormedSpace ℂ Coord4 := coord4EquivProd.normedSpace ℂ

def coord4LinearEquivProd : Coord4 ≃ₗ[ℂ] ℂ × ℂ :=
  { coord4EquivProd with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

def coord4LinearIsometryEquivProd : Coord4 ≃ₗᵢ[ℂ] ℂ × ℂ :=
  LinearIsometryEquiv.mk coord4LinearEquivProd (fun _ => rfl)

/-- The same chart as a continuous complex-linear equivalence with the uniform
`Fin n → ℂ` convention used for Gaussian coordinate measures. -/
def coord4ContinuousLinearEquivFun : Coord4 ≃L[ℂ] (Fin 2 → ℂ) :=
  coord4LinearIsometryEquivProd.toContinuousLinearEquiv.trans
    (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm

instance : CompleteSpace Coord4 :=
  coord4LinearIsometryEquivProd.toIsometryEquiv.completeSpace

/-- The measurable structure on the affine chart is its Borel structure. -/
instance : MeasurableSpace Coord4 := borel Coord4

instance : BorelSpace Coord4 := ⟨rfl⟩

/-- The affine coordinate chart is homeomorphic to `ℂ²`. -/
def coord4HomeomorphProd : Coord4 ≃ₜ ℂ × ℂ :=
  coord4EquivProd.homeomorph

@[continuity, fun_prop]
theorem continuous_coord4_x : Continuous fun q : Coord4 => q.x := by
  change Continuous fun q : Coord4 => (coord4HomeomorphProd q).1
  exact continuous_fst.comp coord4HomeomorphProd.continuous

@[continuity, fun_prop]
theorem continuous_coord4_y : Continuous fun q : Coord4 => q.y := by
  change Continuous fun q : Coord4 => (coord4HomeomorphProd q).2
  exact continuous_snd.comp coord4HomeomorphProd.continuous

@[fun_prop]
theorem differentiable_coord4_x : Differentiable ℂ fun q : Coord4 => q.x := by
  change Differentiable ℂ fun q : Coord4 => (coord4LinearIsometryEquivProd q).1
  fun_prop

@[fun_prop]
theorem differentiable_coord4_y : Differentiable ℂ fun q : Coord4 => q.y := by
  change Differentiable ℂ fun q : Coord4 => (coord4LinearIsometryEquivProd q).2
  fun_prop

/-- Coordinatewise differentiability criterion for the transported `Coord4`
vector-space structure. -/
theorem differentiableAt_coord4_mk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → ℂ} {a : E} (hf : DifferentiableAt ℂ f a)
    (hg : DifferentiableAt ℂ g a) :
    DifferentiableAt ℂ (fun x => Coord4.mk (f x) (g x)) a := by
  change DifferentiableAt ℂ
    (fun x => coord4LinearIsometryEquivProd.symm (f x, g x)) a
  exact coord4LinearIsometryEquivProd.toContinuousLinearEquiv.symm.differentiableAt.comp a
    (hf.prodMk hg)

/-- The Pfaffian of the normalized four-point matrix in affine coordinates. -/
def delta4 (q : Coord4) : ℂ := 1 - q.x + q.y

@[continuity, fun_prop]
theorem continuous_delta4 : Continuous delta4 := by
  fun_prop (disch := aesop) [delta4]

/-- Predicate cutting out the normalized generic four-point locus. -/
structure IsU4 (q : Coord4) : Prop where
  x_ne : q.x ≠ 0
  y_ne : q.y ≠ 0
  delta_ne : delta4 q ≠ 0

/-- The ambient carrier of the normalized four-point chart. -/
def u4Set : Set Coord4 := {q | IsU4 q}

theorem isOpen_u4Set : IsOpen u4Set := by
  have hx : IsOpen {q : Coord4 | q.x ≠ 0} :=
    isOpen_ne_fun continuous_coord4_x continuous_const
  have hy : IsOpen {q : Coord4 | q.y ≠ 0} :=
    isOpen_ne_fun continuous_coord4_y continuous_const
  have hd : IsOpen {q : Coord4 | delta4 q ≠ 0} :=
    isOpen_ne_fun continuous_delta4 continuous_const
  rw [show u4Set = {q : Coord4 | q.x ≠ 0} ∩
      ({q : Coord4 | q.y ≠ 0} ∩ {q : Coord4 | delta4 q ≠ 0}) by
    ext q
    constructor
    · intro h
      exact ⟨h.x_ne, h.y_ne, h.delta_ne⟩
    · rintro ⟨hxq, hyq, hdq⟩
      exact ⟨hxq, hyq, hdq⟩]
  exact hx.inter (hy.inter hd)

/-- The normalized generic four-point locus. -/
abbrev U4 := {q : Coord4 // IsU4 q}

/-- The normalized four-point skew Gram matrix. -/
def matrix4 (q : Coord4) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 1, 1, 1;
     -1, 0, 1, q.x;
     -1, -1, 0, q.y;
     -1, -q.x, -q.y, 0]

/-- The degree-four Pfaffian polynomial, with the sign convention used in the paper. -/
def pfaffian4 (A : Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2

/-- Exact four-point Pfaffian certificate. -/
@[simp]
theorem pfaffian4_matrix4 (q : Coord4) : pfaffian4 (matrix4 q) = delta4 q := by
  simp [pfaffian4, matrix4, delta4]
  ring

/-! ## Five-point coordinates -/

/-- Ambient affine coordinates for the normalized five-point Gram matrix. -/
@[ext]
structure Coord5 where
  u : ℂ
  v : ℂ
  w : ℂ
  x : ℂ
  y : ℂ
deriving DecidableEq

/-- Coordinate identification with the standard five-dimensional complex affine
space.  It fixes the topology and Borel structure used by the measurable layer. -/
def coord5EquivFun : Coord5 ≃ (Fin 5 → ℂ) where
  toFun q := ![q.u, q.v, q.w, q.x, q.y]
  invFun q := ⟨q 0, q 1, q 2, q 3, q 4⟩
  left_inv q := by ext <;> simp
  right_inv q := by
    funext i
    fin_cases i <;> simp

instance : NormedAddCommGroup Coord5 := coord5EquivFun.normedAddCommGroup

instance : NormedSpace ℂ Coord5 := coord5EquivFun.normedSpace ℂ

def coord5LinearEquivFun : Coord5 ≃ₗ[ℂ] (Fin 5 → ℂ) :=
  { coord5EquivFun with
    map_add' := by
      intro q r
      funext i
      fin_cases i <;> rfl
    map_smul' := by
      intro c q
      funext i
      fin_cases i <;> rfl }

def coord5LinearIsometryEquivFun : Coord5 ≃ₗᵢ[ℂ] (Fin 5 → ℂ) :=
  LinearIsometryEquiv.mk coord5LinearEquivFun (by
    intro q
    simp only [coord5LinearEquivFun]
    rfl)

instance : CompleteSpace Coord5 :=
  coord5LinearIsometryEquivFun.toIsometryEquiv.completeSpace

instance : MeasurableSpace Coord5 := borel Coord5

instance : BorelSpace Coord5 := ⟨rfl⟩

def coord5HomeomorphFun : Coord5 ≃ₜ (Fin 5 → ℂ) :=
  coord5EquivFun.homeomorph

@[continuity, fun_prop] theorem continuous_coord5_u : Continuous fun q : Coord5 => q.u := by
  change Continuous fun q : Coord5 => coord5HomeomorphFun q 0
  exact (continuous_apply 0).comp coord5HomeomorphFun.continuous

@[continuity, fun_prop] theorem continuous_coord5_v : Continuous fun q : Coord5 => q.v := by
  change Continuous fun q : Coord5 => coord5HomeomorphFun q 1
  exact (continuous_apply 1).comp coord5HomeomorphFun.continuous

@[continuity, fun_prop] theorem continuous_coord5_w : Continuous fun q : Coord5 => q.w := by
  change Continuous fun q : Coord5 => coord5HomeomorphFun q 2
  exact (continuous_apply 2).comp coord5HomeomorphFun.continuous

@[continuity, fun_prop] theorem continuous_coord5_x : Continuous fun q : Coord5 => q.x := by
  change Continuous fun q : Coord5 => coord5HomeomorphFun q 3
  exact (continuous_apply 3).comp coord5HomeomorphFun.continuous

@[continuity, fun_prop] theorem continuous_coord5_y : Continuous fun q : Coord5 => q.y := by
  change Continuous fun q : Coord5 => coord5HomeomorphFun q 4
  exact (continuous_apply 4).comp coord5HomeomorphFun.continuous

@[fun_prop] theorem differentiable_coord5_u : Differentiable ℂ fun q : Coord5 => q.u := by
  change Differentiable ℂ fun q : Coord5 => coord5LinearIsometryEquivFun q 0
  fun_prop

@[fun_prop] theorem differentiable_coord5_v : Differentiable ℂ fun q : Coord5 => q.v := by
  change Differentiable ℂ fun q : Coord5 => coord5LinearIsometryEquivFun q 1
  fun_prop

@[fun_prop] theorem differentiable_coord5_w : Differentiable ℂ fun q : Coord5 => q.w := by
  change Differentiable ℂ fun q : Coord5 => coord5LinearIsometryEquivFun q 2
  fun_prop

@[fun_prop] theorem differentiable_coord5_x : Differentiable ℂ fun q : Coord5 => q.x := by
  change Differentiable ℂ fun q : Coord5 => coord5LinearIsometryEquivFun q 3
  fun_prop

@[fun_prop] theorem differentiable_coord5_y : Differentiable ℂ fun q : Coord5 => q.y := by
  change Differentiable ℂ fun q : Coord5 => coord5LinearIsometryEquivFun q 4
  fun_prop

/-- Coordinatewise differentiability criterion for the transported `Coord5`
vector-space structure. -/
theorem differentiableAt_coord5_mk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f₀ f₁ f₂ f₃ f₄ : E → ℂ} {a : E}
    (h₀ : DifferentiableAt ℂ f₀ a) (h₁ : DifferentiableAt ℂ f₁ a)
    (h₂ : DifferentiableAt ℂ f₂ a) (h₃ : DifferentiableAt ℂ f₃ a)
    (h₄ : DifferentiableAt ℂ f₄ a) :
    DifferentiableAt ℂ (fun x => Coord5.mk (f₀ x) (f₁ x) (f₂ x) (f₃ x) (f₄ x)) a := by
  change DifferentiableAt ℂ (fun x => coord5LinearIsometryEquivFun.symm
    (![f₀ x, f₁ x, f₂ x, f₃ x, f₄ x])) a
  apply coord5LinearIsometryEquivFun.toContinuousLinearEquiv.symm.differentiableAt.comp a
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;> simp <;> assumption

def p0 (q : Coord5) : ℂ := q.y - q.u * q.x + q.v * q.w
def p1 (q : Coord5) : ℂ := q.y - q.x + q.w
def p2 (q : Coord5) : ℂ := q.y - q.v + q.u
def p3 (q : Coord5) : ℂ := q.x - q.v + 1
def p4 (q : Coord5) : ℂ := q.w - q.u + 1

@[continuity, fun_prop] theorem continuous_p0 : Continuous p0 := by fun_prop [p0]
@[continuity, fun_prop] theorem continuous_p1 : Continuous p1 := by fun_prop [p1]
@[continuity, fun_prop] theorem continuous_p2 : Continuous p2 := by fun_prop [p2]
@[continuity, fun_prop] theorem continuous_p3 : Continuous p3 := by fun_prop [p3]
@[continuity, fun_prop] theorem continuous_p4 : Continuous p4 := by fun_prop [p4]

/-- Predicate cutting out the normalized generic five-point locus. -/
structure IsU5 (q : Coord5) : Prop where
  u_ne : q.u ≠ 0
  v_ne : q.v ≠ 0
  w_ne : q.w ≠ 0
  x_ne : q.x ≠ 0
  y_ne : q.y ≠ 0
  p0_ne : p0 q ≠ 0
  p1_ne : p1 q ≠ 0
  p2_ne : p2 q ≠ 0
  p3_ne : p3 q ≠ 0
  p4_ne : p4 q ≠ 0

/-- The ambient carrier of the normalized five-point chart. -/
def u5Set : Set Coord5 := {q | IsU5 q}

theorem isOpen_u5Set : IsOpen u5Set := by
  have hu : IsOpen {q : Coord5 | q.u ≠ 0} :=
    isOpen_ne_fun continuous_coord5_u continuous_const
  have hv : IsOpen {q : Coord5 | q.v ≠ 0} :=
    isOpen_ne_fun continuous_coord5_v continuous_const
  have hw : IsOpen {q : Coord5 | q.w ≠ 0} :=
    isOpen_ne_fun continuous_coord5_w continuous_const
  have hx : IsOpen {q : Coord5 | q.x ≠ 0} :=
    isOpen_ne_fun continuous_coord5_x continuous_const
  have hy : IsOpen {q : Coord5 | q.y ≠ 0} :=
    isOpen_ne_fun continuous_coord5_y continuous_const
  have hp0 : IsOpen {q : Coord5 | p0 q ≠ 0} :=
    isOpen_ne_fun continuous_p0 continuous_const
  have hp1 : IsOpen {q : Coord5 | p1 q ≠ 0} :=
    isOpen_ne_fun continuous_p1 continuous_const
  have hp2 : IsOpen {q : Coord5 | p2 q ≠ 0} :=
    isOpen_ne_fun continuous_p2 continuous_const
  have hp3 : IsOpen {q : Coord5 | p3 q ≠ 0} :=
    isOpen_ne_fun continuous_p3 continuous_const
  have hp4 : IsOpen {q : Coord5 | p4 q ≠ 0} :=
    isOpen_ne_fun continuous_p4 continuous_const
  rw [show u5Set = {q : Coord5 | q.u ≠ 0} ∩
      ({q : Coord5 | q.v ≠ 0} ∩ ({q : Coord5 | q.w ≠ 0} ∩
      ({q : Coord5 | q.x ≠ 0} ∩ ({q : Coord5 | q.y ≠ 0} ∩
      ({q : Coord5 | p0 q ≠ 0} ∩ ({q : Coord5 | p1 q ≠ 0} ∩
      ({q : Coord5 | p2 q ≠ 0} ∩
      ({q : Coord5 | p3 q ≠ 0} ∩ {q : Coord5 | p4 q ≠ 0})))))))) by
    ext q
    constructor
    · intro h
      exact ⟨h.u_ne, h.v_ne, h.w_ne, h.x_ne, h.y_ne, h.p0_ne,
        h.p1_ne, h.p2_ne, h.p3_ne, h.p4_ne⟩
    · rintro ⟨huq, hvq, hwq, hxq, hyq, hp0q, hp1q, hp2q, hp3q, hp4q⟩
      exact ⟨huq, hvq, hwq, hxq, hyq, hp0q, hp1q, hp2q, hp3q, hp4q⟩]
  exact hu.inter (hv.inter (hw.inter (hx.inter (hy.inter
    (hp0.inter (hp1.inter (hp2.inter (hp3.inter hp4))))))))

/-- The normalized generic five-point locus. -/
abbrev U5 := {q : Coord5 // IsU5 q}

/-- The normalized five-point skew Gram matrix. -/
def matrix5 (q : Coord5) : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0, 1, 1, 1, 1;
     -1, 0, 1, q.u, q.v;
     -1, -1, 0, q.w, q.x;
     -1, -q.u, -q.w, 0, q.y;
     -1, -q.v, -q.x, -q.y, 0]

/-- Delete one row and column from a five-by-five matrix, preserving order. -/
def principal4Of5 (A : Matrix (Fin 5) (Fin 5) ℂ) (skip : Fin 5) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => A (skip.succAbove i) (skip.succAbove j)

/-- Exact list of the five principal Pfaffians, deletion index zero. -/
@[simp]
theorem pfaffian4_principal4Of5_zero (q : Coord5) :
    pfaffian4 (principal4Of5 (matrix5 q) 0) = p0 q := by
  simp [pfaffian4, principal4Of5, matrix5, p0, Fin.succAbove]

/-- Exact list of the five principal Pfaffians, deletion index one. -/
@[simp]
theorem pfaffian4_principal4Of5_one (q : Coord5) :
    pfaffian4 (principal4Of5 (matrix5 q) 1) = p1 q := by
  simp [pfaffian4, principal4Of5, matrix5, p1, Fin.succAbove]

/-- Exact list of the five principal Pfaffians, deletion index two. -/
@[simp]
theorem pfaffian4_principal4Of5_two (q : Coord5) :
    pfaffian4 (principal4Of5 (matrix5 q) 2) = p2 q := by
  simp [pfaffian4, principal4Of5, matrix5, p2, Fin.succAbove]

/-- Exact list of the five principal Pfaffians, deletion index three. -/
@[simp]
theorem pfaffian4_principal4Of5_three (q : Coord5) :
    pfaffian4 (principal4Of5 (matrix5 q) 3) = p3 q := by
  simp [pfaffian4, principal4Of5, matrix5, p3, Fin.succAbove]

/-- Exact list of the five principal Pfaffians, deletion index four. -/
@[simp]
theorem pfaffian4_principal4Of5_four (q : Coord5) :
    pfaffian4 (principal4Of5 (matrix5 q) 4) = p4 q := by
  simp [pfaffian4, principal4Of5, matrix5, p4, Fin.succAbove]

/-! ## The five normalized four-point faces -/

def face4Coord0 (q : Coord5) : Coord4 :=
  ⟨q.u * q.x / (q.v * q.w), q.y / (q.v * q.w)⟩

def face4Coord1 (q : Coord5) : Coord4 :=
  ⟨q.x / q.w, q.y / q.w⟩

def face4Coord2 (q : Coord5) : Coord4 :=
  ⟨q.v / q.u, q.y / q.u⟩

def face4Coord3 (q : Coord5) : Coord4 :=
  ⟨q.v, q.x⟩

def face4Coord4 (q : Coord5) : Coord4 :=
  ⟨q.u, q.w⟩

theorem face4Coord0_mem (q : U5) : IsU4 (face4Coord0 q.1) := by
  have hd : q.1.v * q.1.w ≠ 0 := mul_ne_zero q.2.v_ne q.2.w_ne
  refine ⟨div_ne_zero (mul_ne_zero q.2.u_ne q.2.x_ne) hd,
    div_ne_zero q.2.y_ne hd, ?_⟩
  have hdelta : delta4 (face4Coord0 q.1) = p0 q.1 / (q.1.v * q.1.w) := by
    dsimp [delta4, face4Coord0, p0]
    field_simp [q.2.v_ne, q.2.w_ne]
    ring
  rw [hdelta]
  exact div_ne_zero q.2.p0_ne hd

theorem face4Coord1_mem (q : U5) : IsU4 (face4Coord1 q.1) := by
  refine ⟨div_ne_zero q.2.x_ne q.2.w_ne, div_ne_zero q.2.y_ne q.2.w_ne, ?_⟩
  have hdelta : delta4 (face4Coord1 q.1) = p1 q.1 / q.1.w := by
    dsimp [delta4, face4Coord1, p1]
    field_simp [q.2.w_ne]
    ring
  rw [hdelta]
  exact div_ne_zero q.2.p1_ne q.2.w_ne

theorem face4Coord2_mem (q : U5) : IsU4 (face4Coord2 q.1) := by
  refine ⟨div_ne_zero q.2.v_ne q.2.u_ne, div_ne_zero q.2.y_ne q.2.u_ne, ?_⟩
  have hdelta : delta4 (face4Coord2 q.1) = p2 q.1 / q.1.u := by
    dsimp [delta4, face4Coord2, p2]
    field_simp [q.2.u_ne]
    ring
  rw [hdelta]
  exact div_ne_zero q.2.p2_ne q.2.u_ne

theorem face4Coord3_mem (q : U5) : IsU4 (face4Coord3 q.1) := by
  refine ⟨q.2.v_ne, q.2.x_ne, ?_⟩
  have h : delta4 (face4Coord3 q.1) = p3 q.1 := by
    dsimp [delta4, face4Coord3, p3]
    ring
  rw [h]
  exact q.2.p3_ne

theorem face4Coord4_mem (q : U5) : IsU4 (face4Coord4 q.1) := by
  refine ⟨q.2.u_ne, q.2.w_ne, ?_⟩
  have h : delta4 (face4Coord4 q.1) = p4 q.1 := by
    dsimp [delta4, face4Coord4, p4]
    ring
  rw [h]
  exact q.2.p4_ne

/-- The five total normalized face maps on the generic subtype. -/
def face4_0 (q : U5) : U4 := ⟨face4Coord0 q.1, face4Coord0_mem q⟩
def face4_1 (q : U5) : U4 := ⟨face4Coord1 q.1, face4Coord1_mem q⟩
def face4_2 (q : U5) : U4 := ⟨face4Coord2 q.1, face4Coord2_mem q⟩
def face4_3 (q : U5) : U4 := ⟨face4Coord3 q.1, face4Coord3_mem q⟩
def face4_4 (q : U5) : U4 := ⟨face4Coord4 q.1, face4Coord4_mem q⟩

/-! ## Six-point coordinates and the Pfaffian hypersurface -/

/-- Ambient affine coordinates for the normalized six-point Gram matrix. -/
@[ext]
structure Coord6 where
  u : ℂ
  v : ℂ
  s : ℂ
  w : ℂ
  x : ℂ
  t : ℂ
  y : ℂ
  z : ℂ
  r : ℂ
deriving DecidableEq

/-- Coordinate identification with the standard nine-dimensional complex affine
space.  The Pfaffian equation is imposed only by the subtype `U6`. -/
def coord6EquivFun : Coord6 ≃ (Fin 9 → ℂ) where
  toFun q := ![q.u, q.v, q.s, q.w, q.x, q.t, q.y, q.z, q.r]
  invFun q := ⟨q 0, q 1, q 2, q 3, q 4, q 5, q 6, q 7, q 8⟩
  left_inv q := by ext <;> simp
  right_inv q := by
    funext i
    fin_cases i <;> simp

instance : NormedAddCommGroup Coord6 := coord6EquivFun.normedAddCommGroup

instance : Module ℂ Coord6 := coord6EquivFun.module ℂ

instance : NormedSpace ℂ Coord6 := coord6EquivFun.normedSpace ℂ

def coord6LinearEquivFun : Coord6 ≃ₗ[ℂ] (Fin 9 → ℂ) :=
  { coord6EquivFun with
    map_add' := by
      intro q r
      funext i
      fin_cases i <;> rfl
    map_smul' := by
      intro c q
      funext i
      fin_cases i <;> rfl }

def coord6LinearIsometryEquivFun : Coord6 ≃ₗᵢ[ℂ] (Fin 9 → ℂ) :=
  LinearIsometryEquiv.mk coord6LinearEquivFun (by
    intro q
    simp only [coord6LinearEquivFun]
    rfl)

instance : CompleteSpace Coord6 :=
  coord6LinearIsometryEquivFun.toIsometryEquiv.completeSpace

instance : MeasurableSpace Coord6 := borel Coord6

instance : BorelSpace Coord6 := ⟨rfl⟩

def coord6HomeomorphFun : Coord6 ≃ₜ (Fin 9 → ℂ) :=
  coord6EquivFun.homeomorph

@[continuity, fun_prop] theorem continuous_coord6_u : Continuous fun q : Coord6 => q.u := by
  change Continuous fun q : Coord6 => coord6HomeomorphFun q 0
  exact (continuous_apply 0).comp coord6HomeomorphFun.continuous

@[continuity, fun_prop] theorem continuous_coord6_v : Continuous fun q : Coord6 => q.v := by
  change Continuous fun q : Coord6 => coord6HomeomorphFun q 1
  exact (continuous_apply 1).comp coord6HomeomorphFun.continuous

@[continuity, fun_prop] theorem continuous_coord6_s : Continuous fun q : Coord6 => q.s := by
  change Continuous fun q : Coord6 => coord6HomeomorphFun q 2
  exact (continuous_apply 2).comp coord6HomeomorphFun.continuous

@[continuity, fun_prop] theorem continuous_coord6_w : Continuous fun q : Coord6 => q.w := by
  change Continuous fun q : Coord6 => coord6HomeomorphFun q 3
  exact (continuous_apply 3).comp coord6HomeomorphFun.continuous

@[continuity, fun_prop] theorem continuous_coord6_x : Continuous fun q : Coord6 => q.x := by
  change Continuous fun q : Coord6 => coord6HomeomorphFun q 4
  exact (continuous_apply 4).comp coord6HomeomorphFun.continuous

@[continuity, fun_prop] theorem continuous_coord6_t : Continuous fun q : Coord6 => q.t := by
  change Continuous fun q : Coord6 => coord6HomeomorphFun q 5
  exact (continuous_apply 5).comp coord6HomeomorphFun.continuous

@[continuity, fun_prop] theorem continuous_coord6_y : Continuous fun q : Coord6 => q.y := by
  change Continuous fun q : Coord6 => coord6HomeomorphFun q 6
  exact (continuous_apply 6).comp coord6HomeomorphFun.continuous

@[continuity, fun_prop] theorem continuous_coord6_z : Continuous fun q : Coord6 => q.z := by
  change Continuous fun q : Coord6 => coord6HomeomorphFun q 7
  exact (continuous_apply 7).comp coord6HomeomorphFun.continuous

@[continuity, fun_prop] theorem continuous_coord6_r : Continuous fun q : Coord6 => q.r := by
  change Continuous fun q : Coord6 => coord6HomeomorphFun q 8
  exact (continuous_apply 8).comp coord6HomeomorphFun.continuous

def pf0123 (q : Coord6) : ℂ := q.w - q.u + 1
def pf0124 (q : Coord6) : ℂ := q.x - q.v + 1
def pf0125 (q : Coord6) : ℂ := q.t - q.s + 1
def pf0134 (q : Coord6) : ℂ := q.y - q.v + q.u
def pf0135 (q : Coord6) : ℂ := q.z - q.s + q.u
def pf0145 (q : Coord6) : ℂ := q.r - q.s + q.v
def pf0234 (q : Coord6) : ℂ := q.y - q.x + q.w
def pf0235 (q : Coord6) : ℂ := q.z - q.t + q.w
def pf0245 (q : Coord6) : ℂ := q.r - q.t + q.x
def pf0345 (q : Coord6) : ℂ := q.r - q.z + q.y
def pf1234 (q : Coord6) : ℂ := q.y - q.u * q.x + q.v * q.w
def pf1235 (q : Coord6) : ℂ := q.z - q.u * q.t + q.s * q.w
def pf1245 (q : Coord6) : ℂ := q.r - q.v * q.t + q.s * q.x
def pf1345 (q : Coord6) : ℂ := q.u * q.r - q.v * q.z + q.s * q.y
def pf2345 (q : Coord6) : ℂ := q.w * q.r - q.x * q.z + q.t * q.y

/-- The six-by-six Pfaffian hypersurface polynomial from the article. -/
def pi6 (q : Coord6) : ℂ :=
  -q.r * q.u + q.r * q.w + q.r - q.s * q.w + q.s * q.x - q.s * q.y +
    q.t * q.u - q.t * q.v + q.t * q.y - q.u * q.x + q.v * q.w +
    q.v * q.z - q.x * q.z + q.y - q.z

/-- The numerator obtained by solving the six-point Pfaffian equation for `r`. -/
def rNumerator (q : Coord6) : ℂ :=
  q.s * q.w - q.s * q.x + q.s * q.y - q.t * q.u + q.t * q.v -
    q.t * q.y + q.u * q.x - q.v * q.w - q.v * q.z + q.x * q.z - q.y + q.z

/-- The Pfaffian equation is linear in the last coordinate, with coefficient
the leading principal Pfaffian. -/
theorem pi6_eq_r_mul_pf0123_sub (q : Coord6) :
    pi6 q = q.r * pf0123 q - rNumerator q := by
  simp only [pi6, pf0123, rNumerator]
  ring

/-- Exact multiplication-back and uniqueness certificate for elimination of `r`.
The forward implication solves `Π = 0`; the reverse implication verifies the
displayed rational solution by substitution. -/
theorem pi6_eq_zero_iff_r_eq_div (q : Coord6) (hden : pf0123 q ≠ 0) :
    pi6 q = 0 ↔ q.r = rNumerator q / pf0123 q := by
  rw [pi6_eq_r_mul_pf0123_sub]
  constructor
  · intro h
    apply (eq_div_iff hden).2
    exact sub_eq_zero.mp h
  · intro h
    apply sub_eq_zero.mpr
    exact (eq_div_iff hden).mp h

/-- The normalized six-point skew Gram matrix. -/
def matrix6 (q : Coord6) : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, 1, 1, 1, 1, 1;
     -1, 0, 1, q.u, q.v, q.s;
     -1, -1, 0, q.w, q.x, q.t;
     -1, -q.u, -q.w, 0, q.y, q.z;
     -1, -q.v, -q.x, -q.y, 0, q.r;
     -1, -q.s, -q.t, -q.z, -q.r, 0]

/-- The ordered Pfaffian of a selected four-by-four principal block. -/
def pfaffian4At6 (A : Matrix (Fin 6) (Fin 6) ℂ)
    (i j k l : Fin 6) : ℂ :=
  A i j * A k l - A i k * A j l + A i l * A j k

/-- Recursive first-row formula for a six-by-six Pfaffian. -/
def pfaffian6 (A : Matrix (Fin 6) (Fin 6) ℂ) : ℂ :=
  A 0 1 * (A 2 3 * A 4 5 - A 2 4 * A 3 5 + A 2 5 * A 3 4) -
  A 0 2 * (A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4) +
  A 0 3 * (A 1 2 * A 4 5 - A 1 4 * A 2 5 + A 1 5 * A 2 4) -
  A 0 4 * (A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3) +
  A 0 5 * (A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3)

/-- Exact six-point Pfaffian certificate. -/
@[simp]
theorem pfaffian6_matrix6 (q : Coord6) : pfaffian6 (matrix6 q) = pi6 q := by
  simp [pfaffian6, matrix6, pi6]
  ring

/-- Predicate cutting out the normalized generic rank-four six-point locus. -/
structure IsU6 (q : Coord6) : Prop where
  u_ne : q.u ≠ 0
  v_ne : q.v ≠ 0
  s_ne : q.s ≠ 0
  w_ne : q.w ≠ 0
  x_ne : q.x ≠ 0
  t_ne : q.t ≠ 0
  y_ne : q.y ≠ 0
  z_ne : q.z ≠ 0
  r_ne : q.r ≠ 0
  pi_zero : pi6 q = 0
  pf0123_ne : pf0123 q ≠ 0
  pf0124_ne : pf0124 q ≠ 0
  pf0125_ne : pf0125 q ≠ 0
  pf0134_ne : pf0134 q ≠ 0
  pf0135_ne : pf0135 q ≠ 0
  pf0145_ne : pf0145 q ≠ 0
  pf0234_ne : pf0234 q ≠ 0
  pf0235_ne : pf0235 q ≠ 0
  pf0245_ne : pf0245 q ≠ 0
  pf0345_ne : pf0345 q ≠ 0
  pf1234_ne : pf1234 q ≠ 0
  pf1235_ne : pf1235 q ≠ 0
  pf1245_ne : pf1245 q ≠ 0
  pf1345_ne : pf1345 q ≠ 0
  pf2345_ne : pf2345 q ≠ 0

/-- Product of every nonvanishing coordinate and principal Pfaffian used to
define the generic six-point locus.  Packaging the open conditions in one
polynomial is convenient when `U6` is parametrized by its eight-dimensional
Pfaffian graph. -/
def u6Discriminant (q : Coord6) : ℂ :=
  q.u * q.v * q.s * q.w * q.x * q.t * q.y * q.z * q.r *
    pf0123 q * pf0124 q * pf0125 q * pf0134 q * pf0135 q *
    pf0145 q * pf0234 q * pf0235 q * pf0245 q * pf0345 q *
    pf1234 q * pf1235 q * pf1245 q * pf1345 q * pf2345 q

@[continuity, fun_prop]
theorem continuous_u6Discriminant : Continuous u6Discriminant := by
  fun_prop [u6Discriminant, pf0123, pf0124, pf0125, pf0134, pf0135,
    pf0145, pf0234, pf0235, pf0245, pf0345, pf1234, pf1235,
    pf1245, pf1345, pf2345]

theorem u6Discriminant_ne_iff (q : Coord6) :
    u6Discriminant q ≠ 0 ↔
      q.u ≠ 0 ∧ q.v ≠ 0 ∧ q.s ≠ 0 ∧ q.w ≠ 0 ∧ q.x ≠ 0 ∧
      q.t ≠ 0 ∧ q.y ≠ 0 ∧ q.z ≠ 0 ∧ q.r ≠ 0 ∧
      pf0123 q ≠ 0 ∧ pf0124 q ≠ 0 ∧ pf0125 q ≠ 0 ∧
      pf0134 q ≠ 0 ∧ pf0135 q ≠ 0 ∧ pf0145 q ≠ 0 ∧
      pf0234 q ≠ 0 ∧ pf0235 q ≠ 0 ∧ pf0245 q ≠ 0 ∧
      pf0345 q ≠ 0 ∧ pf1234 q ≠ 0 ∧ pf1235 q ≠ 0 ∧
      pf1245 q ≠ 0 ∧ pf1345 q ≠ 0 ∧ pf2345 q ≠ 0 := by
  simp only [u6Discriminant, mul_ne_zero_iff, and_assoc]

theorem IsU6.discriminant_ne {q : Coord6} (hq : IsU6 q) :
    u6Discriminant q ≠ 0 := by
  rw [u6Discriminant_ne_iff]
  exact ⟨hq.u_ne, hq.v_ne, hq.s_ne, hq.w_ne, hq.x_ne, hq.t_ne,
    hq.y_ne, hq.z_ne, hq.r_ne, hq.pf0123_ne, hq.pf0124_ne,
    hq.pf0125_ne, hq.pf0134_ne, hq.pf0135_ne, hq.pf0145_ne,
    hq.pf0234_ne, hq.pf0235_ne, hq.pf0245_ne, hq.pf0345_ne,
    hq.pf1234_ne, hq.pf1235_ne, hq.pf1245_ne, hq.pf1345_ne,
    hq.pf2345_ne⟩

theorem isU6_of_pi6_eq_zero_of_discriminant_ne {q : Coord6}
    (hpi : pi6 q = 0) (hdisc : u6Discriminant q ≠ 0) : IsU6 q := by
  rw [u6Discriminant_ne_iff] at hdisc
  rcases hdisc with
    ⟨hu, hv, hs, hw, hx, ht, hy, hz, hr, h0123, h0124, h0125,
      h0134, h0135, h0145, h0234, h0235, h0245, h0345,
      h1234, h1235, h1245, h1345, h2345⟩
  exact ⟨hu, hv, hs, hw, hx, ht, hy, hz, hr, hpi, h0123, h0124,
    h0125, h0134, h0135, h0145, h0234, h0235, h0245, h0345,
    h1234, h1235, h1245, h1345, h2345⟩

/-- The normalized generic six-point Pfaffian locus. -/
abbrev U6 := {q : Coord6 // IsU6 q}

/-- On the generic six-point locus the last coordinate is the advertised rational
function of the other eight coordinates. -/
theorem r_elimination (q : U6) :
    q.1.r = rNumerator q.1 / pf0123 q.1 :=
  (pi6_eq_zero_iff_r_eq_div q.1 q.2.pf0123_ne).mp q.2.pi_zero

/-! ### The six normalized five-point faces -/

def face5Coord0 (q : Coord6) : Coord5 :=
  ⟨q.u * q.x / (q.v * q.w), q.u * q.t / (q.w * q.s),
   q.y / (q.v * q.w), q.z / (q.w * q.s),
   q.r * q.u / (q.v * q.w * q.s)⟩

def face5Coord1 (q : Coord6) : Coord5 :=
  ⟨q.x / q.w, q.t / q.w, q.y / q.w, q.z / q.w, q.r / q.w⟩

def face5Coord2 (q : Coord6) : Coord5 :=
  ⟨q.v / q.u, q.s / q.u, q.y / q.u, q.z / q.u, q.r / q.u⟩

def face5Coord3 (q : Coord6) : Coord5 := ⟨q.v, q.s, q.x, q.t, q.r⟩
def face5Coord4 (q : Coord6) : Coord5 := ⟨q.u, q.s, q.w, q.t, q.z⟩
def face5Coord5 (q : Coord6) : Coord5 := ⟨q.u, q.v, q.w, q.x, q.y⟩

theorem face5Coord3_mem (q : U6) : IsU5 (face5Coord3 q.1) := by
  refine ⟨q.2.v_ne, q.2.s_ne, q.2.x_ne, q.2.t_ne, q.2.r_ne, ?_, ?_, ?_, ?_, ?_⟩
  · exact q.2.pf1245_ne
  · exact q.2.pf0245_ne
  · exact q.2.pf0145_ne
  · exact q.2.pf0125_ne
  · exact q.2.pf0124_ne

theorem face5Coord4_mem (q : U6) : IsU5 (face5Coord4 q.1) := by
  refine ⟨q.2.u_ne, q.2.s_ne, q.2.w_ne, q.2.t_ne, q.2.z_ne, ?_, ?_, ?_, ?_, ?_⟩
  · exact q.2.pf1235_ne
  · exact q.2.pf0235_ne
  · exact q.2.pf0135_ne
  · exact q.2.pf0125_ne
  · exact q.2.pf0123_ne

theorem face5Coord5_mem (q : U6) : IsU5 (face5Coord5 q.1) := by
  refine ⟨q.2.u_ne, q.2.v_ne, q.2.w_ne, q.2.x_ne, q.2.y_ne, ?_, ?_, ?_, ?_, ?_⟩
  · exact q.2.pf1234_ne
  · exact q.2.pf0234_ne
  · exact q.2.pf0134_ne
  · exact q.2.pf0124_ne
  · exact q.2.pf0123_ne

private theorem left_ne_of_mul_eq_ne {a d n : ℂ} (h : a * d = n) (hn : n ≠ 0) : a ≠ 0 := by
  intro ha
  apply hn
  rw [← h, ha, zero_mul]

theorem face5Coord2_mem (q : U6) : IsU5 (face5Coord2 q.1) := by
  refine ⟨div_ne_zero q.2.v_ne q.2.u_ne, div_ne_zero q.2.s_ne q.2.u_ne,
    div_ne_zero q.2.y_ne q.2.u_ne, div_ne_zero q.2.z_ne q.2.u_ne,
    div_ne_zero q.2.r_ne q.2.u_ne, ?_, ?_, ?_, ?_, ?_⟩
  · have h : p0 (face5Coord2 q.1) * q.1.u ^ 2 = pf1345 q.1 := by
      dsimp [p0, face5Coord2, pf1345]
      field_simp [q.2.u_ne]
    exact left_ne_of_mul_eq_ne h q.2.pf1345_ne
  · have h : p1 (face5Coord2 q.1) * q.1.u = pf0345 q.1 := by
      dsimp [p1, face5Coord2, pf0345]
      field_simp [q.2.u_ne]
    exact left_ne_of_mul_eq_ne h q.2.pf0345_ne
  · have h : p2 (face5Coord2 q.1) * q.1.u = pf0145 q.1 := by
      dsimp [p2, face5Coord2, pf0145]
      field_simp [q.2.u_ne]
    exact left_ne_of_mul_eq_ne h q.2.pf0145_ne
  · have h : p3 (face5Coord2 q.1) * q.1.u = pf0135 q.1 := by
      dsimp [p3, face5Coord2, pf0135]
      field_simp [q.2.u_ne]
    exact left_ne_of_mul_eq_ne h q.2.pf0135_ne
  · have h : p4 (face5Coord2 q.1) * q.1.u = pf0134 q.1 := by
      dsimp [p4, face5Coord2, pf0134]
      field_simp [q.2.u_ne]
    exact left_ne_of_mul_eq_ne h q.2.pf0134_ne

theorem face5Coord1_mem (q : U6) : IsU5 (face5Coord1 q.1) := by
  refine ⟨div_ne_zero q.2.x_ne q.2.w_ne, div_ne_zero q.2.t_ne q.2.w_ne,
    div_ne_zero q.2.y_ne q.2.w_ne, div_ne_zero q.2.z_ne q.2.w_ne,
    div_ne_zero q.2.r_ne q.2.w_ne, ?_, ?_, ?_, ?_, ?_⟩
  · have h : p0 (face5Coord1 q.1) * q.1.w ^ 2 = pf2345 q.1 := by
      dsimp [p0, face5Coord1, pf2345]
      field_simp [q.2.w_ne]
    exact left_ne_of_mul_eq_ne h q.2.pf2345_ne
  · have h : p1 (face5Coord1 q.1) * q.1.w = pf0345 q.1 := by
      dsimp [p1, face5Coord1, pf0345]
      field_simp [q.2.w_ne]
    exact left_ne_of_mul_eq_ne h q.2.pf0345_ne
  · have h : p2 (face5Coord1 q.1) * q.1.w = pf0245 q.1 := by
      dsimp [p2, face5Coord1, pf0245]
      field_simp [q.2.w_ne]
    exact left_ne_of_mul_eq_ne h q.2.pf0245_ne
  · have h : p3 (face5Coord1 q.1) * q.1.w = pf0235 q.1 := by
      dsimp [p3, face5Coord1, pf0235]
      field_simp [q.2.w_ne]
    exact left_ne_of_mul_eq_ne h q.2.pf0235_ne
  · have h : p4 (face5Coord1 q.1) * q.1.w = pf0234 q.1 := by
      dsimp [p4, face5Coord1, pf0234]
      field_simp [q.2.w_ne]
    exact left_ne_of_mul_eq_ne h q.2.pf0234_ne

theorem face5Coord0_mem (q : U6) : IsU5 (face5Coord0 q.1) := by
  refine ⟨div_ne_zero (mul_ne_zero q.2.u_ne q.2.x_ne)
      (mul_ne_zero q.2.v_ne q.2.w_ne),
    div_ne_zero (mul_ne_zero q.2.u_ne q.2.t_ne)
      (mul_ne_zero q.2.w_ne q.2.s_ne),
    div_ne_zero q.2.y_ne (mul_ne_zero q.2.v_ne q.2.w_ne),
    div_ne_zero q.2.z_ne (mul_ne_zero q.2.w_ne q.2.s_ne),
    div_ne_zero (mul_ne_zero q.2.r_ne q.2.u_ne)
      (mul_ne_zero (mul_ne_zero q.2.v_ne q.2.w_ne) q.2.s_ne), ?_, ?_, ?_, ?_, ?_⟩
  · have h : p0 (face5Coord0 q.1) * (q.1.v * q.1.w ^ 2 * q.1.s) =
        q.1.u * pf2345 q.1 := by
      dsimp [p0, face5Coord0, pf2345]
      field_simp [q.2.v_ne, q.2.w_ne, q.2.s_ne]
    exact left_ne_of_mul_eq_ne h (mul_ne_zero q.2.u_ne q.2.pf2345_ne)
  · have h : p1 (face5Coord0 q.1) * (q.1.v * q.1.w * q.1.s) =
        pf1345 q.1 := by
      dsimp [p1, face5Coord0, pf1345]
      field_simp [q.2.v_ne, q.2.w_ne, q.2.s_ne]
    exact left_ne_of_mul_eq_ne h q.2.pf1345_ne
  · have h : p2 (face5Coord0 q.1) * (q.1.v * q.1.w * q.1.s) =
        q.1.u * pf1245 q.1 := by
      dsimp [p2, face5Coord0, pf1245]
      field_simp [q.2.v_ne, q.2.w_ne, q.2.s_ne]
    exact left_ne_of_mul_eq_ne h (mul_ne_zero q.2.u_ne q.2.pf1245_ne)
  · have h : p3 (face5Coord0 q.1) * (q.1.w * q.1.s) = pf1235 q.1 := by
      dsimp [p3, face5Coord0, pf1235]
      field_simp [q.2.w_ne, q.2.s_ne]
    exact left_ne_of_mul_eq_ne h q.2.pf1235_ne
  · have h : p4 (face5Coord0 q.1) * (q.1.v * q.1.w) = pf1234 q.1 := by
      dsimp [p4, face5Coord0, pf1234]
      field_simp [q.2.v_ne, q.2.w_ne]
    exact left_ne_of_mul_eq_ne h q.2.pf1234_ne

/-- The six total normalized face maps on the generic six-point subtype. -/
def face5_0 (q : U6) : U5 := ⟨face5Coord0 q.1, face5Coord0_mem q⟩
def face5_1 (q : U6) : U5 := ⟨face5Coord1 q.1, face5Coord1_mem q⟩
def face5_2 (q : U6) : U5 := ⟨face5Coord2 q.1, face5Coord2_mem q⟩
def face5_3 (q : U6) : U5 := ⟨face5Coord3 q.1, face5Coord3_mem q⟩
def face5_4 (q : U6) : U5 := ⟨face5Coord4 q.1, face5Coord4_mem q⟩
def face5_5 (q : U6) : U5 := ⟨face5Coord5 q.1, face5Coord5_mem q⟩

/-! ### Twice-deletion certificates

For `i < j`, deleting `j` and then `i` agrees with deleting `i` and then the
shifted index `j - 1`.  These are the coordinate transports of
`FinTuple.delete_delete_swap`; keeping them as named certificates lets the proof of
`E D = 0` use only simplicial cancellation.
-/

theorem face4_0_face5_1 (q : U6) :
    face4_0 (face5_1 q) = face4_0 (face5_0 q) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [face4_0, face4Coord0, face5_1, face5Coord1, face5_0, face5Coord0] <;>
    field_simp [q.2.u_ne, q.2.v_ne, q.2.s_ne, q.2.w_ne, q.2.x_ne, q.2.t_ne,
      q.2.y_ne, q.2.z_ne, q.2.r_ne]

theorem face4_0_face5_2 (q : U6) :
    face4_0 (face5_2 q) = face4_1 (face5_0 q) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [face4_0, face4Coord0, face5_2, face5Coord2,
      face4_1, face4Coord1, face5_0, face5Coord0] <;>
    field_simp [q.2.u_ne, q.2.v_ne, q.2.s_ne, q.2.w_ne, q.2.x_ne, q.2.t_ne,
      q.2.y_ne, q.2.z_ne, q.2.r_ne]

theorem face4_0_face5_3 (q : U6) :
    face4_0 (face5_3 q) = face4_2 (face5_0 q) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [face4_0, face4Coord0, face5_3, face5Coord3,
      face4_2, face4Coord2, face5_0, face5Coord0] <;>
    field_simp [q.2.u_ne, q.2.v_ne, q.2.s_ne, q.2.w_ne, q.2.x_ne, q.2.t_ne,
      q.2.y_ne, q.2.z_ne, q.2.r_ne]

theorem face4_0_face5_4 (q : U6) :
    face4_0 (face5_4 q) = face4_3 (face5_0 q) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [face4_0, face4Coord0, face5_4, face5Coord4,
      face4_3, face4Coord3, face5_0, face5Coord0] <;>
    field_simp [q.2.u_ne, q.2.v_ne, q.2.s_ne, q.2.w_ne, q.2.x_ne, q.2.t_ne,
      q.2.y_ne, q.2.z_ne, q.2.r_ne]

theorem face4_0_face5_5 (q : U6) :
    face4_0 (face5_5 q) = face4_4 (face5_0 q) := by
  rfl

theorem face4_1_face5_2 (q : U6) :
    face4_1 (face5_2 q) = face4_1 (face5_1 q) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [face4_1, face4Coord1, face5_2, face5Coord2, face5_1, face5Coord1] <;>
    field_simp [q.2.u_ne, q.2.v_ne, q.2.s_ne, q.2.w_ne, q.2.x_ne, q.2.t_ne,
      q.2.y_ne, q.2.z_ne, q.2.r_ne]

theorem face4_1_face5_3 (q : U6) :
    face4_1 (face5_3 q) = face4_2 (face5_1 q) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [face4_1, face4Coord1, face5_3, face5Coord3,
      face4_2, face4Coord2, face5_1, face5Coord1] <;>
    field_simp [q.2.u_ne, q.2.v_ne, q.2.s_ne, q.2.w_ne, q.2.x_ne, q.2.t_ne,
      q.2.y_ne, q.2.z_ne, q.2.r_ne]

theorem face4_1_face5_4 (q : U6) :
    face4_1 (face5_4 q) = face4_3 (face5_1 q) := by
  rfl

theorem face4_1_face5_5 (q : U6) :
    face4_1 (face5_5 q) = face4_4 (face5_1 q) := by
  rfl

theorem face4_2_face5_3 (q : U6) :
    face4_2 (face5_3 q) = face4_2 (face5_2 q) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [face4_2, face4Coord2, face5_3, face5Coord3, face5_2, face5Coord2] <;>
    field_simp [q.2.u_ne, q.2.v_ne, q.2.s_ne, q.2.w_ne, q.2.x_ne, q.2.t_ne,
      q.2.y_ne, q.2.z_ne, q.2.r_ne]

theorem face4_2_face5_4 (q : U6) :
    face4_2 (face5_4 q) = face4_3 (face5_2 q) := by
  rfl

theorem face4_2_face5_5 (q : U6) :
    face4_2 (face5_5 q) = face4_4 (face5_2 q) := by
  rfl

theorem face4_3_face5_4 (q : U6) :
    face4_3 (face5_4 q) = face4_3 (face5_3 q) := by
  rfl

theorem face4_3_face5_5 (q : U6) :
    face4_3 (face5_5 q) = face4_4 (face5_3 q) := by
  rfl

theorem face4_4_face5_5 (q : U6) :
    face4_4 (face5_5 q) = face4_4 (face5_4 q) := by
  rfl

end

end Pfaffian

end Sp4
