import Sp4.Pfaffian.Operators

/-!
# Exact Pfaffian certificates

Every identity in this file is checked by the Lean kernel from the displayed rational
formulas.  It imports no cohomology.
-/

namespace Sp4

namespace Pfaffian

noncomputable section

open Filter

/-! ## The fifteen principal four-by-four Pfaffians of the six-point matrix -/

@[simp] theorem pfaffian4At6_0123 (q : Coord6) :
    pfaffian4At6 (matrix6 q) 0 1 2 3 = pf0123 q := by
  simp [pfaffian4At6, matrix6, pf0123]

@[simp] theorem pfaffian4At6_0124 (q : Coord6) :
    pfaffian4At6 (matrix6 q) 0 1 2 4 = pf0124 q := by
  simp [pfaffian4At6, matrix6, pf0124]

@[simp] theorem pfaffian4At6_0125 (q : Coord6) :
    pfaffian4At6 (matrix6 q) 0 1 2 5 = pf0125 q := by
  simp [pfaffian4At6, matrix6, pf0125]

@[simp] theorem pfaffian4At6_0134 (q : Coord6) :
    pfaffian4At6 (matrix6 q) 0 1 3 4 = pf0134 q := by
  simp [pfaffian4At6, matrix6, pf0134]

@[simp] theorem pfaffian4At6_0135 (q : Coord6) :
    pfaffian4At6 (matrix6 q) 0 1 3 5 = pf0135 q := by
  simp [pfaffian4At6, matrix6, pf0135]

@[simp] theorem pfaffian4At6_0145 (q : Coord6) :
    pfaffian4At6 (matrix6 q) 0 1 4 5 = pf0145 q := by
  simp [pfaffian4At6, matrix6, pf0145]

@[simp] theorem pfaffian4At6_0234 (q : Coord6) :
    pfaffian4At6 (matrix6 q) 0 2 3 4 = pf0234 q := by
  simp [pfaffian4At6, matrix6, pf0234]

@[simp] theorem pfaffian4At6_0235 (q : Coord6) :
    pfaffian4At6 (matrix6 q) 0 2 3 5 = pf0235 q := by
  simp [pfaffian4At6, matrix6, pf0235]

@[simp] theorem pfaffian4At6_0245 (q : Coord6) :
    pfaffian4At6 (matrix6 q) 0 2 4 5 = pf0245 q := by
  simp [pfaffian4At6, matrix6, pf0245]

@[simp] theorem pfaffian4At6_0345 (q : Coord6) :
    pfaffian4At6 (matrix6 q) 0 3 4 5 = pf0345 q := by
  simp [pfaffian4At6, matrix6, pf0345]

@[simp] theorem pfaffian4At6_1234 (q : Coord6) :
    pfaffian4At6 (matrix6 q) 1 2 3 4 = pf1234 q := by
  simp [pfaffian4At6, matrix6, pf1234]

@[simp] theorem pfaffian4At6_1235 (q : Coord6) :
    pfaffian4At6 (matrix6 q) 1 2 3 5 = pf1235 q := by
  simp [pfaffian4At6, matrix6, pf1235]

@[simp] theorem pfaffian4At6_1245 (q : Coord6) :
    pfaffian4At6 (matrix6 q) 1 2 4 5 = pf1245 q := by
  simp [pfaffian4At6, matrix6, pf1245]

@[simp] theorem pfaffian4At6_1345 (q : Coord6) :
    pfaffian4At6 (matrix6 q) 1 3 4 5 = pf1345 q := by
  simp [pfaffian4At6, matrix6, pf1345]

@[simp] theorem pfaffian4At6_2345 (q : Coord6) :
    pfaffian4At6 (matrix6 q) 2 3 4 5 = pf2345 q := by
  simp [pfaffian4At6, matrix6, pf2345]

/-! The five nonidentity quotient-coordinate transformations. -/

def cyclicCoord (q : Coord4) : Coord4 := ⟨-1 / q.y, -q.x / q.y⟩
def cyclicSqCoord (q : Coord4) : Coord4 := ⟨q.y / q.x, -1 / q.x⟩
def oddXCoord (q : Coord4) : Coord4 := ⟨1 / q.x, -q.y / q.x⟩
def rhoCoord (q : Coord4) : Coord4 := ⟨-q.y, -q.x⟩
def oddYCoord (q : Coord4) : Coord4 := ⟨q.x / q.y, 1 / q.y⟩

/-! ## The permutation action table -/

/-- Simultaneously permute the rows and columns of a four-by-four matrix. -/
def reindex4 (σ : Equiv.Perm (Fin 4)) (A : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  fun i j => A (σ i) (σ j)

/-- The two normalized quotient coordinates extracted from a four-by-four Gram
matrix.  On generic Gram matrices the displayed denominator is nonzero. -/
def chi4 (A : Matrix (Fin 4) (Fin 4) ℂ) : Coord4 :=
  ⟨A 1 3 * A 0 2 / (A 1 2 * A 0 3),
    A 2 3 * A 0 1 / (A 1 2 * A 0 3)⟩

def permCyclic : Equiv.Perm (Fin 4) :=
  Equiv.swap (1 : Fin 4) 2 * Equiv.swap (2 : Fin 4) 3

def permCyclicSq : Equiv.Perm (Fin 4) :=
  Equiv.swap (2 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2

def permOddX : Equiv.Perm (Fin 4) := Equiv.swap (2 : Fin 4) 3
def permRho : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) 2
def permOddY : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) 3

/-- The three nonidentity elements of the Klein four subgroup. -/
def permKlein01_23 : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 1 * Equiv.swap (2 : Fin 4) 3

def permKlein02_13 : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 2 * Equiv.swap (1 : Fin 4) 3

def permKlein03_12 : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 3 * Equiv.swap (1 : Fin 4) 2

theorem chi4_matrix4 (q : Coord4) : chi4 (matrix4 q) = q := by
  apply Coord4.ext <;> simp [chi4, matrix4]

theorem chi4_reindex4_permCyclic (q : U4) :
    chi4 (reindex4 permCyclic (matrix4 q.1)) = cyclicCoord q.1 := by
  apply Coord4.ext <;>
    simp [chi4, reindex4, permCyclic, matrix4, cyclicCoord,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def]

theorem chi4_reindex4_permCyclicSq (q : U4) :
    chi4 (reindex4 permCyclicSq (matrix4 q.1)) = cyclicSqCoord q.1 := by
  apply Coord4.ext <;>
    simp [chi4, reindex4, permCyclicSq, matrix4, cyclicSqCoord,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    field_simp [q.2.x_ne]

theorem chi4_reindex4_permOddX (q : U4) :
    chi4 (reindex4 permOddX (matrix4 q.1)) = oddXCoord q.1 := by
  apply Coord4.ext <;>
    simp [chi4, reindex4, permOddX, matrix4, oddXCoord,
      Equiv.swap_apply_def]

theorem chi4_reindex4_permRho (q : U4) :
    chi4 (reindex4 permRho (matrix4 q.1)) = rhoCoord q.1 := by
  apply Coord4.ext <;>
    simp [chi4, reindex4, permRho, matrix4, rhoCoord, Equiv.swap_apply_def] <;>
    field_simp

theorem chi4_reindex4_permOddY (q : U4) :
    chi4 (reindex4 permOddY (matrix4 q.1)) = oddYCoord q.1 := by
  apply Coord4.ext <;>
    simp [chi4, reindex4, permOddY, matrix4, oddYCoord,
      Equiv.swap_apply_def]

theorem chi4_reindex4_permKlein01_23 (q : U4) :
    chi4 (reindex4 permKlein01_23 (matrix4 q.1)) = q.1 := by
  apply Coord4.ext <;>
    simp [chi4, reindex4, permKlein01_23, matrix4,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def]

theorem chi4_reindex4_permKlein02_13 (q : U4) :
    chi4 (reindex4 permKlein02_13 (matrix4 q.1)) = q.1 := by
  apply Coord4.ext <;>
    simp [chi4, reindex4, permKlein02_13, matrix4,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def]

theorem chi4_reindex4_permKlein03_12 (q : U4) :
    chi4 (reindex4 permKlein03_12 (matrix4 q.1)) = q.1 := by
  apply Coord4.ext <;>
    simp [chi4, reindex4, permKlein03_12, matrix4,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def]

theorem sign_permCyclic : Equiv.Perm.sign permCyclic = 1 := by decide
theorem sign_permCyclicSq : Equiv.Perm.sign permCyclicSq = 1 := by decide
theorem sign_permOddX : Equiv.Perm.sign permOddX = -1 := by decide
theorem sign_permRho : Equiv.Perm.sign permRho = -1 := by decide
theorem sign_permOddY : Equiv.Perm.sign permOddY = -1 := by decide
theorem sign_permKlein01_23 : Equiv.Perm.sign permKlein01_23 = 1 := by decide
theorem sign_permKlein02_13 : Equiv.Perm.sign permKlein02_13 = 1 := by decide
theorem sign_permKlein03_12 : Equiv.Perm.sign permKlein03_12 = 1 := by decide

/-! ## The sixfold coordinate symmetry of the four-point locus -/

theorem cyclicCoord_mem (q : U4) : IsU4 (cyclicCoord q.1) := by
  refine ⟨div_ne_zero (neg_ne_zero.mpr one_ne_zero) q.2.y_ne,
    div_ne_zero (neg_ne_zero.mpr q.2.x_ne) q.2.y_ne, ?_⟩
  have hdelta : delta4 (cyclicCoord q.1) = delta4 q.1 / q.1.y := by
    dsimp [delta4, cyclicCoord]
    field_simp [q.2.y_ne]
    ring
  rw [hdelta]
  exact div_ne_zero q.2.delta_ne q.2.y_ne

theorem cyclicSqCoord_mem (q : U4) : IsU4 (cyclicSqCoord q.1) := by
  refine ⟨div_ne_zero q.2.y_ne q.2.x_ne,
    div_ne_zero (neg_ne_zero.mpr one_ne_zero) q.2.x_ne, ?_⟩
  have hdelta : delta4 (cyclicSqCoord q.1) = -delta4 q.1 / q.1.x := by
    dsimp [delta4, cyclicSqCoord]
    field_simp [q.2.x_ne]
    ring
  rw [hdelta]
  exact div_ne_zero (neg_ne_zero.mpr q.2.delta_ne) q.2.x_ne

theorem oddXCoord_mem (q : U4) : IsU4 (oddXCoord q.1) := by
  refine ⟨div_ne_zero one_ne_zero q.2.x_ne,
    div_ne_zero (neg_ne_zero.mpr q.2.y_ne) q.2.x_ne, ?_⟩
  have hdelta : delta4 (oddXCoord q.1) = -delta4 q.1 / q.1.x := by
    dsimp [delta4, oddXCoord]
    field_simp [q.2.x_ne]
    ring
  rw [hdelta]
  exact div_ne_zero (neg_ne_zero.mpr q.2.delta_ne) q.2.x_ne

theorem rhoCoord_mem (q : U4) : IsU4 (rhoCoord q.1) := by
  refine ⟨neg_ne_zero.mpr q.2.y_ne, neg_ne_zero.mpr q.2.x_ne, ?_⟩
  have hdelta : delta4 (rhoCoord q.1) = delta4 q.1 := by
    dsimp [delta4, rhoCoord]
    ring
  rw [hdelta]
  exact q.2.delta_ne

theorem oddYCoord_mem (q : U4) : IsU4 (oddYCoord q.1) := by
  refine ⟨div_ne_zero q.2.x_ne q.2.y_ne, div_ne_zero one_ne_zero q.2.y_ne, ?_⟩
  have hdelta : delta4 (oddYCoord q.1) = delta4 q.1 / q.1.y := by
    dsimp [delta4, oddYCoord]
    field_simp [q.2.y_ne]
    ring
  rw [hdelta]
  exact div_ne_zero q.2.delta_ne q.2.y_ne

def cyclic (q : U4) : U4 := ⟨cyclicCoord q.1, cyclicCoord_mem q⟩
def cyclicSq (q : U4) : U4 := ⟨cyclicSqCoord q.1, cyclicSqCoord_mem q⟩
def oddX (q : U4) : U4 := ⟨oddXCoord q.1, oddXCoord_mem q⟩
def rho (q : U4) : U4 := ⟨rhoCoord q.1, rhoCoord_mem q⟩
def oddY (q : U4) : U4 := ⟨oddYCoord q.1, oddYCoord_mem q⟩

/-- Pointwise alternating transformation law in quotient coordinates. -/
structure PointAlt (f : U4 → ℝ) : Prop where
  cyclic : ∀ q, f (Pfaffian.cyclic q) = f q
  cyclicSq : ∀ q, f (Pfaffian.cyclicSq q) = f q
  oddX : ∀ q, f (Pfaffian.oddX q) = -f q
  rho : ∀ q, f (Pfaffian.rho q) = -f q
  oddY : ∀ q, f (Pfaffian.oddY q) = -f q

theorem PointAlt.zero_of_oddX_fixed {f : U4 → ℝ} (hf : PointAlt f) (q : U4)
    (hq : Pfaffian.oddX q = q) : f q = 0 := by
  have h := hf.oddX q
  rw [hq] at h
  linarith

theorem PointAlt.zero_of_rho_fixed {f : U4 → ℝ} (hf : PointAlt f) (q : U4)
    (hq : Pfaffian.rho q = q) : f q = 0 := by
  have h := hf.rho q
  rw [hq] at h
  linarith

theorem PointAlt.zero_of_oddY_fixed {f : U4 → ℝ} (hf : PointAlt f) (q : U4)
    (hq : Pfaffian.oddY q = q) : f q = 0 := by
  have h := hf.oddY q
  rw [hq] at h
  linarith

theorem oddX_fixed_of_x_eq_neg_one (q : U4) (hq : q.1.x = -1) : oddX q = q := by
  apply Subtype.ext
  apply Coord4.ext <;> simp [oddX, oddXCoord, hq]

theorem rho_fixed_of_y_eq_neg_x (q : U4) (hq : q.1.y = -q.1.x) : rho q = q := by
  apply Subtype.ext
  apply Coord4.ext <;> simp [rho, rhoCoord, hq]

theorem oddY_fixed_of_y_eq_one (q : U4) (hq : q.1.y = 1) : oddY q = q := by
  apply Subtype.ext
  apply Coord4.ext <;> simp [oddY, oddYCoord, hq]

/-- The three odd fixed-locus consequences in coordinate-free subtype form. -/
theorem PointAlt.zero_of_x_eq_neg_one {f : U4 → ℝ} (hf : PointAlt f) (q : U4)
    (hq : q.1.x = -1) : f q = 0 :=
  hf.zero_of_oddX_fixed q (oddX_fixed_of_x_eq_neg_one q hq)

theorem PointAlt.zero_of_y_eq_neg_x {f : U4 → ℝ} (hf : PointAlt f) (q : U4)
    (hq : q.1.y = -q.1.x) : f q = 0 :=
  hf.zero_of_rho_fixed q (rho_fixed_of_y_eq_neg_x q hq)

theorem PointAlt.zero_of_y_eq_one {f : U4 → ℝ} (hf : PointAlt f) (q : U4)
    (hq : q.1.y = 1) : f q = 0 :=
  hf.zero_of_oddY_fixed q (oddY_fixed_of_y_eq_one q hq)

/-! A single explicit rational point witnesses nonemptiness of all four substitution
domains. -/

def genericityWitnessCoord : Coord4 := ⟨2, 3⟩

theorem genericityWitnessCoord_mem : IsU4 genericityWitnessCoord := by
  constructor <;> norm_num [genericityWitnessCoord, delta4]

def genericityWitness : U4 := ⟨genericityWitnessCoord, genericityWitnessCoord_mem⟩

/-! ## The first defect substitution -/

def T1Coord (q : Coord4) : Coord4 := ⟨-q.x, -(q.y ^ 2)⟩

def Phi1Coord (q : Coord4) : Coord5 :=
  ⟨q.x, -q.x, q.y, -(q.y ^ 2), -(q.x * q.y)⟩

/-! The complete principal-Pfaffian factor table for `Φ₁`. -/

@[simp] theorem p0_Phi1Coord (q : Coord4) :
    p0 (Phi1Coord q) = q.x * q.y * (q.y - 2) := by
  simp [p0, Phi1Coord]
  ring

@[simp] theorem p1_Phi1Coord (q : Coord4) :
    p1 (Phi1Coord q) = -q.y * (q.x - q.y - 1) := by
  simp [p1, Phi1Coord]
  ring

@[simp] theorem p2_Phi1Coord (q : Coord4) :
    p2 (Phi1Coord q) = -q.x * (q.y - 2) := by
  simp [p2, Phi1Coord]
  ring

@[simp] theorem p3_Phi1Coord (q : Coord4) :
    p3 (Phi1Coord q) = q.x - q.y ^ 2 + 1 := by
  simp [p3, Phi1Coord]
  ring

@[simp] theorem p4_Phi1Coord (q : Coord4) :
    p4 (Phi1Coord q) = -q.x + q.y + 1 := by
  simp [p4, Phi1Coord]
  ring

/-- The exact admissible domain of the first substitution. -/
abbrev Adm1 := {q : U4 // IsU5 (Phi1Coord q.1)}

theorem Phi1Coord_witness_mem : IsU5 (Phi1Coord genericityWitnessCoord) := by
  constructor <;>
    norm_num [Phi1Coord, genericityWitnessCoord, p0, p1, p2, p3, p4]

/-- Explicit proof that the first admissible substitution domain is nonempty. -/
def adm1Witness : Adm1 := ⟨genericityWitness, Phi1Coord_witness_mem⟩

def phi1 (q : Adm1) : U5 := ⟨Phi1Coord q.1.1, q.2⟩

def base1 (q : Adm1) : U4 := q.1

/-- The first dilation target, defined through the corresponding total face. -/
def T1 (q : Adm1) : U4 := face4_3 (phi1 q)

@[simp]
theorem T1_val (q : Adm1) : (T1 q).1 = T1Coord q.1.1 := by
  rfl

theorem phi1_face0_eq_rho_face2 (q : Adm1) :
    face4_0 (phi1 q) = rho (face4_2 (phi1 q)) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [face4_0, face4Coord0, face4_2, face4Coord2, phi1, Phi1Coord, rho, rhoCoord]
  · field_simp [q.1.2.x_ne, q.1.2.y_ne]
  · field_simp [q.1.2.x_ne, q.1.2.y_ne]

theorem phi1_face1_eq_rho_base (q : Adm1) : face4_1 (phi1 q) = rho (base1 q) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [face4_1, face4Coord1, phi1, Phi1Coord, rho, rhoCoord, base1]
  · field_simp [q.1.2.y_ne]
  · field_simp [q.1.2.y_ne]

@[simp]
theorem phi1_face4_eq_base (q : Adm1) : face4_4 (phi1 q) = base1 q := by
  rfl

/-- The first pointwise defect--dilation identity. -/
theorem defect_dilation_one (f : U4 → ℝ) (hf : PointAlt f) (q : Adm1) :
    2 * f (base1 q) - f (T1 q) = D f (phi1 q) := by
  rw [D_apply, phi1_face0_eq_rho_face2, phi1_face1_eq_rho_base,
    phi1_face4_eq_base, hf.rho, hf.rho]
  simp only [T1]
  ring

/-! ## The second defect substitution -/

def T2Coord (q : Coord4) : Coord4 := ⟨q.x * q.y, -(q.y ^ 2)⟩

def Phi2Coord (q : Coord4) : Coord5 :=
  ⟨q.x, q.x * q.y, q.y, -(q.y ^ 2), -(q.x * q.y)⟩

/-! The complete principal-Pfaffian factor table for `Φ₂`. -/

@[simp] theorem p0_Phi2Coord (q : Coord4) :
    p0 (Phi2Coord q) = q.x * q.y * (2 * q.y - 1) := by
  simp [p0, Phi2Coord]
  ring

@[simp] theorem p1_Phi2Coord (q : Coord4) :
    p1 (Phi2Coord q) = -q.y * (q.x - q.y - 1) := by
  simp [p1, Phi2Coord]
  ring

@[simp] theorem p2_Phi2Coord (q : Coord4) :
    p2 (Phi2Coord q) = -q.x * (2 * q.y - 1) := by
  simp [p2, Phi2Coord]
  ring

@[simp] theorem p3_Phi2Coord (q : Coord4) :
    p3 (Phi2Coord q) = 1 - q.x * q.y - q.y ^ 2 := by
  simp [p3, Phi2Coord]
  ring

@[simp] theorem p4_Phi2Coord (q : Coord4) :
    p4 (Phi2Coord q) = -q.x + q.y + 1 := by
  simp [p4, Phi2Coord]
  ring

abbrev Adm2 := {q : U4 // IsU5 (Phi2Coord q.1)}

theorem Phi2Coord_witness_mem : IsU5 (Phi2Coord genericityWitnessCoord) := by
  constructor <;>
    norm_num [Phi2Coord, genericityWitnessCoord, p0, p1, p2, p3, p4]

/-- Explicit proof that the second admissible substitution domain is nonempty. -/
def adm2Witness : Adm2 := ⟨genericityWitness, Phi2Coord_witness_mem⟩

def phi2 (q : Adm2) : U5 := ⟨Phi2Coord q.1.1, q.2⟩
def base2 (q : Adm2) : U4 := q.1
def T2 (q : Adm2) : U4 := face4_3 (phi2 q)

@[simp]
theorem T2_val (q : Adm2) : (T2 q).1 = T2Coord q.1.1 := by
  rfl

theorem phi2_face0_x_eq_neg_one (q : Adm2) : (face4_0 (phi2 q)).1.x = -1 := by
  dsimp [face4_0, face4Coord0, phi2, Phi2Coord]
  field_simp [q.1.2.x_ne, q.1.2.y_ne]

theorem phi2_face1_eq_rho_base (q : Adm2) : face4_1 (phi2 q) = rho (base2 q) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [face4_1, face4Coord1, phi2, Phi2Coord, rho, rhoCoord, base2]
  · field_simp [q.1.2.y_ne]
  · field_simp [q.1.2.y_ne]

theorem phi2_face2_y_eq_neg_x (q : Adm2) :
    (face4_2 (phi2 q)).1.y = -(face4_2 (phi2 q)).1.x := by
  dsimp [face4_2, face4Coord2, phi2, Phi2Coord]
  field_simp [q.1.2.x_ne]

@[simp]
theorem phi2_face4_eq_base (q : Adm2) : face4_4 (phi2 q) = base2 q := by
  rfl

/-- The second pointwise defect--dilation identity. -/
theorem defect_dilation_two (f : U4 → ℝ) (hf : PointAlt f) (q : Adm2) :
    2 * f (base2 q) - f (T2 q) = D f (phi2 q) := by
  have hA : f (face4_0 (phi2 q)) = 0 :=
    hf.zero_of_x_eq_neg_one _ (phi2_face0_x_eq_neg_one q)
  have hC : f (face4_2 (phi2 q)) = 0 :=
    hf.zero_of_y_eq_neg_x _ (phi2_face2_y_eq_neg_x q)
  rw [D_apply, phi2_face1_eq_rho_base, phi2_face4_eq_base, hf.rho, hA, hC]
  simp only [T2]
  ring

/-! ## The third defect substitution -/

def T3Coord (q : Coord4) : Coord4 := ⟨q.y ^ 2 / q.x, 1 / q.x⟩

def Phi3Coord (q : Coord4) : Coord5 :=
  ⟨q.x, -1, q.y, -q.y, -(q.y ^ 2)⟩

/-! The complete principal-Pfaffian factor table for `Φ₃`. -/

@[simp] theorem p0_Phi3Coord (q : Coord4) :
    p0 (Phi3Coord q) = q.y * (q.x - q.y - 1) := by
  simp [p0, Phi3Coord]
  ring

@[simp] theorem p1_Phi3Coord (q : Coord4) :
    p1 (Phi3Coord q) = -q.y * (q.y - 2) := by
  simp [p1, Phi3Coord]
  ring

@[simp] theorem p2_Phi3Coord (q : Coord4) :
    p2 (Phi3Coord q) = q.x - q.y ^ 2 + 1 := by
  simp [p2, Phi3Coord]
  ring

@[simp] theorem p3_Phi3Coord (q : Coord4) :
    p3 (Phi3Coord q) = 2 - q.y := by
  simp [p3, Phi3Coord]
  ring

@[simp] theorem p4_Phi3Coord (q : Coord4) :
    p4 (Phi3Coord q) = -q.x + q.y + 1 := by
  simp [p4, Phi3Coord]
  ring

abbrev Adm3 := {q : U4 // IsU5 (Phi3Coord q.1)}

theorem Phi3Coord_witness_mem : IsU5 (Phi3Coord genericityWitnessCoord) := by
  constructor <;>
    norm_num [Phi3Coord, genericityWitnessCoord, p0, p1, p2, p3, p4]

/-- Explicit proof that the third admissible substitution domain is nonempty. -/
def adm3Witness : Adm3 := ⟨genericityWitness, Phi3Coord_witness_mem⟩

def phi3 (q : Adm3) : U5 := ⟨Phi3Coord q.1.1, q.2⟩
def base3 (q : Adm3) : U4 := q.1
def T3 (q : Adm3) : U4 := rho (face4_2 (phi3 q))

@[simp]
theorem T3_val (q : Adm3) : (T3 q).1 = T3Coord q.1.1 := by
  apply Coord4.ext <;>
    dsimp [T3, rho, rhoCoord, face4_2, face4Coord2, phi3, Phi3Coord, T3Coord]
  · field_simp [q.1.2.x_ne]
  · field_simp [q.1.2.x_ne]

theorem phi3_face0_eq_base (q : Adm3) : face4_0 (phi3 q) = base3 q := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [face4_0, face4Coord0, phi3, Phi3Coord, base3]
  · field_simp [q.1.2.y_ne]
  · field_simp [q.1.2.y_ne]

theorem phi3_face1_eq_face3 (q : Adm3) : face4_1 (phi3 q) = face4_3 (phi3 q) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [face4_1, face4Coord1, face4_3, face4Coord3, phi3, Phi3Coord]
  · field_simp [q.1.2.y_ne]
  · field_simp [q.1.2.y_ne]

theorem phi3_face1_x_eq_neg_one (q : Adm3) : (face4_1 (phi3 q)).1.x = -1 := by
  dsimp [face4_1, face4Coord1, phi3, Phi3Coord]
  field_simp [q.1.2.y_ne]

@[simp]
theorem phi3_face4_eq_base (q : Adm3) : face4_4 (phi3 q) = base3 q := by
  rfl

/-- The third pointwise defect--dilation identity. -/
theorem defect_dilation_three (f : U4 → ℝ) (hf : PointAlt f) (q : Adm3) :
    2 * f (base3 q) - f (T3 q) = D f (phi3 q) := by
  have hB : f (face4_1 (phi3 q)) = 0 :=
    hf.zero_of_x_eq_neg_one _ (phi3_face1_x_eq_neg_one q)
  rw [D_apply, phi3_face0_eq_base, ← phi3_face1_eq_face3, phi3_face4_eq_base, hB]
  simp only [T3]
  rw [hf.rho]
  ring

/-! ## The fourth defect substitution -/

def T4Coord (q : Coord4) : Coord4 := ⟨-q.y / q.x, -1 / (q.x * q.y)⟩

def Phi4Coord (q : Coord4) : Coord5 :=
  ⟨q.x, 1 / q.y, q.y, 1, q.y⟩

/-! The complete principal-Pfaffian factor table for `Φ₄`. -/

@[simp] theorem p0_Phi4Coord (q : Coord4) (hy : q.y ≠ 0) :
    p0 (Phi4Coord q) = -q.x + q.y + 1 := by
  simp only [p0, Phi4Coord]
  field_simp [hy]
  ring

@[simp] theorem p1_Phi4Coord (q : Coord4) :
    p1 (Phi4Coord q) = 2 * q.y - 1 := by
  simp [p1, Phi4Coord]
  ring

@[simp] theorem p2_Phi4Coord (q : Coord4) (hy : q.y ≠ 0) :
    p2 (Phi4Coord q) = (q.x * q.y + q.y ^ 2 - 1) / q.y := by
  simp only [p2, Phi4Coord]
  field_simp [hy]
  ring

@[simp] theorem p3_Phi4Coord (q : Coord4) (hy : q.y ≠ 0) :
    p3 (Phi4Coord q) = (2 * q.y - 1) / q.y := by
  simp only [p3, Phi4Coord]
  field_simp [hy]
  ring

@[simp] theorem p4_Phi4Coord (q : Coord4) :
    p4 (Phi4Coord q) = -q.x + q.y + 1 := by
  simp [p4, Phi4Coord]
  ring

abbrev Adm4 := {q : U4 // IsU5 (Phi4Coord q.1)}

theorem Phi4Coord_witness_mem : IsU5 (Phi4Coord genericityWitnessCoord) := by
  constructor <;>
    norm_num [Phi4Coord, genericityWitnessCoord, p0, p1, p2, p3, p4]

/-- Explicit proof that the fourth admissible substitution domain is nonempty. -/
def adm4Witness : Adm4 := ⟨genericityWitness, Phi4Coord_witness_mem⟩

def phi4 (q : Adm4) : U5 := ⟨Phi4Coord q.1.1, q.2⟩
def base4 (q : Adm4) : U4 := q.1
def T4 (q : Adm4) : U4 := rho (face4_2 (phi4 q))

@[simp]
theorem T4_val (q : Adm4) : (T4 q).1 = T4Coord q.1.1 := by
  apply Coord4.ext <;>
    dsimp [T4, rho, rhoCoord, face4_2, face4Coord2, phi4, Phi4Coord, T4Coord]
  · field_simp [q.1.2.x_ne, q.1.2.y_ne]
  · field_simp [q.1.2.x_ne, q.1.2.y_ne]

theorem phi4_face0_eq_base (q : Adm4) : face4_0 (phi4 q) = base4 q := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [face4_0, face4Coord0, phi4, Phi4Coord, base4]
  · field_simp [q.1.2.x_ne, q.1.2.y_ne]
  · field_simp [q.1.2.y_ne]

theorem phi4_face1_eq_face3 (q : Adm4) : face4_1 (phi4 q) = face4_3 (phi4 q) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [face4_1, face4Coord1, face4_3, face4Coord3, phi4, Phi4Coord]
  all_goals field_simp [q.1.2.y_ne]

theorem phi4_face1_y_eq_one (q : Adm4) : (face4_1 (phi4 q)).1.y = 1 := by
  dsimp [face4_1, face4Coord1, phi4, Phi4Coord]
  field_simp [q.1.2.y_ne]

@[simp]
theorem phi4_face4_eq_base (q : Adm4) : face4_4 (phi4 q) = base4 q := by
  rfl

/-- The fourth pointwise defect--dilation identity. -/
theorem defect_dilation_four (f : U4 → ℝ) (hf : PointAlt f) (q : Adm4) :
    2 * f (base4 q) - f (T4 q) = D f (phi4 q) := by
  have hB : f (face4_1 (phi4 q)) = 0 :=
    hf.zero_of_y_eq_one _ (phi4_face1_y_eq_one q)
  rw [D_apply, phi4_face0_eq_base, ← phi4_face1_eq_face3, phi4_face4_eq_base, hB]
  simp only [T4]
  rw [hf.rho]
  ring

/-! ## The diagonal five-point certificate -/

def diagonal4Coord (t : ℂ) : Coord4 := ⟨t, t⟩

theorem diagonal4Coord_mem (t : ℂ) (ht : t ≠ 0) : IsU4 (diagonal4Coord t) := by
  refine ⟨ht, ht, ?_⟩
  simp [delta4, diagonal4Coord]

def diagonal4 (t : ℂ) (ht : t ≠ 0) : U4 :=
  ⟨diagonal4Coord t, diagonal4Coord_mem t ht⟩

def diagonal5Coord (t : ℂ) : Coord5 := ⟨t, 1, t, 1, t⟩

theorem diagonal5Coord_mem (t : ℂ) (ht : t ≠ 0) (hhalf : t ≠ 1 / 2) :
    IsU5 (diagonal5Coord t) := by
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  have hlin : 2 * t - 1 ≠ 0 := by
    intro h
    apply hhalf
    apply (eq_div_iff htwo).2
    calc
      t * 2 = 2 * t := mul_comm _ _
      _ = 1 := sub_eq_zero.mp h
  refine ⟨ht, one_ne_zero, ht, one_ne_zero, ht, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [diagonal5Coord, p0] using ht
  · have hp : p1 (diagonal5Coord t) = 2 * t - 1 := by
      simp [diagonal5Coord, p1]
      ring
    rw [hp]
    exact hlin
  · have hp : p2 (diagonal5Coord t) = 2 * t - 1 := by
      simp [diagonal5Coord, p2]
      ring
    rw [hp]
    exact hlin
  · norm_num [diagonal5Coord, p3]
  · norm_num [diagonal5Coord, p4]

def diagonal5 (t : ℂ) (ht : t ≠ 0) (hhalf : t ≠ 1 / 2) : U5 :=
  ⟨diagonal5Coord t, diagonal5Coord_mem t ht hhalf⟩

theorem diagonal5_face0_eq_face3 (t : ℂ) (ht : t ≠ 0) (hhalf : t ≠ 1 / 2) :
    face4_0 (diagonal5 t ht hhalf) = face4_3 (diagonal5 t ht hhalf) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    dsimp [face4_0, face4Coord0, face4_3, face4Coord3, diagonal5, diagonal5Coord] <;>
    field_simp [ht]

theorem diagonal5_face1_eq_face2 (t : ℂ) (ht : t ≠ 0) (hhalf : t ≠ 1 / 2) :
    face4_1 (diagonal5 t ht hhalf) = face4_2 (diagonal5 t ht hhalf) := by
  rfl

@[simp]
theorem diagonal5_face4 (t : ℂ) (ht : t ≠ 0) (hhalf : t ≠ 1 / 2) :
    face4_4 (diagonal5 t ht hhalf) = diagonal4 t ht := by
  rfl

/-- The diagonal identity is in fact purely simplicial; alternation is not needed. -/
theorem D_diagonal (f : U4 → ℝ) (t : ℂ) (ht : t ≠ 0) (hhalf : t ≠ 1 / 2) :
    D f (diagonal5 t ht hhalf) = f (diagonal4 t ht) := by
  rw [D_apply, diagonal5_face0_eq_face3, diagonal5_face1_eq_face2,
    diagonal5_face4]
  ring

/-! ## Exact dyadic radial matrices -/

abbrev Mat2Q := Matrix (Fin 2) (Fin 2) ℚ

def upperShear (t : ℚ) : Mat2Q := !![1, t; 0, 1]
def radialU : Mat2Q := upperShear (1 / 2)
def radialUInv : Mat2Q := upperShear (-1 / 2)
def radialC : Mat2Q := !![0, -1; 1, -1]
def radialCInv : Mat2Q := !![-1, 1; -1, 0]
def radialV : Mat2Q := !![1, 0; -1 / 2, 1]
def radialVInv : Mat2Q := !![1, 0; 1 / 2, 1]
def radialR : Mat2Q := !![2, 0; 0, 1 / 2]
def radialRInv : Mat2Q := !![1 / 2, 0; 0, 2]

theorem radialU_inverse : radialU * radialUInv = 1 ∧ radialUInv * radialU = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [radialU, radialUInv, upperShear, Matrix.mul_apply, Fin.sum_univ_two]

theorem radialC_inverse : radialC * radialCInv = 1 ∧ radialCInv * radialC = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [radialC, radialCInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem radialV_inverse : radialV * radialVInv = 1 ∧ radialVInv * radialV = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [radialV, radialVInv, Matrix.mul_apply, Fin.sum_univ_two]

theorem radialR_inverse : radialR * radialRInv = 1 ∧ radialRInv * radialR = 1 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [radialR, radialRInv, Matrix.mul_apply, Fin.sum_univ_two]

/-- The lower shear is exactly the conjugate `C U C⁻¹`. -/
theorem radialV_eq_conjugate : radialV = radialC * radialU * radialCInv := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [radialV, radialC, radialU, radialCInv, upperShear,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- Kernel-checked dyadic factorization used in the compact-return word. -/
theorem radial_factorization :
    radialU ^ 4 * radialV * radialU ^ 2 * radialVInv ^ 2 * radialUInv ^ 2 =
      radialR := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [radialU, radialUInv, radialV, radialVInv, radialR, upperShear,
      Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

/-- One conjugation step multiplies an upper-shear parameter by four. -/
theorem radialR_conjugates_upperShear (t : ℚ) :
    radialR * upperShear t * radialRInv = upperShear (4 * t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radialR, radialRInv, upperShear, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-! ## Fixed-line edge discriminants -/

/-- Common admissibility discriminant for the elementary two-valued correspondence. -/
def deltaU (a b : ℂ) : ℂ :=
  a * b * (b - 2) * (2 * b - 1) * (a - b - 1) * (a - b ^ 2 + 1) *
    (1 - a * b - b ^ 2)

def fixedP1 (A : ℂ) : ℂ :=
  A ^ 2 * (A - 2) * (A + 2) * (A ^ 2 - 8) * (3 * A ^ 2 + 8)

def fixedP2 (A : ℂ) : ℂ :=
  A ^ 2 * (3 * A ^ 2 + 4) * (3 * A ^ 2 + 8) * (9 * A ^ 2 - 8)

def fixedP3 (A : ℂ) : ℂ :=
  A * (A - 2) * (2 * A - 1) * (9 * A + 10) * (9 * A ^ 2 - 8) *
    (9 * A ^ 2 - A - 9)

def fixedP4 (A : ℂ) : ℂ :=
  A ^ 2 * (A - 2) * (2 * A - 1) * (8 * A + 9) * (10 * A ^ 2 - 9) *
    (9 * A ^ 2 - A - 9)

def fixedP5 (A : ℂ) : ℂ :=
  (10 * A ^ 2 - 9) * (10 * A ^ 2 + 3 * Complex.I) *
    ((1 - 3 * Complex.I) * A ^ 2 - 3 * Complex.I)

def fixedP6 (A : ℂ) : ℂ :=
  (10 * A ^ 2 + 1) * (10 * A ^ 2 + 3 * Complex.I) *
    ((1 - 3 * Complex.I) * A ^ 2 - 1)

def fixedP7 (A : ℂ) : ℂ :=
  (A - 2 * Complex.I) * (2 * A - Complex.I) * (8 * A - Complex.I) *
    (10 * A ^ 2 + 1) * (A ^ 2 - 9 * Complex.I * A + 1)

def fixedP8 (A : ℂ) : ℂ :=
  (A - 2 * Complex.I) * (A + 10 * Complex.I) * (2 * A - Complex.I) *
    (A ^ 2 - 8) * (A ^ 2 - 9 * Complex.I * A + 1)

private theorem I_pow_five : Complex.I ^ 5 = Complex.I := by
  rw [show 5 = 4 + 1 by omega, pow_succ, Complex.I_pow_four, one_mul]

private theorem I_pow_six : Complex.I ^ 6 = -1 := by
  rw [show 6 = 4 + 2 by omega, pow_add, Complex.I_pow_four, one_mul, Complex.I_sq]

private theorem I_pow_seven : Complex.I ^ 7 = -Complex.I := by
  rw [show 7 = 4 + 3 by omega, pow_add, Complex.I_pow_four, one_mul,
    Complex.I_pow_three]

private theorem I_pow_eight : Complex.I ^ 8 = 1 := by
  rw [show 8 = 4 + 4 by omega, pow_add, Complex.I_pow_four, one_mul]

private theorem I_pow_nine : Complex.I ^ 9 = Complex.I := by
  rw [show 9 = 8 + 1 by omega, pow_succ, I_pow_eight, one_mul]

/-- First fixed-line discriminant factorization. -/
theorem fixed_discriminant_one (A : ℂ) :
    deltaU (A ^ 2) 3 = -15 * fixedP1 A := by
  simp only [deltaU, fixedP1]
  ring

/-- Second fixed-line discriminant factorization. -/
theorem fixed_discriminant_two (A : ℂ) :
    deltaU (-3 * A ^ 2) 3 = -45 * fixedP2 A := by
  simp only [deltaU, fixedP2]
  ring

/-- Third fixed-line discriminant factorization. -/
theorem fixed_discriminant_three (A : ℂ) :
    deltaU (-1 / 9) A = (1 / 6561) * fixedP3 A := by
  simp only [deltaU, fixedP3]
  ring

/-- Fourth fixed-line discriminant factorization. -/
theorem fixed_discriminant_four (A : ℂ) :
    deltaU (A / 9) A = (-1 / 6561) * fixedP4 A := by
  simp only [deltaU, fixedP4]
  ring

/-- Fifth fixed-line discriminant factorization. -/
theorem fixed_discriminant_five (A : ℂ) (hA : A ≠ 0) :
    deltaU (-(1 / A ^ 2)) (Complex.I / 3) =
      ((-16 + 15 * Complex.I) / 6561) * fixedP5 A / A ^ 8 := by
  simp only [deltaU, fixedP5]
  field_simp [hA, Complex.I_mul_I]
  ring_nf
  simp only [I_pow_five, I_pow_six, I_pow_seven, I_pow_eight, I_pow_nine,
    Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four]
  ring

/-- Sixth fixed-line discriminant factorization. -/
theorem fixed_discriminant_six (A : ℂ) (hA : A ≠ 0) :
    deltaU (Complex.I / (3 * A ^ 2)) (Complex.I / 3) =
      ((15 + 16 * Complex.I) / 19683) * fixedP6 A / A ^ 8 := by
  simp only [deltaU, fixedP6]
  field_simp [hA, Complex.I_mul_I]
  ring_nf
  simp only [I_pow_five, I_pow_six, I_pow_seven, I_pow_eight, I_pow_nine,
    Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four]
  ring

/-- Seventh fixed-line discriminant factorization. -/
theorem fixed_discriminant_seven (A : ℂ) (hA : A ≠ 0) :
    deltaU 9 (Complex.I / A) =
      (9 * Complex.I) * fixedP7 A / A ^ 8 := by
  simp only [deltaU, fixedP7]
  field_simp [hA, Complex.I_mul_I]
  ring_nf
  simp only [I_pow_five, I_pow_six, I_pow_seven, I_pow_eight, I_pow_nine,
    Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four]
  ring

/-- Eighth fixed-line discriminant factorization. -/
theorem fixed_discriminant_eight (A : ℂ) (hA : A ≠ 0) :
    deltaU (-9 * Complex.I / A) (Complex.I / A) =
      -9 * fixedP8 A / A ^ 9 := by
  simp only [deltaU, fixedP8]
  field_simp [hA, Complex.I_mul_I]
  ring_nf
  simp only [I_pow_five, I_pow_six, I_pow_seven, I_pow_eight, I_pow_nine,
    Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four]
  ring

/-! The constants in the eight factorization identities are all nonzero. -/

theorem fixed_constant_one_ne : (-15 : ℂ) ≠ 0 := by norm_num
theorem fixed_constant_two_ne : (-45 : ℂ) ≠ 0 := by norm_num
theorem fixed_constant_three_ne : (1 / 6561 : ℂ) ≠ 0 := by norm_num
theorem fixed_constant_four_ne : (-1 / 6561 : ℂ) ≠ 0 := by norm_num

theorem fixed_constant_five_ne : ((-16 + 15 * Complex.I) / 6561 : ℂ) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num at hr

theorem fixed_constant_six_ne : ((15 + 16 * Complex.I) / 19683 : ℂ) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num at hr

theorem fixed_constant_seven_ne : (9 * Complex.I : ℂ) ≠ 0 :=
  mul_ne_zero (by norm_num) Complex.I_ne_zero

theorem fixed_constant_eight_ne : (-9 : ℂ) ≠ 0 := by norm_num

/-! ## The exact two-free-vertices Jacobian minor -/

def betaJacobianWitness : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1 / 2, -1 / 2, 0, -1 / 2, 1 / 2;
     1, -3 / 2, 0, -1, 3 / 2;
     5 / 8, -1 / 2, -1 / 4, -1 / 2, 5 / 8;
     3 / 2, -3 / 2, -1 / 2, -1, 5 / 4;
     7 / 4, -7 / 4, -1 / 2, -1, 5 / 4]

/-- The displayed complex Jacobian minor has nonzero determinant `1/256`. -/
theorem betaJacobianWitness_det : betaJacobianWitness.det = 1 / 256 := by
  simp only [betaJacobianWitness, norm_det]

theorem betaJacobianWitness_det_ne : betaJacobianWitness.det ≠ 0 := by
  rw [betaJacobianWitness_det]
  norm_num

/-! ## Special-face rational functions and pole blocks -/

def specialN1 (a b : ℂ) : ℂ :=
  3 * a ^ 4 - 4 * a ^ 3 * b ^ 2 - 8 * a ^ 3 * b - 4 * a ^ 3 +
    5 * a ^ 2 * b ^ 4 - 8 * a ^ 2 * b ^ 3 + 48 * a ^ 2 * b ^ 2 -
    40 * a ^ 2 * b + 34 * a ^ 2 - 8 * a * b ^ 5 + 8 * a * b ^ 3 -
    20 * a * b ^ 2 - 24 * a * b - 4 * a + 6 * b ^ 6 - 8 * b ^ 5 -
    b ^ 4 + 16 * b ^ 3 - 8 * b ^ 2 + 8 * b + 19

def specialN2 (a b : ℂ) : ℂ :=
  3 * a ^ 4 * b ^ 2 - 4 * a ^ 3 * b ^ 3 - 8 * a ^ 3 * b ^ 2 -
    4 * a ^ 3 * b + 34 * a ^ 2 * b ^ 4 - 40 * a ^ 2 * b ^ 3 +
    48 * a ^ 2 * b ^ 2 - 8 * a ^ 2 * b + 5 * a ^ 2 - 4 * a * b ^ 5 -
    24 * a * b ^ 4 - 20 * a * b ^ 3 + 8 * a * b ^ 2 - 8 * a +
    19 * b ^ 6 + 8 * b ^ 5 - 8 * b ^ 4 + 16 * b ^ 3 - b ^ 2 - 8 * b + 6

def specialDenom1 (a b : ℂ) : ℂ :=
  30 * (b - 2) ^ 2 * (a - b - 1) ^ 2 * (a - b ^ 2 + 1)

def specialDenom2 (a b : ℂ) : ℂ :=
  30 * (2 * b - 1) ^ 2 * (a - b - 1) ^ 2 * (a * b + b ^ 2 - 1)

def specialF1 (a b : ℂ) : ℂ :=
  specialN1 a b / specialDenom1 a b

def specialF2 (a b : ℂ) : ℂ :=
  -specialN2 a b / specialDenom2 a b

theorem specialDenom1_ne_of_deltaU_ne {a b : ℂ} (h : deltaU a b ≠ 0) :
    specialDenom1 a b ≠ 0 := by
  have hb2 : b - 2 ≠ 0 := by
    intro hz
    apply h
    simp [deltaU, hz]
  have hab1 : a - b - 1 ≠ 0 := by
    intro hz
    apply h
    simp [deltaU, hz]
  have hab2 : a - b ^ 2 + 1 ≠ 0 := by
    intro hz
    apply h
    simp [deltaU, hz]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hb2)) (pow_ne_zero 2 hab1))
    hab2

theorem specialDenom2_ne_of_deltaU_ne {a b : ℂ} (h : deltaU a b ≠ 0) :
    specialDenom2 a b ≠ 0 := by
  have hb2 : 2 * b - 1 ≠ 0 := by
    intro hz
    apply h
    simp [deltaU, hz]
  have hab1 : a - b - 1 ≠ 0 := by
    intro hz
    apply h
    simp [deltaU, hz]
  have hab2 : 1 - a * b - b ^ 2 ≠ 0 := by
    intro hz
    apply h
    simp [deltaU, hz]
  have hab2' : a * b + b ^ 2 - 1 ≠ 0 := by
    rw [show a * b + b ^ 2 - 1 = -(1 - a * b - b ^ 2) by ring]
    exact neg_ne_zero.mpr hab2
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hb2)) (pow_ne_zero 2 hab1))
    hab2'

theorem specialF1_continuousAt {X : Type*} [TopologicalSpace X]
    {a b : X → ℂ} {x : X} (ha : ContinuousAt a x) (hb : ContinuousAt b x)
    (hdelta : deltaU (a x) (b x) ≠ 0) :
    ContinuousAt (fun z => specialF1 (a z) (b z)) x := by
  apply ContinuousAt.div₀
  · unfold specialN1
    fun_prop
  · unfold specialDenom1
    fun_prop
  · exact specialDenom1_ne_of_deltaU_ne hdelta

theorem specialF2_continuousAt {X : Type*} [TopologicalSpace X]
    {a b : X → ℂ} {x : X} (ha : ContinuousAt a x) (hb : ContinuousAt b x)
    (hdelta : deltaU (a x) (b x) ≠ 0) :
    ContinuousAt (fun z => specialF2 (a z) (b z)) x := by
  apply ContinuousAt.div₀
  · unfold specialN2
    fun_prop
  · unfold specialDenom2
    fun_prop
  · exact specialDenom2_ne_of_deltaU_ne hdelta

def specialG (a b : ℂ) : ℂ := specialF2 a b - specialF1 a b

def specialQ (X S : ℂ) : ℂ := specialG (-X) S + specialG (X * S) S

def fixedQ1 (A : ℂ) : ℂ := specialQ (-A ^ 2) 3
def fixedQ2 (A : ℂ) : ℂ := specialQ (1 / 9) A
def fixedQ3 (A : ℂ) : ℂ := specialQ (1 / A ^ 2) (Complex.I / 3)
def fixedQ4 (A : ℂ) : ℂ := specialQ (-9) (Complex.I / A)

def poleR1 (A : ℂ) : ℂ :=
  1701 * A ^ 14 - 15768 * A ^ 12 - 44145 * A ^ 10 + 516744 * A ^ 8 -
    65936 * A ^ 6 - 2656512 * A ^ 4 - 261120 * A ^ 2 + 1703936

def poleS1 (A : ℂ) : ℂ :=
  13608 * A ^ 13 + 27216 * A ^ 12 - 71712 * A ^ 11 - 143424 * A ^ 10 -
    633933 * A ^ 9 - 1243566 * A ^ 8 + 1633320 * A ^ 7 + 3115440 * A ^ 6 +
    5462192 * A ^ 5 + 10564384 * A ^ 4 - 464128 * A ^ 3 - 851456 * A ^ 2 -
    3638272 * A - 6969344

def poleR2 (A : ℂ) : ℂ :=
  3351942 * A ^ 11 + 14512770 * A ^ 10 + 6527619 * A ^ 9 -
    31596345 * A ^ 8 - 22099522 * A ^ 7 + 37036859 * A ^ 6 +
    31780606 * A ^ 5 - 25579727 * A ^ 4 - 32514102 * A ^ 3 +
    1818576 * A ^ 2 + 13268448 * A + 4117392

def poleS2 (A : ℂ) : ℂ :=
  13407768 * A ^ 11 + 98274384 * A ^ 10 + 181799604 * A ^ 9 -
    80115696 * A ^ 8 - 522301012 * A ^ 7 - 292153276 * A ^ 6 +
    404767838 * A ^ 5 + 435788732 * A ^ 4 - 39720591 * A ^ 3 -
    168747426 * A ^ 2 - 37687032 * A + 7220016

def fixedQ1Closed (A : ℂ) : ℂ :=
  4 * poleR1 A /
    (375 * (A - 2) ^ 2 * (A + 2) ^ 2 * (A ^ 2 - 8) *
      (3 * A ^ 2 + 4) ^ 2 * (9 * A ^ 2 - 8))

def fixedQ2Closed (A : ℂ) : ℂ :=
  2 * (A + 1) * poleR2 A /
    (45 * (A - 2) ^ 2 * (2 * A - 1) ^ 2 * (8 * A + 9) ^ 2 *
      (9 * A + 10) ^ 2 * (9 * A ^ 2 - 8) * (10 * A ^ 2 - 9))

/-- Exact first-block formula obtained from the two special-face rational functions. -/
theorem fixedQ1_eq_closed (A : ℂ)
    (hm2 : A - 2 ≠ 0) (hp2 : A + 2 ≠ 0) (h8 : A ^ 2 - 8 ≠ 0)
    (h34 : 3 * A ^ 2 + 4 ≠ 0) (h38 : 3 * A ^ 2 + 8 ≠ 0)
    (h98 : 9 * A ^ 2 - 8 ≠ 0) :
    fixedQ1 A = fixedQ1Closed A := by
  have h4 : A ^ 2 - 4 ≠ 0 := by
    rw [show A ^ 2 - 4 = (A - 2) * (A + 2) by ring]
    exact mul_ne_zero hm2 hp2
  have hd4 : 16 - A ^ 2 * 8 + A ^ 4 ≠ 0 := by
    rw [show 16 - A ^ 2 * 8 + A ^ 4 = (A ^ 2 - 4) ^ 2 by ring]
    exact pow_ne_zero 2 h4
  have hd34 : 16 + A ^ 2 * 24 + A ^ 4 * 9 ≠ 0 := by
    rw [show 16 + A ^ 2 * 24 + A ^ 4 * 9 = (3 * A ^ 2 + 4) ^ 2 by ring]
    exact pow_ne_zero 2 h34
  have hh8 : -8 + A ^ 2 ≠ 0 := by
    convert h8 using 1 <;> ring
  have hh38 : 8 + A ^ 2 * 3 ≠ 0 := by
    convert h38 using 1 <;> ring
  have hnh38 : -8 - A ^ 2 * 3 ≠ 0 := by
    rw [show -8 - A ^ 2 * 3 = -(3 * A ^ 2 + 8) by ring]
    exact neg_ne_zero.mpr h38
  have hh98 : -8 + A ^ 2 * 9 ≠ 0 := by
    convert h98 using 1 <;> ring
  have hnh98 : 8 - A ^ 2 * 9 ≠ 0 := by
    rw [show 8 - A ^ 2 * 9 = -(9 * A ^ 2 - 8) by ring]
    exact neg_ne_zero.mpr h98
  simp only [fixedQ1, specialQ, specialG, specialF1, specialF2, specialN1,
    specialN2, specialDenom1, specialDenom2, fixedQ1Closed, poleR1]
  field_simp [hm2, hp2, h8, h34, h38, h98, h4, hd4, hd34, hh8, hh38,
    hnh38, hh98, hnh98]
  field_simp [hd4, hd34, hh8, hh38, hnh38, hh98, hnh98]
  ring_nf
  field_simp [hd4, hd34, hh8, hh38, hnh38, hh98, hnh98]
  ring

/-- Exact second-block formula obtained from the two special-face rational functions. -/
theorem fixedQ2_eq_closed (A : ℂ)
    (hm2 : A - 2 ≠ 0) (h21 : 2 * A - 1 ≠ 0) (h89 : 8 * A + 9 ≠ 0)
    (h910 : 9 * A + 10 ≠ 0) (h98 : 9 * A ^ 2 - 8 ≠ 0)
    (h109 : 10 * A ^ 2 - 9 ≠ 0) (h9A : 9 * A ^ 2 - A - 9 ≠ 0) :
    fixedQ2 A = fixedQ2Closed A := by
  have hd1 : -9 + A * 35 - A ^ 2 * 23 - A ^ 3 * 40 + A ^ 4 * 36 ≠ 0 := by
    rw [show -9 + A * 35 - A ^ 2 * 23 - A ^ 3 * 40 + A ^ 4 * 36 =
      (2 * A - 1) ^ 2 * (9 * A ^ 2 - A - 9) by ring]
    exact mul_ne_zero (pow_ne_zero 2 h21) h9A
  have hd2 : 100 + A * 180 + A ^ 2 * 81 ≠ 0 := by
    rw [show 100 + A * 180 + A ^ 2 * 81 = (9 * A + 10) ^ 2 by ring]
    exact pow_ne_zero 2 h910
  have hd3 : 8 - A ^ 2 * 9 ≠ 0 := by
    rw [show 8 - A ^ 2 * 9 = -(9 * A ^ 2 - 8) by ring]
    exact neg_ne_zero.mpr h98
  have hd4 : -9 + A * 36 - A ^ 2 * 26 - A ^ 3 * 40 + A ^ 4 * 40 ≠ 0 := by
    rw [show -9 + A * 36 - A ^ 2 * 26 - A ^ 3 * 40 + A ^ 4 * 40 =
      (2 * A - 1) ^ 2 * (10 * A ^ 2 - 9) by ring]
    exact mul_ne_zero (pow_ne_zero 2 h21) h109
  have hd5 : 81 + A * 144 + A ^ 2 * 64 ≠ 0 := by
    rw [show 81 + A * 144 + A ^ 2 * 64 = (8 * A + 9) ^ 2 by ring]
    exact pow_ne_zero 2 h89
  have hd6 : 9 + A - A ^ 2 * 9 ≠ 0 := by
    rw [show 9 + A - A ^ 2 * 9 = -(9 * A ^ 2 - A - 9) by ring]
    exact neg_ne_zero.mpr h9A
  have hd7 :
      -729 + A * 1620 + A ^ 2 * 2502 - A ^ 3 * 4680 - A ^ 4 * 4184 +
          A ^ 5 * 3200 + A ^ 6 * 2560 ≠ 0 := by
    rw [show -729 + A * 1620 + A ^ 2 * 2502 - A ^ 3 * 4680 -
        A ^ 4 * 4184 + A ^ 5 * 3200 + A ^ 6 * 2560 =
      (2 * A - 1) ^ 2 * (8 * A + 9) ^ 2 * (10 * A ^ 2 - 9) by ring]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h21) (pow_ne_zero 2 h89)) h109
  simp only [fixedQ2, specialQ, specialG, specialF1, specialF2, specialN1,
    specialN2, specialDenom1, specialDenom2, fixedQ2Closed, poleR2]
  field_simp [hm2, h21, h89, h910, h98, h109, h9A]
  ring_nf
  field_simp [hd1, hd2, hd3, hd4, hd5, hd6, hd7]
  ring

/-- First block principal-part identity. -/
theorem fixedQ1_principal_part (A : ℂ)
    (hm2 : A - 2 ≠ 0) (hp2 : A + 2 ≠ 0) (h8 : A ^ 2 - 8 ≠ 0)
    (h34 : 3 * A ^ 2 + 4 ≠ 0) (h98 : 9 * A ^ 2 - 8 ≠ 0) :
    (A - 2) ^ 2 * fixedQ1Closed A + 1 / 10 =
      (A - 2) * poleS1 A /
        (750 * (A + 2) ^ 2 * (A ^ 2 - 8) * (3 * A ^ 2 + 4) ^ 2 *
          (9 * A ^ 2 - 8)) := by
  have hd : -128 - A ^ 2 * 48 + A ^ 4 * 144 + A ^ 6 * 81 ≠ 0 := by
    rw [show -128 - A ^ 2 * 48 + A ^ 4 * 144 + A ^ 6 * 81 =
      (3 * A ^ 2 + 4) ^ 2 * (9 * A ^ 2 - 8) by ring]
    exact mul_ne_zero (pow_ne_zero 2 h34) h98
  simp only [fixedQ1Closed, poleR1, poleS1]
  field_simp [hm2, hp2, h8, h34, h98, hd]
  field_simp [hd]
  ring_nf
  field_simp [hd]
  ring

/-- Second block principal-part identity. -/
theorem fixedQ2_principal_part (A : ℂ)
    (hm2 : A - 2 ≠ 0) (h21 : 2 * A - 1 ≠ 0) (h89 : 8 * A + 9 ≠ 0)
    (h910 : 9 * A + 10 ≠ 0) (h98 : 9 * A ^ 2 - 8 ≠ 0)
    (h109 : 10 * A ^ 2 - 9 ≠ 0) :
    (A - 2) ^ 2 * fixedQ2Closed A - 53 / 90 =
      (A - 2) * poleS2 A /
        (90 * (2 * A - 1) ^ 2 * (8 * A + 9) ^ 2 * (9 * A + 10) ^ 2 *
          (9 * A ^ 2 - 8) * (10 * A ^ 2 - 9)) := by
  have hd :
      583200 - A * 246240 - A ^ 2 * 4518108 - A ^ 3 * 631620 +
          A ^ 4 * 12809863 + A ^ 5 * 7519820 - A ^ 6 * 13468010 -
          A ^ 7 * 13069800 + A ^ 8 * 2778984 + A ^ 9 * 6480000 +
          A ^ 10 * 1866240 ≠ 0 := by
    rw [show 583200 - A * 246240 - A ^ 2 * 4518108 - A ^ 3 * 631620 +
        A ^ 4 * 12809863 + A ^ 5 * 7519820 - A ^ 6 * 13468010 -
        A ^ 7 * 13069800 + A ^ 8 * 2778984 + A ^ 9 * 6480000 +
        A ^ 10 * 1866240 =
      (2 * A - 1) ^ 2 * (8 * A + 9) ^ 2 * (9 * A + 10) ^ 2 *
        (9 * A ^ 2 - 8) * (10 * A ^ 2 - 9) by ring]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero (pow_ne_zero 2 h21) (pow_ne_zero 2 h89))
          (pow_ne_zero 2 h910))
        h98)
      h109
  simp only [fixedQ2Closed, poleR2, poleS2]
  field_simp [hm2, h21, h89, h910, h98, h109]
  ring_nf
  field_simp [hd]
  ring

theorem pole_leading_coefficient : (-1 / 10 : ℂ) + 53 / 90 = 22 / 45 := by
  norm_num

theorem fixedP5_two_ne : fixedP5 2 ≠ 0 := by
  unfold fixedP5
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · norm_num
  · intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  · intro h
    have hr := congrArg Complex.re h
    norm_num at hr

theorem fixedP6_two_ne : fixedP6 2 ≠ 0 := by
  unfold fixedP6
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · norm_num
  · intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  · intro h
    have hr := congrArg Complex.re h
    norm_num at hr

theorem fixedP7_two_ne : fixedP7 2 ≠ 0 := by
  unfold fixedP7
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_
  · intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  · intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  · intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  · norm_num
  · intro h
    have hr := congrArg Complex.re h
    norm_num at hr

theorem fixedP8_two_ne : fixedP8 2 ≠ 0 := by
  unfold fixedP8
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_) ?_
  · intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  · intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  · intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  · norm_num
  · intro h
    have hr := congrArg Complex.re h
    norm_num at hr

theorem fixedEdge5_two_ne :
    deltaU (-(1 / (2 : ℂ) ^ 2)) (Complex.I / 3) ≠ 0 := by
  rw [fixed_discriminant_five 2 (by norm_num)]
  exact div_ne_zero (mul_ne_zero fixed_constant_five_ne fixedP5_two_ne)
    (pow_ne_zero 8 (by norm_num))

theorem fixedEdge6_two_ne :
    deltaU (Complex.I / (3 * (2 : ℂ) ^ 2)) (Complex.I / 3) ≠ 0 := by
  rw [fixed_discriminant_six 2 (by norm_num)]
  exact div_ne_zero (mul_ne_zero fixed_constant_six_ne fixedP6_two_ne)
    (pow_ne_zero 8 (by norm_num))

theorem fixedEdge7_two_ne : deltaU 9 (Complex.I / 2) ≠ 0 := by
  rw [fixed_discriminant_seven 2 (by norm_num)]
  exact div_ne_zero (mul_ne_zero fixed_constant_seven_ne fixedP7_two_ne)
    (pow_ne_zero 8 (by norm_num))

theorem fixedEdge8_two_ne :
    deltaU (-9 * Complex.I / 2) (Complex.I / 2) ≠ 0 := by
  rw [fixed_discriminant_eight 2 (by norm_num)]
  exact div_ne_zero (mul_ne_zero fixed_constant_eight_ne fixedP8_two_ne)
    (pow_ne_zero 9 (by norm_num))

/-- The third block is regular at the prospective pole `A = 2`. -/
theorem fixedQ3_continuousAt_two : ContinuousAt fixedQ3 2 := by
  change ContinuousAt (fun A : ℂ =>
    specialG (-(1 / A ^ 2)) (Complex.I / 3) +
      specialG ((1 / A ^ 2) * (Complex.I / 3)) (Complex.I / 3)) 2
  have hX : ContinuousAt (fun A : ℂ => 1 / A ^ 2) 2 := by
    fun_prop (disch := norm_num)
  have hS : ContinuousAt (fun _ : ℂ => Complex.I / 3) 2 := continuousAt_const
  have hfirst : ContinuousAt
      (fun A : ℂ => specialG (-(1 / A ^ 2)) (Complex.I / 3)) 2 := by
    exact (specialF2_continuousAt hX.neg hS fixedEdge5_two_ne).sub
      (specialF1_continuousAt hX.neg hS fixedEdge5_two_ne)
  have hsecond : ContinuousAt
      (fun A : ℂ => specialG ((1 / A ^ 2) * (Complex.I / 3)) (Complex.I / 3)) 2 := by
    have hparam : ContinuousAt (fun A : ℂ => (1 / A ^ 2) * (Complex.I / 3)) 2 :=
      hX.mul continuousAt_const
    have hedge : deltaU ((1 / (2 : ℂ) ^ 2) * (Complex.I / 3)) (Complex.I / 3) ≠ 0 := by
      convert fixedEdge6_two_ne using 1 <;> norm_num <;> ring
    exact (specialF2_continuousAt hparam hS hedge).sub
      (specialF1_continuousAt hparam hS hedge)
  exact hfirst.add hsecond

/-- The fourth block is regular at the prospective pole `A = 2`. -/
theorem fixedQ4_continuousAt_two : ContinuousAt fixedQ4 2 := by
  change ContinuousAt (fun A : ℂ =>
    specialG (-(-9)) (Complex.I / A) +
      specialG ((-9) * (Complex.I / A)) (Complex.I / A)) 2
  have hS : ContinuousAt (fun A : ℂ => Complex.I / A) 2 := by
    fun_prop (disch := norm_num)
  have hfirst : ContinuousAt (fun A : ℂ => specialG 9 (Complex.I / A)) 2 := by
    exact (specialF2_continuousAt continuousAt_const hS fixedEdge7_two_ne).sub
      (specialF1_continuousAt continuousAt_const hS fixedEdge7_two_ne)
  have hsecond : ContinuousAt
      (fun A : ℂ => specialG (-9 * (Complex.I / A)) (Complex.I / A)) 2 := by
    have hparam : ContinuousAt (fun A : ℂ => -9 * (Complex.I / A)) 2 :=
      continuousAt_const.mul hS
    have hedge : deltaU (-9 * (Complex.I / 2)) (Complex.I / 2) ≠ 0 := by
      convert fixedEdge8_two_ne using 1 <;> ring
    exact (specialF2_continuousAt hparam hS hedge).sub
      (specialF1_continuousAt hparam hS hedge)
  have hsum := hfirst.add hsecond
  change ContinuousAt (fun A : ℂ =>
    specialG 9 (Complex.I / A) + specialG (-9 * (Complex.I / A)) (Complex.I / A)) 2 at hsum
  simpa only [neg_neg] using hsum

theorem fixedQ3_scaled_tendsto_zero :
    Tendsto (fun A : ℂ => (A - 2) ^ 2 * fixedQ3 A) (nhds 2) (nhds 0) := by
  have hzero : Tendsto (fun A : ℂ => (A - 2) ^ 2) (nhds 2) (nhds 0) := by
    have hid : Tendsto (fun A : ℂ => A) (nhds 2) (nhds 2) := tendsto_id
    have hc : Tendsto (fun _ : ℂ => (2 : ℂ)) (nhds 2) (nhds 2) := tendsto_const_nhds
    have hp := (hid.sub hc).pow 2
    norm_num at hp
    exact hp
  simpa using hzero.mul fixedQ3_continuousAt_two

theorem fixedQ4_scaled_tendsto_zero :
    Tendsto (fun A : ℂ => (A - 2) ^ 2 * fixedQ4 A) (nhds 2) (nhds 0) := by
  have hzero : Tendsto (fun A : ℂ => (A - 2) ^ 2) (nhds 2) (nhds 0) := by
    have hid : Tendsto (fun A : ℂ => A) (nhds 2) (nhds 2) := tendsto_id
    have hc : Tendsto (fun _ : ℂ => (2 : ℂ)) (nhds 2) (nhds 2) := tendsto_const_nhds
    have hp := (hid.sub hc).pow 2
    norm_num at hp
    exact hp
  simpa using hzero.mul fixedQ4_continuousAt_two

end

end Pfaffian

end Sp4
