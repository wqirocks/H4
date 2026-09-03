import Sp4.Pfaffian.Permutation
import Sp4.Pfaffian.Certificates
import Sp4.Measure.SmoothSubmersion
import Sp4.Symplectic.GenericApex

/-!
# Two free projective vertices

This file formalizes the explicit geometric calculation behind the
two-free-vertices lemma.  We work first with the standard ordered triple
`([e₁],[f₁],[e₁+f₁+e₂])` and the affine chart

`x = [a:b:c:1]`, `y = [d:e:f:1]`.

The five normalized Gram coordinates are computed from an actual projective
lift.  The full-rank assertion is then proved from an explicit local rational
section; the independent determinant certificate from the paper remains in
`Sp4.Pfaffian.Certificates`.
-/

namespace Sp4

open scoped LinearAlgebra.Projectivization
open OrbitChain

namespace TwoFree

noncomputable section

/-- Six affine coordinates `(a,b,c,d,e,f)` for two projective points. -/
abbrev Param := Fin 6 → ℂ

def a (p : Param) : ℂ := p 0
def b (p : Param) : ℂ := p 1
def c (p : Param) : ℂ := p 2
def d (p : Param) : ℂ := p 3
def e (p : Param) : ℂ := p 4
def f (p : Param) : ℂ := p 5

/-- The affine lift `[r:s:t:1]`. -/
def affineVector (r s t : ℂ) : SymplecticVector := ![r, s, t, 1]

theorem affineVector_ne_zero (r s t : ℂ) : affineVector r s t ≠ 0 := by
  intro h
  have h3 := congrFun h (3 : Fin 4)
  simpa [affineVector] using h3

def e1 : SymplecticVector := ![1, 0, 0, 0]
def f1 : SymplecticVector := ![0, 1, 0, 0]
def e1_add_f1_add_e2 : SymplecticVector := ![1, 1, 1, 0]
def f2 : SymplecticVector := ![0, 0, 0, 1]

theorem e1_ne_zero : e1 ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 4)
  simpa [e1] using h0

theorem f1_ne_zero : f1 ≠ 0 := by
  intro h
  have h1 := congrFun h (1 : Fin 4)
  simpa [f1] using h1

theorem e1_add_f1_add_e2_ne_zero : e1_add_f1_add_e2 ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 4)
  simpa [e1_add_f1_add_e2] using h0

theorem f2_ne_zero : f2 ≠ 0 := by
  intro h
  have h3 := congrFun h (3 : Fin 4)
  simpa [f2] using h3

/-- The standard strong ordered triple used in the stabilizer computation. -/
def standardTriple : ProjectiveConfig 3 :=
  ![Projectivization.mk ℂ e1 e1_ne_zero,
    Projectivization.mk ℂ f1 f1_ne_zero,
    Projectivization.mk ℂ e1_add_f1_add_e2 e1_add_f1_add_e2_ne_zero]

/-- The article's generic triple condition: pairwise transversality together
with genuine three-dimensional span.  For triples, the `four_spans` field of
`IsGeneric` is vacuous, so the independence condition must be recorded
separately. -/
structure IsStrongTriple (z : ProjectiveConfig 3) : Prop where
  generic : IsGeneric z
  independent : TriplesIndependent z

abbrev StrongTriple := {z : ProjectiveConfig 3 // IsStrongTriple z}

/-- The literal vector lift of `(x,y,[e₁],[f₁],[e₁+f₁+e₂])`. -/
def standardFiveVectors (p : Param) : Fin 5 → SymplecticVector :=
  ![affineVector (a p) (b p) (c p),
    affineVector (d p) (e p) (f p),
    e1, f1, e1_add_f1_add_e2]

theorem standardFiveVectors_ne_zero (p : Param) (i : Fin 5) :
    standardFiveVectors p i ≠ 0 := by
  fin_cases i <;>
    simp only [standardFiveVectors, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four] <;>
    first | exact affineVector_ne_zero _ _ _ | exact e1_ne_zero |
      exact f1_ne_zero | exact e1_add_f1_add_e2_ne_zero

/-- The projective five-tuple represented by `standardFiveVectors`. -/
def standardFiveConfig (p : Param) : ProjectiveConfig 5 := fun i ↦
  Projectivization.mk ℂ (standardFiveVectors p i)
    (standardFiveVectors_ne_zero p i)

/-- The displayed vectors, packaged as a simultaneous projective lift. -/
def standardFiveLift (p : Param) : ProjectiveLift (standardFiveConfig p) where
  vec := standardFiveVectors p
  ne_zero := standardFiveVectors_ne_zero p
  projectivizes _ := rfl

/-- The ten upper-triangular symplectic pairings of the displayed lift. -/
theorem gram_standardFiveVectors (p : Param) :
    gram (standardFiveVectors p) =
      !![0, a p * e p - b p * d p + c p - f p,
          -b p, a p, a p - b p - 1;
         -(a p * e p - b p * d p + c p - f p), 0,
          -e p, d p, d p - e p - 1;
         b p, e p, 0, 1, 1;
         -a p, -d p, -1, 0, -1;
         -(a p - b p - 1), -(d p - e p - 1), -1, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, standardFiveVectors, affineVector, e1, f1,
      e1_add_f1_add_e2, omega_apply, a, b, c, d, e, f] <;>
    ring

/-- The affine Pfaffian `Δ = ae-bd+c-f`. -/
def delta (p : Param) : ℂ := a p * e p - b p * d p + c p - f p

/-- The five rational quotient coordinates in the standard chart. -/
def betaFormula (p : Param) : Pfaffian.Coord5 :=
  ⟨b p * d p / (a p * e p),
    b p * (d p - e p - 1) / (e p * (a p - b p - 1)),
    -delta p / (a p * e p),
    -delta p / (e p * (a p - b p - 1)),
    -(b p * delta p) / (a p * e p * (a p - b p - 1))⟩

/-- Direct substitution of the ten pairings into the invariant `chi5` gives
the five formulas printed in the article. -/
theorem chi5_gram_standardFiveVectors (p : Param)
    (hdelta : delta p ≠ 0) (ha : a p ≠ 0) (hb : b p ≠ 0)
    (he : e p ≠ 0) (hshift : a p - b p - 1 ≠ 0) :
    Pfaffian.chi5 (gram (standardFiveVectors p)) = betaFormula p := by
  have hgram : gram (standardFiveVectors p) =
      !![0, delta p, -b p, a p, a p - b p - 1;
         -delta p, 0, -e p, d p, d p - e p - 1;
         b p, e p, 0, 1, 1;
         -a p, -d p, -1, 0, -1;
         -(a p - b p - 1), -(d p - e p - 1), -1, 1, 0] := by
    simpa [delta] using gram_standardFiveVectors p
  rw [hgram]
  apply Pfaffian.Coord5.ext
  · change d p * delta p * (-b p) / ((-e p) * delta p * a p) =
      b p * d p / (a p * e p)
    field_simp [hdelta, ha, he]
  · change (d p - e p - 1) * delta p * (-b p) /
        ((-e p) * delta p * (a p - b p - 1)) =
      b p * (d p - e p - 1) / (e p * (a p - b p - 1))
    field_simp [hdelta, he, hshift]
  · change 1 * delta p * (-b p) / ((-e p) * (-b p) * a p) =
      -delta p / (a p * e p)
    field_simp [ha, hb, he]
  · change 1 * delta p * (-b p) /
        ((-e p) * (-b p) * (a p - b p - 1)) =
      -delta p / (e p * (a p - b p - 1))
    field_simp [hb, he, hshift]
  · change (-1) * delta p * (-b p) /
        ((-e p) * a p * (a p - b p - 1)) =
      -(b p * delta p) / (a p * e p * (a p - b p - 1))
    field_simp [ha, he, hshift]

/-- The open domain on which the displayed projective five-tuple is generic. -/
abbrev Domain := {p : Param // IsGeneric (standardFiveConfig p)}

/-- The genuine normalized orbit map for the standard triple. -/
def beta (p : Domain) : Pfaffian.U5 :=
  Pfaffian.orbitCoord5 ⟨standardFiveConfig p.1, p.2⟩

theorem domain_delta_ne (p : Domain) : delta p.1 ≠ 0 := by
  have h := p.2.pairwise_transverse 0 1 (by decide)
  rw [show standardFiveConfig p.1 0 =
      Projectivization.mk ℂ (standardFiveVectors p.1 0)
        (standardFiveVectors_ne_zero p.1 0) by rfl,
    show standardFiveConfig p.1 1 =
      Projectivization.mk ℂ (standardFiveVectors p.1 1)
        (standardFiveVectors_ne_zero p.1 1) by rfl,
    transverse_mk_iff] at h
  simpa [gram, delta, standardFiveVectors, affineVector, omega_apply,
    a, b, c, d, e, f] using h

theorem domain_b_ne (p : Domain) : b p.1 ≠ 0 := by
  have h := p.2.pairwise_transverse 0 2 (by decide)
  rw [show standardFiveConfig p.1 0 =
      Projectivization.mk ℂ (standardFiveVectors p.1 0)
        (standardFiveVectors_ne_zero p.1 0) by rfl,
    show standardFiveConfig p.1 2 =
      Projectivization.mk ℂ (standardFiveVectors p.1 2)
        (standardFiveVectors_ne_zero p.1 2) by rfl,
    transverse_mk_iff] at h
  simpa [standardFiveVectors, affineVector, e1, omega_apply, b] using h

theorem domain_a_ne (p : Domain) : a p.1 ≠ 0 := by
  have h := p.2.pairwise_transverse 0 3 (by decide)
  rw [show standardFiveConfig p.1 0 =
      Projectivization.mk ℂ (standardFiveVectors p.1 0)
        (standardFiveVectors_ne_zero p.1 0) by rfl,
    show standardFiveConfig p.1 3 =
      Projectivization.mk ℂ (standardFiveVectors p.1 3)
        (standardFiveVectors_ne_zero p.1 3) by rfl,
    transverse_mk_iff] at h
  simpa [standardFiveVectors, affineVector, f1, omega_apply, a] using h

theorem domain_e_ne (p : Domain) : e p.1 ≠ 0 := by
  have h := p.2.pairwise_transverse 1 2 (by decide)
  rw [show standardFiveConfig p.1 1 =
      Projectivization.mk ℂ (standardFiveVectors p.1 1)
        (standardFiveVectors_ne_zero p.1 1) by rfl,
    show standardFiveConfig p.1 2 =
      Projectivization.mk ℂ (standardFiveVectors p.1 2)
        (standardFiveVectors_ne_zero p.1 2) by rfl,
    transverse_mk_iff] at h
  simpa [standardFiveVectors, affineVector, e1, omega_apply, e] using h

theorem domain_shift_ne (p : Domain) : a p.1 - b p.1 - 1 ≠ 0 := by
  have h := p.2.pairwise_transverse 0 4 (by decide)
  rw [show standardFiveConfig p.1 0 =
      Projectivization.mk ℂ (standardFiveVectors p.1 0)
        (standardFiveVectors_ne_zero p.1 0) by rfl,
    show standardFiveConfig p.1 4 =
      Projectivization.mk ℂ (standardFiveVectors p.1 4)
        (standardFiveVectors_ne_zero p.1 4) by rfl,
    transverse_mk_iff] at h
  simpa [standardFiveVectors, affineVector, e1_add_f1_add_e2,
    omega_apply, a, b] using h

/-- The coordinate-free orbit map agrees with the displayed rational map. -/
theorem beta_val (p : Domain) : (beta p).1 = betaFormula p.1 := by
  obtain ⟨s, hs⟩ :=
    (canonicalProjectiveLift (standardFiveConfig p.1)).gram_diagonalCongruent
      (standardFiveLift p.1)
  change Pfaffian.chi5 (projectiveGram (standardFiveConfig p.1)) = _
  have hs' : projectiveGram (standardFiveConfig p.1) =
      diagonalCongruence (fun i ↦ (s i : ℂ))
        (gram (standardFiveVectors p.1)) := by
    simpa [projectiveGram, canonicalProjectiveLift, standardFiveLift] using hs
  rw [hs', Pfaffian.chi5_diagonalCongruence]
  · exact chi5_gram_standardFiveVectors p.1 (domain_delta_ne p)
      (domain_a_ne p) (domain_b_ne p) (domain_e_ne p) (domain_shift_ne p)
  · intro i j hij
    have h := p.2.pairwise_transverse i j hij
    rw [show standardFiveConfig p.1 i =
        Projectivization.mk ℂ (standardFiveVectors p.1 i)
          (standardFiveVectors_ne_zero p.1 i) by rfl,
      show standardFiveConfig p.1 j =
        Projectivization.mk ℂ (standardFiveVectors p.1 j)
          (standardFiveVectors_ne_zero p.1 j) by rfl,
      transverse_mk_iff] at h
    exact h

/-! ## The full-rank witness from the paper -/

/-- `(a,b,c,d,e,f)=(-2,-2,-2,-2,-2,-1)`. -/
def witnessParam : Param := ![-2, -2, -2, -2, -2, -1]

/-- Its normalized quotient coordinate. -/
def witnessCoord : Pfaffian.Coord5 := ⟨1, 1, 1 / 4, 1 / 2, 1 / 2⟩

theorem witnessCoord_mem : Pfaffian.IsU5 witnessCoord := by
  constructor <;>
    norm_num [witnessCoord, Pfaffian.p0, Pfaffian.p1, Pfaffian.p2,
      Pfaffian.p3, Pfaffian.p4]

def witnessU5 : Pfaffian.U5 := ⟨witnessCoord, witnessCoord_mem⟩

@[simp] theorem witness_a : a witnessParam = -2 := by rfl
@[simp] theorem witness_b : b witnessParam = -2 := by rfl
@[simp] theorem witness_c : c witnessParam = -2 := by rfl
@[simp] theorem witness_d : d witnessParam = -2 := by rfl
@[simp] theorem witness_e : e witnessParam = -2 := by rfl
@[simp] theorem witness_f : f witnessParam = -1 := by rfl

@[simp] theorem witness_delta : delta witnessParam = -1 := by
  norm_num [delta]

/-- The ten pairings at the witness, in matrix form. -/
theorem gram_witness : gram (standardFiveVectors witnessParam) =
    !![0, -1, 2, -2, -1;
       1, 0, 2, -2, -1;
       -2, -2, 0, 1, 1;
       2, 2, -1, 0, -1;
       1, 1, -1, 1, 0] := by
  rw [gram_standardFiveVectors]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The inverse normalization factors carrying the normalized witness Gram
matrix back to the literal affine Gram matrix. -/
def witnessScale : Fin 5 → ℂˣ :=
  ![Units.mk0 (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero),
    Units.mk0 (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero),
    Units.mk0 (2 * Complex.I) (mul_ne_zero (by norm_num) Complex.I_ne_zero),
    Units.mk0 (-2 * Complex.I) (mul_ne_zero (by norm_num) Complex.I_ne_zero),
    Units.mk0 (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero)]

/-- Exact diagonal congruence relating the displayed pairings to the
normalized coordinate `(1,1,1/4,1/2,1/2)`. -/
theorem gram_witness_eq_diagonalCongruence :
    gram (standardFiveVectors witnessParam) =
      diagonalCongruence (fun i ↦ (witnessScale i : ℂ))
        (Pfaffian.matrix5 witnessCoord) := by
  rw [gram_witness]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalCongruence, witnessScale, Pfaffian.matrix5, witnessCoord,
      Complex.I_sq] <;>
    ring_nf <;>
    simp [Complex.I_sq]

theorem gram_witness_isAdmissible :
    IsAdmissibleGram (gram (standardFiveVectors witnessParam)) := by
  rw [gram_witness_eq_diagonalCongruence]
  exact Pfaffian.isAdmissibleGram_diagonalCongruence
    (OrbitChain.matrix5_isAdmissible witnessU5) witnessScale

/-- The witness is genuinely in the projective genericity domain. -/
theorem witness_generic : IsGeneric (standardFiveConfig witnessParam) :=
  (standardFiveLift witnessParam).isGeneric_of_gram_isAdmissible
    gram_witness_isAdmissible

def witness : Domain := ⟨witnessParam, witness_generic⟩

@[simp]
theorem betaFormula_witness : betaFormula witnessParam = witnessCoord := by
  apply Pfaffian.Coord5.ext <;>
    norm_num [betaFormula, delta, witnessCoord]

@[simp]
theorem beta_witness : beta witness = witnessU5 := by
  apply Subtype.ext
  rw [beta_val]
  exact betaFormula_witness

/-- The determinant certificate appearing in the article is nonzero after
coercion from `ℚ` to `ℂ`. -/
theorem betaJacobianWitness_complex_det_ne :
    (Pfaffian.betaJacobianWitness.map (algebraMap ℚ ℂ)).det ≠ 0 := by
  change ((algebraMap ℚ ℂ).mapMatrix Pfaffian.betaJacobianWitness).det ≠ 0
  rw [← RingHom.map_det, Pfaffian.betaJacobianWitness_det]
  norm_num

/-! ## A rational local section and the submersion certificate -/

/-- The first denominator appearing in the inverse formulas.  On `U5` it is
`-p1`. -/
def sourceDenom (q : Pfaffian.Coord5) : ℂ := q.x - q.y - q.w

/-- The second denominator appearing in the inverse formulas.  On `U5` it is
`-p0`. -/
def targetDenom (q : Pfaffian.Coord5) : ℂ :=
  q.u * q.x - q.y - q.v * q.w

theorem sourceDenom_eq_neg_p1 (q : Pfaffian.Coord5) :
    sourceDenom q = -Pfaffian.p1 q := by
  simp [sourceDenom, Pfaffian.p1]
  ring

theorem targetDenom_eq_neg_p0 (q : Pfaffian.Coord5) :
    targetDenom q = -Pfaffian.p0 q := by
  simp [targetDenom, Pfaffian.p0]
  ring

theorem sourceDenom_ne (q : Pfaffian.U5) : sourceDenom q.1 ≠ 0 := by
  rw [sourceDenom_eq_neg_p1]
  exact neg_ne_zero.mpr q.2.p1_ne

theorem targetDenom_ne (q : Pfaffian.U5) : targetDenom q.1 ≠ 0 := by
  rw [targetDenom_eq_neg_p0]
  exact neg_ne_zero.mpr q.2.p0_ne

/-- A rational right inverse to the five quotient formulas.  We fix `f=-1`;
the other five affine coordinates are then recovered from `(U,V,W,X,Y)`. -/
def betaSection (q : Pfaffian.Coord5) : Param :=
  ![q.x / sourceDenom q,
    q.y / sourceDenom q,
    -1 + (q.x / sourceDenom q) * (q.y / targetDenom q) *
      (q.u - q.w - 1),
    q.u * q.x / targetDenom q,
    q.y / targetDenom q,
    -1]

@[simp] theorem a_section (q : Pfaffian.Coord5) :
    a (betaSection q) = q.x / sourceDenom q := rfl
@[simp] theorem b_section (q : Pfaffian.Coord5) :
    b (betaSection q) = q.y / sourceDenom q := rfl
@[simp] theorem c_section (q : Pfaffian.Coord5) :
    c (betaSection q) = -1 + (q.x / sourceDenom q) *
      (q.y / targetDenom q) * (q.u - q.w - 1) := rfl
@[simp] theorem d_section (q : Pfaffian.Coord5) :
    d (betaSection q) = q.u * q.x / targetDenom q := rfl
@[simp] theorem e_section (q : Pfaffian.Coord5) :
    e (betaSection q) = q.y / targetDenom q := rfl
@[simp] theorem f_section (q : Pfaffian.Coord5) :
    f (betaSection q) = -1 := rfl

theorem shift_section (q : Pfaffian.U5) :
    a (betaSection q.1) - b (betaSection q.1) - 1 =
      q.1.w / sourceDenom q.1 := by
  simp only [a_section, b_section]
  field_simp [sourceDenom_ne q]
  simp [sourceDenom]

theorem secondShift_section (q : Pfaffian.U5) :
    d (betaSection q.1) - e (betaSection q.1) - 1 =
      q.1.v * q.1.w / targetDenom q.1 := by
  simp only [d_section, e_section]
  field_simp [targetDenom_ne q]
  simp [targetDenom]

theorem delta_section (q : Pfaffian.U5) :
    delta (betaSection q.1) =
      -(q.1.x * q.1.y * q.1.w) /
        (sourceDenom q.1 * targetDenom q.1) := by
  simp only [delta, a_section, b_section, c_section, d_section,
    e_section, f_section]
  field_simp [sourceDenom_ne q, targetDenom_ne q]
  simp [sourceDenom, targetDenom]
  ring

/-- The inverse formulas really form a right inverse on the whole normalized
generic locus, not merely to first order at the witness. -/
theorem betaFormula_section (q : Pfaffian.U5) :
    betaFormula (betaSection q.1) = q.1 := by
  have hs := sourceDenom_ne q
  have ht := targetDenom_ne q
  have hshift := shift_section q
  have hsecond := secondShift_section q
  have hdelta := delta_section q
  apply Pfaffian.Coord5.ext
  · change b (betaSection q.1) * d (betaSection q.1) /
        (a (betaSection q.1) * e (betaSection q.1)) = q.1.u
    rw [a_section, b_section, d_section, e_section]
    field_simp [hs, ht, q.2.x_ne, q.2.y_ne]
  · change b (betaSection q.1) *
        (d (betaSection q.1) - e (betaSection q.1) - 1) /
        (e (betaSection q.1) *
          (a (betaSection q.1) - b (betaSection q.1) - 1)) = q.1.v
    rw [hshift, hsecond, b_section, e_section]
    field_simp [hs, ht, q.2.w_ne, q.2.y_ne]
  · change -delta (betaSection q.1) /
        (a (betaSection q.1) * e (betaSection q.1)) = q.1.w
    rw [hdelta, a_section, e_section]
    field_simp [hs, ht, q.2.x_ne, q.2.y_ne, q.2.w_ne]
  · change -delta (betaSection q.1) /
        (e (betaSection q.1) *
          (a (betaSection q.1) - b (betaSection q.1) - 1)) = q.1.x
    rw [hdelta, e_section, hshift]
    field_simp [hs, ht, q.2.y_ne, q.2.w_ne]
  · change -(b (betaSection q.1) * delta (betaSection q.1)) /
        (a (betaSection q.1) * e (betaSection q.1) *
          (a (betaSection q.1) - b (betaSection q.1) - 1)) = q.1.y
    rw [hshift, b_section, hdelta, a_section, e_section]
    field_simp [hs, ht, q.2.x_ne, q.2.y_ne, q.2.w_ne]

/-- The rational section with the unused sixth affine coordinate fixed to an
arbitrary value.  This one-parameter freedom is the fibre direction of the
two-free quotient map. -/
def betaSectionWithF (r : ℂ) (q : Pfaffian.Coord5) : Param :=
  ![q.x / sourceDenom q,
    q.y / sourceDenom q,
    r + (q.x / sourceDenom q) * (q.y / targetDenom q) *
      (q.u - q.w - 1),
    q.u * q.x / targetDenom q,
    q.y / targetDenom q,
    r]

theorem delta_sectionWithF (r : ℂ) (q : Pfaffian.Coord5) :
    delta (betaSectionWithF r q) = delta (betaSection q) := by
  simp [delta, betaSectionWithF, betaSection, a, b, c, d, e, f]
  ring

/-- Every member of the one-parameter family is a right inverse on `U5`. -/
theorem betaFormula_sectionWithF (r : ℂ) (q : Pfaffian.U5) :
    betaFormula (betaSectionWithF r q.1) = q.1 := by
  calc
    betaFormula (betaSectionWithF r q.1) =
        betaFormula (betaSection q.1) := by
      apply Pfaffian.Coord5.ext
      · rfl
      · rfl
      · exact congrArg
          (fun z : ℂ ↦ -z /
            (a (betaSectionWithF r q.1) * e (betaSectionWithF r q.1)))
          (delta_sectionWithF r q.1)
      · exact congrArg
          (fun z : ℂ ↦ -z /
            (e (betaSectionWithF r q.1) *
              (a (betaSectionWithF r q.1) -
                b (betaSectionWithF r q.1) - 1)))
          (delta_sectionWithF r q.1)
      · exact congrArg
          (fun z : ℂ ↦ -(b (betaSectionWithF r q.1) * z) /
            (a (betaSectionWithF r q.1) * e (betaSectionWithF r q.1) *
              (a (betaSectionWithF r q.1) -
                b (betaSectionWithF r q.1) - 1)))
          (delta_sectionWithF r q.1)
    _ = q.1 := betaFormula_section q

theorem sourceDenom_betaFormula (p : Domain) :
    sourceDenom (betaFormula p.1) =
      -delta p.1 /
        (a p.1 * e p.1 * (a p.1 - b p.1 - 1)) := by
  simp only [sourceDenom, betaFormula]
  field_simp [domain_a_ne p, domain_e_ne p, domain_shift_ne p]
  ring

theorem targetDenom_betaFormula (p : Domain) :
    targetDenom (betaFormula p.1) =
      -(b p.1 * delta p.1) /
        (a p.1 * e p.1 ^ 2 * (a p.1 - b p.1 - 1)) := by
  simp only [targetDenom, betaFormula]
  field_simp [domain_a_ne p, domain_e_ne p, domain_shift_ne p]
  ring

/-- The free-coordinate section through a generic affine point returns that
point when evaluated at its quotient coordinate. -/
@[simp]
theorem betaSectionWithF_betaFormula (p : Domain) :
    betaSectionWithF (f p.1) (betaFormula p.1) = p.1 := by
  have ha := domain_a_ne p
  have hb := domain_b_ne p
  have he := domain_e_ne p
  have hs := domain_shift_ne p
  have hdelta := domain_delta_ne p
  funext i
  fin_cases i
  · change (betaFormula p.1).x / sourceDenom (betaFormula p.1) = a p.1
    rw [sourceDenom_betaFormula p]
    simp only [betaFormula]
    field_simp [ha, he, hs, hdelta]
  · change (betaFormula p.1).y / sourceDenom (betaFormula p.1) = b p.1
    rw [sourceDenom_betaFormula p]
    simp only [betaFormula]
    field_simp [ha, he, hs, hdelta]
  · change f p.1 +
      ((betaFormula p.1).x / sourceDenom (betaFormula p.1)) *
      ((betaFormula p.1).y / targetDenom (betaFormula p.1)) *
      ((betaFormula p.1).u - (betaFormula p.1).w - 1) = c p.1
    rw [sourceDenom_betaFormula p, targetDenom_betaFormula p]
    simp only [betaFormula]
    field_simp [ha, hb, he, hs, hdelta]
    simp [delta]
    ring
  · change (betaFormula p.1).u * (betaFormula p.1).x /
      targetDenom (betaFormula p.1) = d p.1
    rw [targetDenom_betaFormula p]
    simp only [betaFormula]
    field_simp [ha, hb, he, hs, hdelta]
  · change (betaFormula p.1).y / targetDenom (betaFormula p.1) = e p.1
    rw [targetDenom_betaFormula p]
    simp only [betaFormula]
    field_simp [ha, hb, he, hs, hdelta]
  · rfl

theorem a_section_ne (q : Pfaffian.U5) : a (betaSection q.1) ≠ 0 := by
  rw [a_section]
  exact div_ne_zero q.2.x_ne (sourceDenom_ne q)

theorem b_section_ne (q : Pfaffian.U5) : b (betaSection q.1) ≠ 0 := by
  rw [b_section]
  exact div_ne_zero q.2.y_ne (sourceDenom_ne q)

theorem e_section_ne (q : Pfaffian.U5) : e (betaSection q.1) ≠ 0 := by
  rw [e_section]
  exact div_ne_zero q.2.y_ne (targetDenom_ne q)

theorem d_section_ne (q : Pfaffian.U5) : d (betaSection q.1) ≠ 0 := by
  rw [d_section]
  exact div_ne_zero (mul_ne_zero q.2.u_ne q.2.x_ne) (targetDenom_ne q)

theorem shift_section_ne (q : Pfaffian.U5) :
    a (betaSection q.1) - b (betaSection q.1) - 1 ≠ 0 := by
  rw [shift_section]
  exact div_ne_zero q.2.w_ne (sourceDenom_ne q)

theorem secondShift_section_ne (q : Pfaffian.U5) :
    d (betaSection q.1) - e (betaSection q.1) - 1 ≠ 0 := by
  rw [secondShift_section]
  exact div_ne_zero (mul_ne_zero q.2.v_ne q.2.w_ne) (targetDenom_ne q)

theorem delta_section_ne (q : Pfaffian.U5) :
    delta (betaSection q.1) ≠ 0 := by
  rw [delta_section]
  exact div_ne_zero
    (neg_ne_zero.mpr (mul_ne_zero
      (mul_ne_zero q.2.x_ne q.2.y_ne) q.2.w_ne))
    (mul_ne_zero (sourceDenom_ne q) (targetDenom_ne q))

theorem gram_section_offDiagonal (q : Pfaffian.U5) :
    ∀ i j, i ≠ j →
      gram (standardFiveVectors (betaSection q.1)) i j ≠ 0 := by
  intro i j hij
  have hdelta := delta_section_ne q
  have ha := a_section_ne q
  have hb := b_section_ne q
  have hd := d_section_ne q
  have he := e_section_ne q
  have hshift := shift_section_ne q
  have hsecond := secondShift_section_ne q
  have hshiftRev :
      1 - (a (betaSection q.1) - b (betaSection q.1)) ≠ 0 := by
    intro hz
    apply hshift
    calc
      a (betaSection q.1) - b (betaSection q.1) - 1 =
          -(1 - (a (betaSection q.1) - b (betaSection q.1))) := by ring
      _ = 0 := by rw [hz]; simp
  have hsecondRev :
      1 - (d (betaSection q.1) - e (betaSection q.1)) ≠ 0 := by
    intro hz
    apply hsecond
    calc
      d (betaSection q.1) - e (betaSection q.1) - 1 =
          -(1 - (d (betaSection q.1) - e (betaSection q.1))) := by ring
      _ = 0 := by rw [hz]; simp
  have hgram : gram (standardFiveVectors (betaSection q.1)) =
      !![0, delta (betaSection q.1), -b (betaSection q.1),
          a (betaSection q.1),
          a (betaSection q.1) - b (betaSection q.1) - 1;
         -delta (betaSection q.1), 0, -e (betaSection q.1),
          d (betaSection q.1),
          d (betaSection q.1) - e (betaSection q.1) - 1;
         b (betaSection q.1), e (betaSection q.1), 0, 1, 1;
         -a (betaSection q.1), -d (betaSection q.1), -1, 0, -1;
         -(a (betaSection q.1) - b (betaSection q.1) - 1),
          -(d (betaSection q.1) - e (betaSection q.1) - 1),
          -1, 1, 0] := by
    simpa [delta] using gram_standardFiveVectors (betaSection q.1)
  rw [hgram]
  fin_cases i <;> fin_cases j <;>
    simp_all

/-- The section lands in the genuine projective genericity domain.  The
argument normalizes its literal Gram matrix and transports admissibility back
through the inverse diagonal congruence. -/
theorem betaSection_generic (q : Pfaffian.U5) :
    IsGeneric (standardFiveConfig (betaSection q.1)) := by
  let A := gram (standardFiveVectors (betaSection q.1))
  have hAchi : Pfaffian.chi5 A = q.1 := by
    calc
      Pfaffian.chi5 A = betaFormula (betaSection q.1) :=
        chi5_gram_standardFiveVectors _ (delta_section_ne q)
          (a_section_ne q) (b_section_ne q) (e_section_ne q)
          (shift_section_ne q)
      _ = q.1 := betaFormula_section q
  obtain ⟨s, hs⟩ := Pfaffian.exists_matrix5_chi5_diagonalCongruence
    A (gram_isSkew _) (gram_section_offDiagonal q)
  rw [hAchi] at hs
  let sinv : Fin 5 → ℂˣ := fun i ↦ (s i)⁻¹
  have hback : A = diagonalCongruence (fun i ↦ (sinv i : ℂ))
      (Pfaffian.matrix5 q.1) := by
    rw [hs]
    ext i j
    simp only [diagonalCongruence, sinv, Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero]
  apply (standardFiveLift (betaSection q.1)).isGeneric_of_gram_isAdmissible
  change IsAdmissibleGram A
  rw [hback]
  exact Pfaffian.isAdmissibleGram_diagonalCongruence
    (OrbitChain.matrix5_isAdmissible q) sinv

/-- A canonical generic preimage of each normalized five-point coordinate. -/
def betaPreimage (q : Pfaffian.U5) : Domain :=
  ⟨betaSection q.1, betaSection_generic q⟩

@[simp]
theorem beta_betaPreimage (q : Pfaffian.U5) : beta (betaPreimage q) = q := by
  apply Subtype.ext
  rw [beta_val]
  exact betaFormula_section q

/-- The standard-triple two-free-vertices map is onto the entire normalized
five-point quotient. -/
theorem beta_surjective : Function.Surjective beta := fun q ↦
  ⟨betaPreimage q, beta_betaPreimage q⟩

@[simp]
theorem section_witness : betaSection witnessCoord = witnessParam := by
  funext i
  fin_cases i <;>
    norm_num [betaSection, witnessCoord, sourceDenom, targetDenom, witnessParam]

theorem differentiableAt_betaFormula (p : Param)
    (ha : a p ≠ 0) (he : e p ≠ 0)
    (hshift : a p - b p - 1 ≠ 0) :
    DifferentiableAt ℂ betaFormula p := by
  apply Pfaffian.differentiableAt_coord5_mk
  all_goals dsimp [betaFormula, delta, a, b, c, d, e, f]
  all_goals fun_prop (disch := aesop)

theorem differentiableAt_betaFormula_witness :
    DifferentiableAt ℂ betaFormula witnessParam := by
  apply differentiableAt_betaFormula <;> norm_num

theorem differentiableAt_section (q : Pfaffian.Coord5)
    (hs : sourceDenom q ≠ 0) (ht : targetDenom q ≠ 0) :
    DifferentiableAt ℂ betaSection q := by
  rw [differentiableAt_pi]
  intro i
  fin_cases i
  all_goals simp [betaSection]
  all_goals fun_prop (disch := aesop) [sourceDenom, targetDenom]

theorem differentiableAt_sectionWithF (r : ℂ) (q : Pfaffian.Coord5)
    (hs : sourceDenom q ≠ 0) (ht : targetDenom q ≠ 0) :
    DifferentiableAt ℂ (betaSectionWithF r) q := by
  rw [differentiableAt_pi]
  intro i
  fin_cases i
  all_goals simp [betaSectionWithF]
  all_goals fun_prop (disch := aesop) [sourceDenom, targetDenom]

theorem differentiableAt_section_witness :
    DifferentiableAt ℂ betaSection witnessCoord := by
  apply differentiableAt_section <;>
    norm_num [sourceDenom, targetDenom, witnessCoord]

open Filter in
/-- The right-inverse identity holds on a neighbourhood of the witness. -/
theorem eventually_betaFormula_section :
    betaFormula ∘ betaSection =ᶠ[nhds witnessCoord] id := by
  have hU : ∀ᶠ q in nhds witnessCoord, q ∈ Pfaffian.u5Set :=
    Pfaffian.isOpen_u5Set.mem_nhds witnessCoord_mem
  filter_upwards [hU] with q hq
  exact betaFormula_section ⟨q, hq⟩

open Filter in
/-- The free-coordinate right inverse identity holds near every target point
of the normalized generic locus. -/
theorem eventually_betaFormula_sectionWithF (r : ℂ) (q : Pfaffian.U5) :
    betaFormula ∘ betaSectionWithF r =ᶠ[nhds q.1] id := by
  have hU : ∀ᶠ x in nhds q.1, x ∈ Pfaffian.u5Set :=
    Pfaffian.isOpen_u5Set.mem_nhds q.2
  filter_upwards [hU] with x hx
  exact betaFormula_sectionWithF r ⟨x, hx⟩

/-- The explicit standard-triple quotient formula has surjective complex
Fréchet derivative at the displayed witness.  The proof differentiates the
kernel-checked rational right inverse above. -/
theorem betaFormula_hasSurjectiveComplexFDerivAt_witness :
    HasSurjectiveComplexFDerivAt betaFormula witnessParam := by
  refine ⟨differentiableAt_betaFormula_witness, ?_⟩
  have hf : DifferentiableAt ℂ betaFormula (betaSection witnessCoord) := by
    rw [section_witness]
    exact differentiableAt_betaFormula_witness
  have hcomp := fderiv_comp witnessCoord
    hf differentiableAt_section_witness
  rw [section_witness] at hcomp
  have heq : fderiv ℂ (betaFormula ∘ betaSection) witnessCoord = 1 := by
    rw [eventually_betaFormula_section.fderiv_eq]
    exact fderiv_id
  have hright : Function.RightInverse (fderiv ℂ betaSection witnessCoord)
      (fderiv ℂ betaFormula witnessParam) := by
    intro v
    have hc := congrArg
      (fun L : Pfaffian.Coord5 →L[ℂ] Pfaffian.Coord5 ↦ L v)
      (hcomp.symm.trans heq)
    simpa using hc
  exact hright.surjective

/-- In fact the standard affine two-free quotient map is a submersion at
every generic point of its domain.  The proof uses the rational right inverse
whose free coordinate is chosen to pass through the prescribed point. -/
theorem betaFormula_hasSurjectiveComplexFDerivAt (p : Domain) :
    HasSurjectiveComplexFDerivAt betaFormula p.1 := by
  have hdiff : DifferentiableAt ℂ betaFormula p.1 :=
    differentiableAt_betaFormula p.1 (domain_a_ne p) (domain_e_ne p)
      (domain_shift_ne p)
  refine ⟨hdiff, ?_⟩
  let q : Pfaffian.U5 := beta p
  let s : Pfaffian.Coord5 → Param := betaSectionWithF (f p.1)
  have hq : q.1 = betaFormula p.1 := by
    exact beta_val p
  have hsAt : s q.1 = p.1 := by
    change betaSectionWithF (f p.1) q.1 = p.1
    rw [hq]
    exact betaSectionWithF_betaFormula p
  have hsDiff : DifferentiableAt ℂ s q.1 := by
    apply differentiableAt_sectionWithF
    · exact sourceDenom_ne q
    · exact targetDenom_ne q
  have hf : DifferentiableAt ℂ betaFormula (s q.1) := by
    rw [hsAt]
    exact hdiff
  have hcomp := fderiv_comp q.1 hf hsDiff
  rw [hsAt] at hcomp
  have heq : fderiv ℂ (betaFormula ∘ s) q.1 = 1 := by
    rw [(eventually_betaFormula_sectionWithF (f p.1) q).fderiv_eq]
    exact fderiv_id
  have hright : Function.RightInverse (fderiv ℂ s q.1)
      (fderiv ℂ betaFormula p.1) := by
    intro v
    have hc := congrArg
      (fun L : Pfaffian.Coord5 →L[ℂ] Pfaffian.Coord5 ↦ L v)
      (hcomp.symm.trans heq)
    simpa using hc
  exact hright.surjective

/-! ## Transitivity on strong triples -/

/-- A strong projective triple has linearly independent canonical lifts. -/
theorem StrongTriple.lift_linearIndependent (z : StrongTriple) :
    LinearIndependent ℂ (projectiveRepresentatives z.1) := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  have hdim := z.2.independent (id : Fin 3 → Fin 3) Function.injective_id
  have hspan : Submodule.span ℂ
      (Set.range (projectiveRepresentatives z.1)) =
      projectiveTripleSpan z.1 id := by
    rw [Submodule.span_range_eq_iSup]
    simp [projectiveTripleSpan, Projectivization.submodule_eq,
      projectiveRepresentatives]
  rw [Fintype.card_fin]
  change 3 = Module.finrank ℂ
    (Submodule.span ℂ (Set.range (projectiveRepresentatives z.1)))
  rw [hspan, hdim]

theorem StrongTriple.projectiveLift_linearIndependent (z : StrongTriple)
    (u : ProjectiveLift z.1) : LinearIndependent ℂ u.vec := by
  obtain ⟨s, hs⟩ := u.exists_scalars (canonicalProjectiveLift z.1)
  have hscaled := z.lift_linearIndependent.units_smul s
  have hfun : s • projectiveRepresentatives z.1 = u.vec := by
    funext i
    simpa [canonicalProjectiveLift, projectiveRepresentatives] using (hs i).symm
  rw [hfun] at hscaled
  exact hscaled

/-- A convenient symplectic basis whose first three projective lines form the
standard triple. -/
def standardFourVectors : Fin 4 → SymplecticVector :=
  ![e1, f1, e1_add_f1_add_e2, f2]

theorem gram_standardFourVectors : gram standardFourVectors =
    !![0, 1, 1, 0;
       -1, 0, -1, 0;
       -1, 1, 0, 1;
       0, 0, -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gram, standardFourVectors, e1, f1, e1_add_f1_add_e2,
      f2, omega_apply]

theorem standardFourVectors_linearIndependent :
    LinearIndependent ℂ standardFourVectors := by
  rw [Fintype.linearIndependent_iff]
  intro s hs i
  have hs0 := congrFun hs (0 : Fin 4)
  have hs1 := congrFun hs (1 : Fin 4)
  have hs2 := congrFun hs (2 : Fin 4)
  have hs3 := congrFun hs (3 : Fin 4)
  have h2 : s 2 = 0 := by
    simpa [standardFourVectors, e1, f1, e1_add_f1_add_e2, f2,
      Fin.sum_univ_succ] using hs2
  have h0 : s 0 = 0 := by
    simpa [standardFourVectors, e1, f1, e1_add_f1_add_e2, f2,
      Fin.sum_univ_succ, h2] using hs0
  have h1 : s 1 = 0 := by
    simpa [standardFourVectors, e1, f1, e1_add_f1_add_e2, f2,
      Fin.sum_univ_succ, h2] using hs1
  have h3 : s 3 = 0 := by
    simpa [standardFourVectors, e1, f1, e1_add_f1_add_e2, f2,
      Fin.sum_univ_succ] using hs3
  fin_cases i <;> assumption

noncomputable def standardFourBasis : Module.Basis (Fin 4) ℂ SymplecticVector :=
  basisOfTopLeSpanOfCardEqFinrank standardFourVectors
    (le_of_eq ((standardFourVectors_linearIndependent
      ).span_eq_top_of_card_eq_finrank
        (by simp [finrank_symplecticVector])).symm)
    (by simp [finrank_symplecticVector])

@[simp]
theorem standardFourBasis_apply (i : Fin 4) :
    standardFourBasis i = standardFourVectors i := by
  simp [standardFourBasis]

theorem gram_standardFourVectors_det_ne :
    (gram standardFourVectors).det ≠ 0 := by
  have hdet := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
    standardFourBasis).mp omega_nondegenerate
  have hmatrix : gram standardFourVectors =
      LinearMap.BilinForm.toMatrix standardFourBasis omega := by
    ext i j
    simp [gram]
  rw [hmatrix]
  exact hdet

/-- Pairwise transverse independent triples have lifts normalized to the
same three-by-three Gram matrix as the standard triple.  The only choice is
a square root in `ℂ`; all three normalization identities are checked below. -/
theorem exists_normalizedTripleLift (z : StrongTriple) :
    ∃ u : ProjectiveLift z.1,
      gram u.vec =
        !![0, 1, 1;
           -1, 0, -1;
           -1, 1, 0] := by
  let v : Fin 3 → SymplecticVector := projectiveRepresentatives z.1
  let A : ℂ := omega (v 0) (v 1)
  let B : ℂ := omega (v 0) (v 2)
  let C : ℂ := omega (v 1) (v 2)
  have hA : A ≠ 0 := by
    simpa [A, v, Transverse, projectiveRepresentatives] using
      z.2.generic.pairwise_transverse 0 1 (by decide)
  have hB : B ≠ 0 := by
    simpa [B, v, Transverse, projectiveRepresentatives] using
      z.2.generic.pairwise_transverse 0 2 (by decide)
  have hC : C ≠ 0 := by
    simpa [C, v, Transverse, projectiveRepresentatives] using
      z.2.generic.pairwise_transverse 1 2 (by decide)
  let target : ℂ := -C / (A * B)
  have htarget : target ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hC) (mul_ne_zero hA hB)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_eq_mul_self target
  have hr0 : r ≠ 0 := by
    intro hz
    apply htarget
    rw [hr, hz, zero_mul]
  let s0 : ℂˣ := Units.mk0 r hr0
  let s1 : ℂˣ := Units.mk0 (1 / (r * A))
    (div_ne_zero one_ne_zero (mul_ne_zero hr0 hA))
  let s2 : ℂˣ := Units.mk0 (1 / (r * B))
    (div_ne_zero one_ne_zero (mul_ne_zero hr0 hB))
  let s : Fin 3 → ℂˣ := ![s0, s1, s2]
  let w : Fin 3 → SymplecticVector := fun i ↦ (s i : ℂ) • v i
  have hw01 : omega (w 0) (w 1) = 1 := by
    simp [w, s, s0, s1]
    field_simp [hr0, hA]
    rfl
  have hw02 : omega (w 0) (w 2) = 1 := by
    simp [w, s, s0, s2]
    field_simp [hr0, hB]
    rfl
  have hw12 : omega (w 1) (w 2) = -1 := by
    simp [w, s, s1, s2]
    field_simp [hr0, hA, hB]
    rw [pow_two, ← hr]
    simp [target]
    field_simp [hA, hB]
    rfl
  let u : ProjectiveLift z.1 :=
    { vec := w
      ne_zero := fun i ↦ smul_ne_zero (Units.ne_zero (s i))
        (projectiveRepresentatives_ne_zero z.1 i)
      projectivizes := fun i ↦ by
        rw [← Projectivization.mk_rep (z.1 i),
          Projectivization.mk_eq_mk_iff']
        exact ⟨(s i : ℂ), rfl⟩ }
  refine ⟨u, ?_⟩
  ext i j
  change omega (w i) (w j) = _
  fin_cases i <;> fin_cases j
  all_goals norm_num
  · exact omega_isAlt _
  · exact hw01
  · exact hw02
  · rw [omega_skew, hw01]
  · exact omega_isAlt _
  · exact hw12
  · calc
      omega (w 2) (w 0) = -omega (w 0) (w 2) := omega_skew _ _
      _ = -1 := by rw [hw02]
  · calc
      omega (w 2) (w 1) = -omega (w 1) (w 2) := omega_skew _ _
      _ = 1 := by rw [hw12]; norm_num
  · exact omega_isAlt _

/-- A normalized strong triple extends to a symplectic basis with exactly the
same Gram matrix as `standardFourVectors`. -/
theorem exists_normalizedTripleExtension (z : StrongTriple)
    (u : ProjectiveLift z.1)
    (hu : gram u.vec =
      !![0, 1, 1;
         -1, 0, -1;
         -1, 1, 0]) :
    ∃ w : Fin 4 → SymplecticVector,
      (∀ i : Fin 3, w i.castSucc = u.vec i) ∧
      gram w = gram standardFourVectors := by
  have hu01 : omega (u.vec 0) (u.vec 1) = 1 := by
    have h := congrFun (congrFun hu 0) 1
    simpa [gram] using h
  have hu02 : omega (u.vec 0) (u.vec 2) = 1 := by
    have h := congrFun (congrFun hu 0) 2
    simpa [gram] using h
  have hu12 : omega (u.vec 1) (u.vec 2) = -1 := by
    have h := congrFun (congrFun hu 1) 2
    simpa [gram] using h
  have hu10 : omega (u.vec 1) (u.vec 0) = -1 := by
    rw [omega_skew, hu01]
  have hu20 : omega (u.vec 2) (u.vec 0) = -1 := by
    rw [omega_skew, hu02]
  have hu21 : omega (u.vec 2) (u.vec 1) = 1 := by
    rw [omega_skew, hu12]
    norm_num
  let radical : SymplecticVector := u.vec 2 - u.vec 0 - u.vec 1
  have hradical : radical ≠ 0 := by
    intro hzero
    let coeff : Fin 3 → ℂ := ![-1, -1, 1]
    have hsum : ∑ i, coeff i • u.vec i = 0 := by
      calc
        ∑ i, coeff i • u.vec i = radical := by
          simp [coeff, radical, Fin.sum_univ_succ]
          module
        _ = 0 := hzero
    have hc := (Fintype.linearIndependent_iff.mp
      (z.projectiveLift_linearIndependent u)) coeff hsum 2
    have hone : (1 : ℂ) = 0 := by simpa [coeff] using hc
    exact one_ne_zero hone
  obtain ⟨t, ht⟩ : ∃ t : SymplecticVector, omega radical t ≠ 0 := by
    by_contra h
    push_neg at h
    exact hradical (omega_nondegenerate.left radical h)
  let t0 : SymplecticVector := (omega radical t)⁻¹ • t
  have hradical_t0 : omega radical t0 = 1 := by
    simp [t0]
    field_simp [ht]
  have hradical_u0 : omega radical (u.vec 0) = 0 := by
    simp [radical, hu20, hu10, omega_isAlt (u.vec 0)]
  have hradical_u1 : omega radical (u.vec 1) = 0 := by
    simp [radical, hu21, hu01, omega_isAlt (u.vec 1)]
  let t' : SymplecticVector :=
    t0 + omega (u.vec 1) t0 • u.vec 0 -
      omega (u.vec 0) t0 • u.vec 1
  have hu0t : omega (u.vec 0) t' = 0 := by
    simp [t', hu01, omega_isAlt (u.vec 0)]
  have hu1t : omega (u.vec 1) t' = 0 := by
    simp [t', hu10, omega_isAlt (u.vec 1)]
  have hradical_t : omega radical t' = 1 := by
    simp [t', hradical_t0, hradical_u0, hradical_u1]
  have hu2t : omega (u.vec 2) t' = 1 := by
    have h := hradical_t
    simpa [radical, hu0t, hu1t] using h
  let w : Fin 4 → SymplecticVector := ![u.vec 0, u.vec 1, u.vec 2, t']
  refine ⟨w, ?_, ?_⟩
  · intro i
    fin_cases i <;> rfl
  · rw [gram_standardFourVectors]
    ext i j
    change omega (w i) (w j) = _
    fin_cases i <;> fin_cases j
    all_goals norm_num
    · exact omega_isAlt _
    · exact hu01
    · exact hu02
    · exact hu0t
    · exact hu10
    · exact omega_isAlt _
    · exact hu12
    · exact hu1t
    · exact hu20
    · exact hu21
    · exact omega_isAlt _
    · exact hu2t
    · calc
        omega (w 3) (w 0) = -omega (w 0) (w 3) := omega_skew _ _
        _ = 0 := by
          have h : omega (w 0) (w 3) = 0 := by simpa [w] using hu0t
          rw [h]
          norm_num
    · calc
        omega (w 3) (w 1) = -omega (w 1) (w 3) := omega_skew _ _
        _ = 0 := by
          have h : omega (w 1) (w 3) = 0 := by simpa [w] using hu1t
          rw [h]
          norm_num
    · calc
        omega (w 3) (w 2) = -omega (w 2) (w 3) := omega_skew _ _
        _ = -1 := by
          have h : omega (w 2) (w 3) = 1 := by simpa [w] using hu2t
          rw [h]
    · exact omega_isAlt _

/-- `Sp(4,ℂ)` is transitive on the strong ordered-triple locus.  This is the
transitivity assertion used in the two-free-vertices proof, derived from the
normalized lift and symplectic-basis extension above. -/
theorem exists_smul_eq_standardTriple (z : StrongTriple) :
    ∃ g : SymplecticGroup, g • z.1 = standardTriple := by
  obtain ⟨u, hu⟩ := exists_normalizedTripleLift z
  obtain ⟨w, hwfirst, hwgram⟩ := exists_normalizedTripleExtension z u hu
  have hwli : LinearIndependent ℂ w := by
    apply gram_linearIndependent_of_det_ne_zero
    rw [hwgram]
    exact gram_standardFourVectors_det_ne
  let wbasis : Module.Basis (Fin 4) ℂ SymplecticVector :=
    basisOfTopLeSpanOfCardEqFinrank w
      (le_of_eq (hwli.span_eq_top_of_card_eq_finrank
        (by simp [finrank_symplecticVector])).symm)
      (by simp [finrank_symplecticVector])
  obtain ⟨g, hg⟩ := exists_symplectic_of_gram_eq
    w standardFourVectors id wbasis standardFourBasis
    (by intro i; simp [wbasis])
    (by intro i; simp)
    hwgram
  refine ⟨g, funext fun i ↦ ?_⟩
  change g.1 • z.1 i = standardTriple i
  rw [← u.projectivizes i, Projectivization.smul_mk]
  have hgi : g.1 (u.vec i) = standardFourVectors i.castSucc := by
    calc
      g.1 (u.vec i) = g.1 (w i.castSucc) := by rw [hwfirst]
      _ = standardFourVectors i.castSucc := hg i.castSucc
  simp only [LinearEquiv.smul_def]
  fin_cases i
  · change Projectivization.mk ℂ (g.1 (u.vec 0)) _ =
      Projectivization.mk ℂ e1 e1_ne_zero
    have hi : g.1 (u.vec 0) = e1 := by
      simpa [standardFourVectors] using hgi
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨1, by simpa using hi.symm⟩
  · change Projectivization.mk ℂ (g.1 (u.vec 1)) _ =
      Projectivization.mk ℂ f1 f1_ne_zero
    have hi : g.1 (u.vec 1) = f1 := by
      simpa [standardFourVectors] using hgi
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨1, by simpa using hi.symm⟩
  · change Projectivization.mk ℂ (g.1 (u.vec 2)) _ =
      Projectivization.mk ℂ e1_add_f1_add_e2 e1_add_f1_add_e2_ne_zero
    have hi : g.1 (u.vec 2) = e1_add_f1_add_e2 := by
      simpa [standardFourVectors] using hgi
    rw [Projectivization.mk_eq_mk_iff']
    exact ⟨1, by simpa using hi.symm⟩

/-! ## The coordinate-free two-free map for an arbitrary strong triple -/

/-- Prepend two free projective vertices to a fixed ordered triple. -/
def withTriple (z : ProjectiveConfig 3) (x y : ProjectivePoint) :
    ProjectiveConfig 5 := Fin.cons x (Fin.cons y z)

/-- Pairs of free vertices for which the resulting five-tuple is generic. -/
abbrev PairDomain (z : StrongTriple) :=
  {p : ProjectivePoint × ProjectivePoint //
    IsGeneric (withTriple z.1 p.1 p.2)}

/-- The normalized five-point quotient map with a fixed strong triple in the
last three positions. -/
def betaFor (z : StrongTriple) (p : PairDomain z) : Pfaffian.U5 :=
  Pfaffian.orbitCoord5 ⟨withTriple z.1 p.1.1 p.1.2, p.2⟩

theorem standardFiveConfig_eq_withTriple (p : Param) :
    standardFiveConfig p = withTriple standardTriple
      (standardFiveConfig p 0) (standardFiveConfig p 1) := by
  funext i
  fin_cases i <;> rfl

/-- The full coordinate-free two-free-vertices surjectivity theorem. -/
theorem betaFor_surjective (z : StrongTriple) :
    Function.Surjective (betaFor z) := by
  obtain ⟨g, hg⟩ := exists_smul_eq_standardTriple z
  have hback : g⁻¹ • standardTriple = z.1 := by
    calc
      g⁻¹ • standardTriple = g⁻¹ • (g • z.1) :=
        congrArg (fun t : ProjectiveConfig 3 ↦ g⁻¹ • t) hg.symm
      _ = z.1 := by simp [smul_smul]
  intro q
  let p0 : Domain := betaPreimage q
  let std : GenericConfig 5 :=
    ⟨standardFiveConfig p0.1, p0.2⟩
  let moved : GenericConfig 5 := smulGeneric g⁻¹ std
  let xy : ProjectivePoint × ProjectivePoint := (moved.1 0, moved.1 1)
  have hconfig : withTriple z.1 xy.1 xy.2 = moved.1 := by
    funext i
    fin_cases i
    · rfl
    · rfl
    · change z.1 0 = g⁻¹ • standardTriple 0
      exact (congrFun hback 0).symm
    · change z.1 1 = g⁻¹ • standardTriple 1
      exact (congrFun hback 1).symm
    · change z.1 2 = g⁻¹ • standardTriple 2
      exact (congrFun hback 2).symm
  have hgeneric : IsGeneric (withTriple z.1 xy.1 xy.2) := by
    rw [hconfig]
    exact moved.2
  let pre : PairDomain z := ⟨xy, hgeneric⟩
  refine ⟨pre, ?_⟩
  change Pfaffian.orbitCoord5
      (⟨withTriple z.1 xy.1 xy.2, hgeneric⟩ : GenericConfig 5) = q
  have hsub : (⟨withTriple z.1 xy.1 xy.2, hgeneric⟩ : GenericConfig 5) =
      moved := Subtype.ext hconfig
  rw [hsub]
  change Pfaffian.orbitCoord5 (smulGeneric g⁻¹ std) = q
  rw [Pfaffian.orbitCoord5_smulGeneric]
  simpa [std, p0, beta] using beta_betaPreimage q

end

end TwoFree

end Sp4
