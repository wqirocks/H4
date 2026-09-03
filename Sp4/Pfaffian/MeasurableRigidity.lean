import Sp4.Correspondence.Return
import Sp4.Measure.FibreKernel

/-! Fibrewise smoothing, bounded-defect rigidity, and comparison injectivity. -/

namespace Sp4

namespace Pfaffian

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## The six coordinate symmetries and pointwise alternation -/

/-- The six elements of the quotient `S₄/V₄ ≃ S₃` acting on normalized
four-point coordinates. -/
inductive CoordSymm
  | identity
  | cyclic
  | cyclicSq
  | oddX
  | rho
  | oddY
deriving DecidableEq

def coordSymmEquivFin : CoordSymm ≃ Fin 6 where
  toFun
    | .identity => 0
    | .cyclic => 1
    | .cyclicSq => 2
    | .oddX => 3
    | .rho => 4
    | .oddY => 5
  invFun i := Fin.cases .identity (Fin.cases .cyclic
    (Fin.cases .cyclicSq (Fin.cases .oddX (Fin.cases .rho (fun _ => .oddY))))) i
  left_inv s := by cases s <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype CoordSymm :=
  Fintype.ofEquiv (Fin 6) coordSymmEquivFin.symm

/-- The faithful permutation of the homogeneous coordinates `[1,-x,y]`. -/
def coordSymmPerm : CoordSymm → Equiv.Perm (Fin 3)
  | .identity => 1
  | .cyclic => Equiv.swap 1 2 * Equiv.swap 0 1
  | .cyclicSq => Equiv.swap 0 1 * Equiv.swap 1 2
  | .oddX => Equiv.swap 0 1
  | .rho => Equiv.swap 1 2
  | .oddY => Equiv.swap 0 2

private theorem coordSymmPerm_bijective : Function.Bijective coordSymmPerm := by
  decide

/-- Identification of the explicit six-element type with `S₃`. -/
def coordSymmEquivPerm : CoordSymm ≃ Equiv.Perm (Fin 3) :=
  Equiv.ofBijective coordSymmPerm coordSymmPerm_bijective

instance : Group CoordSymm := coordSymmEquivPerm.group

/-- The transferred group structure is identified with permutation composition. -/
def coordSymmMulEquiv : CoordSymm ≃* Equiv.Perm (Fin 3) :=
  coordSymmEquivPerm.mulEquiv

@[simp]
theorem coordSymmPerm_mul (s t : CoordSymm) :
    coordSymmPerm (s * t) = coordSymmPerm s * coordSymmPerm t :=
  coordSymmMulEquiv.map_mul s t

/-- The real sign of a coordinate symmetry. -/
def coordSymmSign (s : CoordSymm) : ℝ :=
  ((Equiv.Perm.sign (coordSymmPerm s) : ℤ) : ℝ)

@[simp]
theorem coordSymmSign_mul (s t : CoordSymm) :
    coordSymmSign (s * t) = coordSymmSign s * coordSymmSign t := by
  simp [coordSymmSign, Equiv.Perm.sign_mul]

@[simp]
theorem coordSymmSign_sq (s : CoordSymm) : coordSymmSign s * coordSymmSign s = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign (coordSymmPerm s)) with hs | hs
  · simp [coordSymmSign, hs]
  · simp [coordSymmSign, hs]

@[simp]
theorem abs_coordSymmSign (s : CoordSymm) : |coordSymmSign s| = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign (coordSymmPerm s)) with hs | hs
  · simp [coordSymmSign, hs]
  · simp [coordSymmSign, hs]

/-- The six rational transformations from the article's `S₃` table. -/
def coordSymmAct : CoordSymm → U4 → U4
  | .identity => id
  | .cyclic => Pfaffian.cyclic
  | .cyclicSq => Pfaffian.cyclicSq
  | .oddX => Pfaffian.oddX
  | .rho => Pfaffian.rho
  | .oddY => Pfaffian.oddY

/-- Homogeneous coordinates `[1,-x,y]` on the normalized four-point locus. -/
def homogeneous4 (q : U4) : Fin 3 → ℂ :=
  ![1, -q.1.x, q.1.y]

theorem homogeneous4_ne_zero (q : U4) (i : Fin 3) : homogeneous4 q i ≠ 0 := by
  fin_cases i
  · simp [homogeneous4]
  · simpa [homogeneous4] using q.2.x_ne
  · simpa [homogeneous4] using q.2.y_ne

/-- Every displayed rational transformation is precisely permutation of homogeneous
coordinates followed by normalization of the zeroth coordinate. -/
theorem homogeneous4_coordSymmAct (s : CoordSymm) (q : U4) (i : Fin 3) :
    homogeneous4 (coordSymmAct s q) i =
      homogeneous4 q (coordSymmPerm s i) /
        homogeneous4 q (coordSymmPerm s 0) := by
  cases s <;> fin_cases i <;>
    simp [homogeneous4, coordSymmAct, coordSymmPerm, Pfaffian.cyclic,
      Pfaffian.cyclicSq, Pfaffian.oddX, Pfaffian.rho, Pfaffian.oddY,
      cyclicCoord, cyclicSqCoord, oddXCoord, rhoCoord, oddYCoord,
      Equiv.Perm.mul_apply, Equiv.swap_apply_def] <;>
    field_simp [q.2.x_ne, q.2.y_ne] <;> ring

private theorem eq_of_homogeneous4_eq (q r : U4)
    (h : ∀ i, homogeneous4 q i = homogeneous4 r i) : q = r := by
  apply Subtype.ext
  apply Coord4.ext
  · simpa [homogeneous4] using h 1
  · simpa [homogeneous4] using h 2

/-- The coordinate transformations form a right action: the inner symmetry is the
left factor in the resulting permutation. -/
theorem coordSymmAct_comp (s t : CoordSymm) (q : U4) :
    coordSymmAct s (coordSymmAct t q) = coordSymmAct (t * s) q := by
  apply eq_of_homogeneous4_eq
  intro i
  rw [homogeneous4_coordSymmAct, homogeneous4_coordSymmAct,
    homogeneous4_coordSymmAct, homogeneous4_coordSymmAct]
  simp only [coordSymmPerm_mul, Equiv.Perm.mul_apply]
  field_simp [homogeneous4_ne_zero]

@[continuity, fun_prop]
theorem continuous_u4_cyclic : Continuous Pfaffian.cyclic := by
  apply Continuous.subtype_mk
  apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
  apply Continuous.prodMk
  · change Continuous fun q : U4 => -1 / q.1.y
    exact continuous_const.div₀
      (continuous_coord4_y.comp continuous_subtype_val) (fun q => q.2.y_ne)
  · change Continuous fun q : U4 => -q.1.x / q.1.y
    exact (continuous_neg.comp
      (continuous_coord4_x.comp continuous_subtype_val)).div₀
        (continuous_coord4_y.comp continuous_subtype_val) (fun q => q.2.y_ne)

@[continuity, fun_prop]
theorem continuous_u4_cyclicSq : Continuous Pfaffian.cyclicSq := by
  apply Continuous.subtype_mk
  apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
  apply Continuous.prodMk
  · change Continuous fun q : U4 => q.1.y / q.1.x
    exact (continuous_coord4_y.comp continuous_subtype_val).div₀
      (continuous_coord4_x.comp continuous_subtype_val) (fun q => q.2.x_ne)
  · change Continuous fun q : U4 => -1 / q.1.x
    exact continuous_const.div₀
      (continuous_coord4_x.comp continuous_subtype_val) (fun q => q.2.x_ne)

@[continuity, fun_prop]
theorem continuous_u4_oddX : Continuous Pfaffian.oddX := by
  apply Continuous.subtype_mk
  apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
  apply Continuous.prodMk
  · change Continuous fun q : U4 => 1 / q.1.x
    exact continuous_const.div₀
      (continuous_coord4_x.comp continuous_subtype_val) (fun q => q.2.x_ne)
  · change Continuous fun q : U4 => -q.1.y / q.1.x
    exact (continuous_neg.comp
      (continuous_coord4_y.comp continuous_subtype_val)).div₀
        (continuous_coord4_x.comp continuous_subtype_val) (fun q => q.2.x_ne)

@[continuity, fun_prop]
theorem continuous_u4_rho : Continuous Pfaffian.rho := by
  apply Continuous.subtype_mk
  apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
  apply Continuous.prodMk <;> fun_prop

@[continuity, fun_prop]
theorem continuous_u4_oddY : Continuous Pfaffian.oddY := by
  apply Continuous.subtype_mk
  apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
  apply Continuous.prodMk
  · change Continuous fun q : U4 => q.1.x / q.1.y
    exact (continuous_coord4_x.comp continuous_subtype_val).div₀
      (continuous_coord4_y.comp continuous_subtype_val) (fun q => q.2.y_ne)
  · change Continuous fun q : U4 => 1 / q.1.y
    exact continuous_const.div₀
      (continuous_coord4_y.comp continuous_subtype_val) (fun q => q.2.y_ne)

@[continuity, fun_prop]
theorem continuous_coordSymmAct (s : CoordSymm) : Continuous (coordSymmAct s) := by
  cases s
  · exact continuous_id
  · exact continuous_u4_cyclic
  · exact continuous_u4_cyclicSq
  · exact continuous_u4_oddX
  · exact continuous_u4_rho
  · exact continuous_u4_oddY

/-! ## Differential-rank and measure-class certificates for the symmetries -/

/-- The rational coordinate transformations before restriction to the generic
open set. -/
def ambientCoordSymmAct : CoordSymm → Coord4 → Coord4
  | .identity => id
  | .cyclic => cyclicCoord
  | .cyclicSq => cyclicSqCoord
  | .oddX => oddXCoord
  | .rho => rhoCoord
  | .oddY => oddYCoord

/-- The inverse rational formula for each ambient coordinate symmetry.  These
formulas are used only in a neighborhood on which their displayed denominator
is nonzero. -/
def ambientCoordSymmSection : CoordSymm → Coord4 → Coord4
  | .identity => id
  | .cyclic => cyclicSqCoord
  | .cyclicSq => cyclicCoord
  | .oddX => oddXCoord
  | .rho => rhoCoord
  | .oddY => oddYCoord

@[simp]
theorem ambientCoordSymmAct_restrict (s : CoordSymm) (q : U4) :
    ambientCoordSymmAct s q.1 = (coordSymmAct s q).1 := by
  cases s <;> rfl

theorem ambientCoordSymmAct_mem (s : CoordSymm) (q : U4) :
    IsU4 (ambientCoordSymmAct s q.1) := by
  rw [ambientCoordSymmAct_restrict]
  exact (coordSymmAct s q).2

theorem differentiableAt_ambientCoordSymmAct (s : CoordSymm) (q : U4) :
    DifferentiableAt ℂ (ambientCoordSymmAct s) q.1 := by
  cases s
  · simp only [ambientCoordSymmAct]
    fun_prop
  · simp only [ambientCoordSymmAct, cyclicCoord]
    apply differentiableAt_coord4_mk <;>
      fun_prop (disch := exact q.2.y_ne)
  · simp only [ambientCoordSymmAct, cyclicSqCoord]
    apply differentiableAt_coord4_mk <;>
      fun_prop (disch := exact q.2.x_ne)
  · simp only [ambientCoordSymmAct, oddXCoord]
    apply differentiableAt_coord4_mk <;>
      fun_prop (disch := exact q.2.x_ne)
  · simp only [ambientCoordSymmAct, rhoCoord]
    apply differentiableAt_coord4_mk <;> fun_prop
  · simp only [ambientCoordSymmAct, oddYCoord]
    apply differentiableAt_coord4_mk <;>
      fun_prop (disch := exact q.2.y_ne)

theorem ambientCoordSymmSection_at (s : CoordSymm) (q : U4) :
    ambientCoordSymmSection s (ambientCoordSymmAct s q.1) = q.1 := by
  cases s <;>
    apply Coord4.ext <;>
    simp [ambientCoordSymmSection, ambientCoordSymmAct, cyclicCoord,
      cyclicSqCoord, oddXCoord, rhoCoord, oddYCoord] <;>
    field_simp [q.2.x_ne, q.2.y_ne]

theorem differentiableAt_ambientCoordSymmSection (s : CoordSymm) (q : U4) :
    DifferentiableAt ℂ (ambientCoordSymmSection s)
      (ambientCoordSymmAct s q.1) := by
  have ha : IsU4 (ambientCoordSymmAct s q.1) :=
    ambientCoordSymmAct_mem s q
  cases s
  · simp only [ambientCoordSymmSection]
    fun_prop
  · simp only [ambientCoordSymmSection, cyclicSqCoord]
    apply differentiableAt_coord4_mk <;>
      fun_prop (disch := exact ha.x_ne)
  · simp only [ambientCoordSymmSection, cyclicCoord]
    apply differentiableAt_coord4_mk <;>
      fun_prop (disch := exact ha.y_ne)
  · simp only [ambientCoordSymmSection, oddXCoord]
    apply differentiableAt_coord4_mk <;>
      fun_prop (disch := exact ha.x_ne)
  · simp only [ambientCoordSymmSection, rhoCoord]
    apply differentiableAt_coord4_mk <;> fun_prop
  · simp only [ambientCoordSymmSection, oddYCoord]
    apply differentiableAt_coord4_mk <;>
      fun_prop (disch := exact ha.y_ne)

/-- The inverse formula is a genuine right inverse near the image of every
point in the generic locus. -/
theorem eventually_ambientCoordSymm_section (s : CoordSymm) (q : U4) :
    ambientCoordSymmAct s ∘ ambientCoordSymmSection s =ᶠ[
      nhds (ambientCoordSymmAct s q.1)] id := by
  have ha : IsU4 (ambientCoordSymmAct s q.1) :=
    ambientCoordSymmAct_mem s q
  have hx : ∀ᶠ a in nhds (ambientCoordSymmAct s q.1), a.x ≠ 0 :=
    continuous_coord4_x.continuousAt.eventually_ne ha.x_ne
  have hy : ∀ᶠ a in nhds (ambientCoordSymmAct s q.1), a.y ≠ 0 :=
    continuous_coord4_y.continuousAt.eventually_ne ha.y_ne
  cases s
  · filter_upwards with a
    rfl
  · filter_upwards [hx] with a hax
    apply Coord4.ext <;>
      simp [ambientCoordSymmAct, ambientCoordSymmSection, cyclicCoord,
        cyclicSqCoord] <;>
      field_simp [hax]
  · filter_upwards [hy] with a hay
    apply Coord4.ext <;>
      simp [ambientCoordSymmAct, ambientCoordSymmSection, cyclicCoord,
        cyclicSqCoord] <;>
      field_simp [hay]
  · filter_upwards [hx] with a hax
    apply Coord4.ext <;>
      simp [ambientCoordSymmAct, ambientCoordSymmSection, oddXCoord] <;>
      field_simp [hax]
  · filter_upwards with a
    apply Coord4.ext <;>
      simp [ambientCoordSymmAct, ambientCoordSymmSection, rhoCoord]
  · filter_upwards [hy] with a hay
    apply Coord4.ext <;>
      simp [ambientCoordSymmAct, ambientCoordSymmSection, oddYCoord] <;>
      field_simp [hay]

/-- Every one of the six ambient rational transformations has surjective
complex Fréchet derivative on the generic four-point locus. -/
theorem ambientCoordSymmAct_hasSurjectiveComplexFDerivAt
    (s : CoordSymm) (q : U4) :
    HasSurjectiveComplexFDerivAt (ambientCoordSymmAct s) q.1 := by
  refine ⟨differentiableAt_ambientCoordSymmAct s q, ?_⟩
  let sec := ambientCoordSymmSection s
  let a := ambientCoordSymmAct s q.1
  have hs : DifferentiableAt ℂ sec a :=
    differentiableAt_ambientCoordSymmSection s q
  have hsa : sec a = q.1 := ambientCoordSymmSection_at s q
  have hf : DifferentiableAt ℂ (ambientCoordSymmAct s) (sec a) := by
    rw [hsa]
    exact differentiableAt_ambientCoordSymmAct s q
  have hcomp := fderiv_comp a hf hs
  rw [hsa] at hcomp
  have heq : fderiv ℂ (ambientCoordSymmAct s ∘ sec) a = 1 := by
    rw [(eventually_ambientCoordSymm_section s q).fderiv_eq]
    exact fderiv_id
  have hright : Function.RightInverse (fderiv ℂ sec a)
      (fderiv ℂ (ambientCoordSymmAct s) q.1) := by
    intro v
    have hc := congrArg (fun L : Coord4 →L[ℂ] Coord4 => L v)
      (hcomp.symm.trans heq)
    simpa using hc
  exact hright.surjective

/-- All six quotient-coordinate symmetries are nonsingular for the concrete
normalized Gaussian measure. -/
theorem coordSymmAct_quasiMeasurePreserving (s : CoordSymm) :
    Measure.QuasiMeasurePreserving (coordSymmAct s) measureU4 measureU4 := by
  have hmem : ∀ x, x ∈ u4Set → ambientCoordSymmAct s x ∈ u4Set := by
    intro x hx
    exact ambientCoordSymmAct_mem s ⟨x, hx⟩
  have h := quasiMeasurePreserving_normalizedOpenGaussian_of_submersion
    coord4Gaussian coord4Gaussian
    coord4GaussianPresentation coord4GaussianPresentation
    u4Set isOpen_u4Set u4Set_nonempty
    u4Set isOpen_u4Set u4Set_nonempty
    (ambientCoordSymmAct s)
    hmem
    (by
      intro x hx
      exact ambientCoordSymmAct_hasSurjectiveComplexFDerivAt s ⟨x, hx⟩)
  change Measure.QuasiMeasurePreserving (coordSymmAct s)
    (normalizedOpenMeasure coord4Gaussian u4Set isOpen_u4Set u4Set_nonempty)
    (normalizedOpenMeasure coord4Gaussian u4Set isOpen_u4Set u4Set_nonempty)
  refine h.congr (continuous_coordSymmAct s).measurable ?_
  filter_upwards with q
  apply Subtype.ext
  exact ambientCoordSymmAct_restrict s q

/-- Pointwise quotient-coordinate alternation. -/
def coordinateAlt (f : U4 → ℝ) (q : U4) : ℝ :=
  (1 / 6 : ℝ) * ∑ s : CoordSymm, coordSymmSign s * f (coordSymmAct s q)

theorem coordinateAlt_coordSymmAct (f : U4 → ℝ) (t : CoordSymm) (q : U4) :
    coordinateAlt f (coordSymmAct t q) =
      coordSymmSign t * coordinateAlt f q := by
  have hreindex := Fintype.sum_equiv (Equiv.mulLeft t)
    (fun s : CoordSymm =>
      coordSymmSign t * coordSymmSign (t * s) * f (coordSymmAct (t * s) q))
    (fun r : CoordSymm =>
      coordSymmSign t * coordSymmSign r * f (coordSymmAct r q))
    (fun _ => rfl)
  have hsum :
      (∑ s : CoordSymm,
        coordSymmSign s * f (coordSymmAct (t * s) q)) =
      coordSymmSign t *
        ∑ r : CoordSymm, coordSymmSign r * f (coordSymmAct r q) := by
    have hcancel (x : ℝ) : coordSymmSign t * (coordSymmSign t * x) = x := by
      rw [← mul_assoc, coordSymmSign_sq, one_mul]
    rw [Finset.mul_sum]
    simpa only [coordSymmSign_mul, mul_assoc, hcancel] using hreindex
  simp only [coordinateAlt, coordSymmAct_comp]
  rw [hsum]
  ring

/-- Alternation produces the exact five pointwise transformation laws used by the
compact-return argument. -/
theorem pointAlt_coordinateAlt (f : U4 → ℝ) : PointAlt (coordinateAlt f) := by
  constructor
  · intro q
    simpa [coordSymmAct, coordSymmSign, coordSymmPerm,
      Equiv.Perm.sign_mul, Equiv.swap_apply_def] using
      coordinateAlt_coordSymmAct f CoordSymm.cyclic q
  · intro q
    simpa [coordSymmAct, coordSymmSign, coordSymmPerm,
      Equiv.Perm.sign_mul, Equiv.swap_apply_def] using
      coordinateAlt_coordSymmAct f CoordSymm.cyclicSq q
  · intro q
    simpa [coordSymmAct, coordSymmSign, coordSymmPerm,
      Equiv.swap_apply_def] using
      coordinateAlt_coordSymmAct f CoordSymm.oddX q
  · intro q
    simpa [coordSymmAct, coordSymmSign, coordSymmPerm,
      Equiv.swap_apply_def] using
      coordinateAlt_coordSymmAct f CoordSymm.rho q
  · intro q
    simpa [coordSymmAct, coordSymmSign, coordSymmPerm,
      Equiv.swap_apply_def] using
      coordinateAlt_coordSymmAct f CoordSymm.oddY q

@[simp]
theorem card_coordSymm : Fintype.card CoordSymm = 6 := by
  simpa using Fintype.card_congr coordSymmEquivFin

theorem continuous_coordinateAlt {f : U4 → ℝ} (hf : Continuous f) :
    Continuous (coordinateAlt f) := by
  apply continuous_const.mul
  apply continuous_finsetSum Finset.univ
  intro s hs
  exact continuous_const.mul (hf.comp (continuous_coordSymmAct s))

theorem pointAlt_coordSymmAct {f : U4 → ℝ} (hf : PointAlt f)
    (s : CoordSymm) (q : U4) :
    f (coordSymmAct s q) = coordSymmSign s * f q := by
  cases s
  · simp [coordSymmAct, coordSymmSign, coordSymmPerm]
  · simpa [coordSymmAct, coordSymmSign, coordSymmPerm,
      Equiv.Perm.sign_mul, Equiv.swap_apply_def] using hf.cyclic q
  · simpa [coordSymmAct, coordSymmSign, coordSymmPerm,
      Equiv.Perm.sign_mul, Equiv.swap_apply_def] using hf.cyclicSq q
  · simpa [coordSymmAct, coordSymmSign, coordSymmPerm,
      Equiv.swap_apply_def] using hf.oddX q
  · simpa [coordSymmAct, coordSymmSign, coordSymmPerm,
      Equiv.swap_apply_def] using hf.rho q
  · simpa [coordSymmAct, coordSymmSign, coordSymmPerm,
      Equiv.swap_apply_def] using hf.oddY q

theorem coordinateAlt_eq_self {f : U4 → ℝ} (hf : PointAlt f) :
    coordinateAlt f = f := by
  funext q
  simp only [coordinateAlt]
  simp_rw [pointAlt_coordSymmAct hf, ← mul_assoc, coordSymmSign_sq, one_mul]
  simp [card_coordSymm]

@[simp]
theorem coordinateAlt_idempotent (f : U4 → ℝ) :
    coordinateAlt (coordinateAlt f) = coordinateAlt f :=
  coordinateAlt_eq_self (pointAlt_coordinateAlt f)

theorem coordinateAlt_add (f g : U4 → ℝ) :
    coordinateAlt (f + g) = coordinateAlt f + coordinateAlt g := by
  funext q
  simp only [coordinateAlt, Pi.add_apply]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  ring

theorem coordinateAlt_smul (c : ℝ) (f : U4 → ℝ) :
    coordinateAlt (c • f) = c • coordinateAlt f := by
  funext q
  simp only [coordinateAlt, Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ s : CoordSymm,
      coordSymmSign s * (c * f (coordSymmAct s q)) =
        c * (coordSymmSign s * f (coordSymmAct s q)) by
          intro s; ring]
  rw [← Finset.mul_sum]
  ring

/-! ## Alternation on a.e.-classes -/

/-- Nonsingularity of the six coordinate symmetries for a chosen smooth measure. -/
structure CoordSymmQuasiMeasurePreserving (μ4 : Measure U4) : Prop where
  qmp : ∀ s, Measure.QuasiMeasurePreserving (coordSymmAct s) μ4 μ4

/-- Concrete nonsingularity package for the full sixfold alternating average. -/
theorem concreteCoordSymmQuasiMeasurePreserving :
    CoordSymmQuasiMeasurePreserving measureU4 where
  qmp := coordSymmAct_quasiMeasurePreserving

/-- Coefficients of the normalized alternating average. -/
def coordinateAltCoeff (s : CoordSymm) : ℝ :=
  (1 / 6 : ℝ) * coordSymmSign s

variable {μ4 : Measure U4}

/-- Quotient-coordinate alternation on finite measurable classes. -/
noncomputable def Alt0 (hsymm : CoordSymmQuasiMeasurePreserving μ4) :
    L0 U4 μ4 →ₗ[ℝ] L0 U4 μ4 :=
  L0.weightedPullbackₗ coordSymmAct hsymm.qmp coordinateAltCoeff

theorem coeFn_Alt0 (hsymm : CoordSymmQuasiMeasurePreserving μ4) (f : L0 U4 μ4) :
    (Alt0 hsymm f : U4 → ℝ) =ᵐ[μ4] coordinateAlt f := by
  refine (L0.coeFn_weightedPullbackₗ coordSymmAct hsymm.qmp
    coordinateAltCoeff f).trans (Filter.Eventually.of_forall fun q => ?_)
  simp only [coordinateAltCoeff, coordinateAlt]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  ring

theorem coordinateAlt_ae_congr (hsymm : CoordSymmQuasiMeasurePreserving μ4)
    {f g : U4 → ℝ} (hfg : f =ᵐ[μ4] g) :
    coordinateAlt f =ᵐ[μ4] coordinateAlt g := by
  have hall : ∀ᵐ q ∂μ4, ∀ s : CoordSymm,
      f (coordSymmAct s q) = g (coordSymmAct s q) :=
    Filter.eventually_all.2 fun s => (hsymm.qmp s).ae hfg
  filter_upwards [hall] with q hq
  simp only [coordinateAlt]
  apply congrArg ((1 / 6 : ℝ) * ·)
  apply Finset.sum_congr rfl
  intro s hs
  rw [hq s]

@[simp]
theorem Alt0_idempotent (hsymm : CoordSymmQuasiMeasurePreserving μ4)
    (f : L0 U4 μ4) : Alt0 hsymm (Alt0 hsymm f) = Alt0 hsymm f := by
  apply AEEqFun.ext
  have hid : coordinateAlt (coordinateAlt f) =ᵐ[μ4] coordinateAlt f :=
    Filter.Eventually.of_forall fun q => congrFun (coordinateAlt_idempotent f) q
  exact (coeFn_Alt0 hsymm (Alt0 hsymm f)).trans
    ((coordinateAlt_ae_congr hsymm (coeFn_Alt0 hsymm f)).trans
      (hid.trans (coeFn_Alt0 hsymm f).symm))

/-- An a.e.-class is alternating precisely when it is fixed by normalized
coordinate alternation. -/
def AEMeasurableAlternating (hsymm : CoordSymmQuasiMeasurePreserving μ4)
    (f : L0 U4 μ4) : Prop :=
  Alt0 hsymm f = f

/-- Quotient-coordinate alternation on `L^∞`. -/
noncomputable def Altinfₗ (hsymm : CoordSymmQuasiMeasurePreserving μ4) :
    Linfty U4 μ4 →ₗ[ℝ] Linfty U4 μ4 :=
  Linfty.weightedPullbackₗ coordSymmAct hsymm.qmp coordinateAltCoeff

theorem coordinateAlt_coeff_abs_sum :
    ∑ s : CoordSymm, |coordinateAltCoeff s| = 1 := by
  simp [coordinateAltCoeff, abs_mul, abs_coordSymmSign, card_coordSymm]

theorem norm_Altinfₗ_le (hsymm : CoordSymmQuasiMeasurePreserving μ4)
    (f : Linfty U4 μ4) : ‖Altinfₗ hsymm f‖ ≤ ‖f‖ := by
  simpa [Altinfₗ, coordinateAlt_coeff_abs_sum] using
    Linfty.norm_weightedPullbackₗ_le coordSymmAct hsymm.qmp coordinateAltCoeff f

/-- Alternation is a continuous linear contraction on `L^∞`. -/
noncomputable def Altinf (hsymm : CoordSymmQuasiMeasurePreserving μ4) :
    Linfty U4 μ4 →L[ℝ] Linfty U4 μ4 :=
  (Altinfₗ hsymm).mkContinuous 1 fun f => by simpa using norm_Altinfₗ_le hsymm f

theorem norm_Altinf_le (hsymm : CoordSymmQuasiMeasurePreserving μ4) :
    ‖Altinf hsymm‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one fun f => by
    simpa using norm_Altinfₗ_le hsymm f

theorem coe_Altinfₗ (hsymm : CoordSymmQuasiMeasurePreserving μ4)
    (f : Linfty U4 μ4) :
    (Altinfₗ hsymm f : L0 U4 μ4) = Alt0 hsymm f.1 :=
  Linfty.coe_weightedPullbackₗ coordSymmAct hsymm.qmp coordinateAltCoeff f

@[simp]
theorem Altinf_idempotent (hsymm : CoordSymmQuasiMeasurePreserving μ4)
    (f : Linfty U4 μ4) :
    Altinf hsymm (Altinf hsymm f) = Altinf hsymm f := by
  apply Subtype.ext
  change (Altinfₗ hsymm (Altinfₗ hsymm f) : L0 U4 μ4) =
    (Altinfₗ hsymm f : L0 U4 μ4)
  rw [coe_Altinfₗ, coe_Altinfₗ]
  exact Alt0_idempotent hsymm f.1

/-! ## The algebraic constant-seven argument -/

/-- Once fibre integration supplies continuous regularization modulo a defect-sized
bounded function, all remaining steps in the measurable bounded-defect theorem are
finite-group averaging, the five-term norm estimate, and the continuous compact-return
theorem. -/
theorem measurable_bounded_defect_of_regularization
    {μ5 : Measure U5} [Measure.IsOpenPosMeasure μ5]
    (hface : Face4QuasiMeasurePreserving μ4 μ5)
    (hsymm : CoordSymmQuasiMeasurePreserving μ4)
    (hreg : HasContinuousRegularization (D0 hface))
    (f : L0 U4 μ4) (F : Linfty U5 μ5)
    (hF : D0 hface f = F.1)
    (hfAlt : AEMeasurableAlternating hsymm f) :
    ∃ fb : Linfty U4 μ4, fb.1 = f ∧ ‖fb‖ ≤ 7 * ‖F‖ := by
  obtain ⟨reg⟩ := hreg f F hF
  let g : U4 → ℝ := reg.representative
  have hg : Continuous g := reg.continuous
  let g0 : L0 U4 μ4 := continuousClass g hg
  let h : U4 → ℝ := coordinateAlt g
  have hhcont : Continuous h := continuous_coordinateAlt hg
  have hhAlt : PointAlt h := pointAlt_coordinateAlt g
  let h0 : L0 U4 μ4 := continuousClass h hhcont
  have hAltg0 : Alt0 hsymm g0 = h0 := by
    apply AEEqFun.ext
    exact (coeFn_Alt0 hsymm g0).trans
      ((coordinateAlt_ae_congr hsymm
        (coeFn_continuousClass (μ := μ4) g hg)).trans
          (coeFn_continuousClass (μ := μ4) h hhcont).symm)
  let err : Linfty U4 μ4 := Altinf hsymm reg.error
  have herrcoe : err.1 = f - h0 := by
    change (Altinfₗ hsymm reg.error : L0 U4 μ4) = f - h0
    rw [coe_Altinfₗ, reg.error_coe]
    change Alt0 hsymm (f - g0) = f - h0
    rw [map_sub, hfAlt, hAltg0]
  have herrnorm : ‖err‖ ≤ ‖F‖ := by
    calc
      ‖err‖ = ‖Altinfₗ hsymm reg.error‖ := rfl
      _ ≤ ‖reg.error‖ := norm_Altinfₗ_le hsymm reg.error
      _ ≤ ‖F‖ := reg.norm_error_le
  let G : Linfty U5 μ5 := F - Dinf hface err
  have hDerr : ‖Dinf hface err‖ ≤ 5 * ‖err‖ := by
    change ‖Dinfₗ hface err‖ ≤ 5 * ‖err‖
    exact norm_Dinfₗ_le hface err
  have hGnorm : ‖G‖ ≤ 6 * ‖F‖ := by
    calc
      ‖G‖ = ‖F - Dinf hface err‖ := rfl
      _ ≤ ‖F‖ + ‖Dinf hface err‖ := norm_sub_le _ _
      _ ≤ ‖F‖ + 5 * ‖err‖ := add_le_add le_rfl hDerr
      _ ≤ ‖F‖ + 5 * ‖F‖ := by gcongr
      _ = 6 * ‖F‖ := by ring
  have hGcoe : G.1 = D0 hface h0 := by
    change F.1 - (Dinfₗ hface err : L0 U5 μ5) = D0 hface h0
    rw [coe_Dinfₗ, ← hF, herrcoe, map_sub]
    abel
  have hGrep : (G : U5 → ℝ) =ᵐ[μ5] D h := by
    rw [show G.1 = D0 hface h0 from hGcoe]
    exact (coeFn_D0 hface h0).trans
      (D_ae_congr hface (coeFn_continuousClass (μ := μ4) h hhcont))
  have hDpointNorm : ∀ q : U5, |D h q| ≤ ‖G‖ :=
    Linfty.continuous_rep_norm_bound G (D h) (continuous_D hhcont) hGrep.symm
  have hDpoint : ∀ q : U5, |D h q| ≤ 6 * ‖F‖ :=
    fun q => (hDpointNorm q).trans hGnorm
  have hhpoint : ∀ q : U4, |h q| ≤ 6 * ‖F‖ :=
    continuous_local_to_global h hhcont hhAlt (6 * ‖F‖)
      (mul_nonneg (by norm_num) (norm_nonneg F)) hDpoint
  have hh0bound : ∀ᵐ q ∂μ4, ‖h0 q‖ ≤ 6 * ‖F‖ := by
    filter_upwards [coeFn_continuousClass (μ := μ4) h hhcont] with q hq
    rw [hq, Real.norm_eq_abs]
    exact hhpoint q
  have hh0mem : eLpNorm h0 ∞ μ4 < ∞ := by
    rw [eLpNorm_exponent_top]
    exact (eLpNormEssSup_le_of_ae_bound hh0bound).trans_lt ENNReal.ofReal_lt_top
  let hb : Linfty U4 μ4 := ⟨h0, hh0mem⟩
  have hbnorm : ‖hb‖ ≤ 6 * ‖F‖ := by
    rw [Lp.norm_def, eLpNorm_exponent_top]
    calc
      ENNReal.toReal (eLpNormEssSup (hb : U4 → ℝ) μ4) ≤
          ENNReal.toReal (ENNReal.ofReal (6 * ‖F‖)) :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top
          (eLpNormEssSup_le_of_ae_bound hh0bound)
      _ = 6 * ‖F‖ := ENNReal.toReal_ofReal
        (mul_nonneg (by norm_num) (norm_nonneg F))
  refine ⟨hb + err, ?_, ?_⟩
  · change h0 + err.1 = f
    rw [herrcoe]
    abel
  · calc
      ‖hb + err‖ ≤ ‖hb‖ + ‖err‖ := norm_add_le _ _
      _ ≤ 6 * ‖F‖ + ‖F‖ := add_le_add hbnorm herrnorm
      _ = 7 * ‖F‖ := by ring

/-- The quantitative lower bound on the alternating `L^∞` subspace. -/
theorem Dinf_bounded_below_of_regularization
    {μ5 : Measure U5} [Measure.IsOpenPosMeasure μ5]
    (hface : Face4QuasiMeasurePreserving μ4 μ5)
    (hsymm : CoordSymmQuasiMeasurePreserving μ4)
    (hreg : HasContinuousRegularization (D0 hface))
    (f : Linfty U4 μ4)
    (hfAlt : AEMeasurableAlternating hsymm f.1) :
    ‖f‖ ≤ 7 * ‖Dinf hface f‖ := by
  have hDcoe : D0 hface f.1 = (Dinf hface f).1 := by
    change D0 hface f.1 = (Dinfₗ hface f : L0 U5 μ5)
    exact (coe_Dinfₗ hface f).symm
  obtain ⟨fb, hfb, hbound⟩ :=
    measurable_bounded_defect_of_regularization hface hsymm hreg
      f.1 (Dinf hface f) hDcoe hfAlt
  have hfb_eq : fb = f := by
    apply Subtype.ext
    exact hfb
  simpa [hfb_eq] using hbound

/-- In particular, the measurable Pfaffian differential has trivial kernel on
alternating a.e.-classes whenever fibre regularization has been constructed. -/
theorem D0_injective_on_alternating_of_regularization
    {μ5 : Measure U5} [Measure.IsOpenPosMeasure μ5]
    (hface : Face4QuasiMeasurePreserving μ4 μ5)
    (hsymm : CoordSymmQuasiMeasurePreserving μ4)
    (hreg : HasContinuousRegularization (D0 hface))
    (f : L0 U4 μ4) (hfAlt : AEMeasurableAlternating hsymm f)
    (hf : D0 hface f = 0) : f = 0 := by
  have hf' : D0 hface f = (0 : Linfty U5 μ5).1 := by
    simpa using hf
  obtain ⟨fb, hfb, hbound⟩ :=
    measurable_bounded_defect_of_regularization hface hsymm hreg
      f 0 hf' hfAlt
  have hnorm : ‖fb‖ = 0 := by
    apply le_antisymm
    · simpa using hbound
    · exact norm_nonneg fb
  have hfbzero : fb = 0 := norm_eq_zero.mp hnorm
  rw [← hfb]
  exact congrArg Subtype.val hfbzero

/-! ## Unconditional form for the article's concrete measures -/

/-- The measurable bounded-defect theorem, with the article's constant `7`, for
the concrete normalized Gaussian measures.  All Pfaffian identities, rank
calculations, local boundedness, fibre averaging, and finite-group estimates have
been discharged; the only imported facts are the explicitly cited generic
coarea/fibre-integration inputs in `ExternalInputs`. -/
theorem concrete_measurable_bounded_defect
    (f : L0 U4 measureU4) (F : Linfty U5 measureU5)
    (hF : D0 concreteFace4QuasiMeasurePreserving f = F.1)
    (hfAlt : AEMeasurableAlternating
      concreteCoordSymmQuasiMeasurePreserving f) :
    ∃ fb : Linfty U4 measureU4, fb.1 = f ∧ ‖fb‖ ≤ 7 * ‖F‖ :=
  measurable_bounded_defect_of_regularization
    concreteFace4QuasiMeasurePreserving
    concreteCoordSymmQuasiMeasurePreserving
    concrete_hasContinuousRegularization f F hF hfAlt

/-- Quantitative lower bound for the concrete alternating `L∞` differential. -/
theorem concrete_Dinf_bounded_below
    (f : Linfty U4 measureU4)
    (hfAlt : AEMeasurableAlternating
      concreteCoordSymmQuasiMeasurePreserving f.1) :
    ‖f‖ ≤ 7 * ‖Dinf concreteFace4QuasiMeasurePreserving f‖ :=
  Dinf_bounded_below_of_regularization
    concreteFace4QuasiMeasurePreserving
    concreteCoordSymmQuasiMeasurePreserving
    concrete_hasContinuousRegularization f hfAlt

/-- Kernel triviality for the concrete measurable alternating differential. -/
theorem concrete_D0_injective_on_alternating
    (f : L0 U4 measureU4)
    (hfAlt : AEMeasurableAlternating
      concreteCoordSymmQuasiMeasurePreserving f)
    (hf : D0 concreteFace4QuasiMeasurePreserving f = 0) : f = 0 :=
  D0_injective_on_alternating_of_regularization
    concreteFace4QuasiMeasurePreserving
    concreteCoordSymmQuasiMeasurePreserving
    concrete_hasContinuousRegularization f hfAlt hf

end

end Pfaffian

end Sp4
