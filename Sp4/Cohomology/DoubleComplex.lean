import Mathlib

/-!
# A kernel-checked low-degree transgression

This file isolates the finite diagram chase used in the paper.  It does not invoke a
general spectral-sequence implementation.  The source is vertical cohomology in
bidegree `(3,1)` and the target is bottom-row horizontal cohomology in column five.
The hypotheses in `SingleTransgressionHypotheses` are precisely the low-degree
vanishing, restriction, and total-acyclicity statements consumed by the chase.
-/

namespace Sp4

noncomputable section

universe u v

/-- A first-quadrant double complex of modules, using the paper's convention that
both differentials raise degree and anticommute. -/
structure FirstQuadrantDoubleComplex (R : Type u) [CommRing R] where
  obj : ℕ → ℕ → ModuleCat.{v} R
  dv : ∀ p q, obj p q →ₗ[R] obj p (q + 1)
  dh : ∀ p q, obj p q →ₗ[R] obj (p + 1) q
  dv_sq : ∀ p q x, dv p (q + 1) (dv p q x) = 0
  dh_sq : ∀ p q x, dh (p + 1) q (dh p q x) = 0
  anticomm : ∀ p q x,
    dv (p + 1) q (dh p q x) + dh p (q + 1) (dv p q x) = 0

namespace FirstQuadrantDoubleComplex

variable {R : Type u} [CommRing R] (C : FirstQuadrantDoubleComplex R)

/-- Vertical cocycles in one bidegree. -/
def VerticalCocycles (p q : ℕ) : Submodule R (C.obj p q) :=
  LinearMap.ker (C.dv p q)

/-- Vertical boundaries in positive degree `q + 1`. -/
def VerticalBoundariesSucc (p q : ℕ) :
    Submodule R (C.VerticalCocycles p (q + 1)) :=
  (LinearMap.range (C.dv p q)).comap
    (C.VerticalCocycles p (q + 1)).subtype

/-- Vertical cohomology in positive degree `q + 1`. -/
abbrev VerticalHSucc (p q : ℕ) : Type _ :=
  (↑(C.VerticalCocycles p (q + 1)) : Type _) ⧸
    C.VerticalBoundariesSucc p q

/-- Degree-one vertical boundaries; retained as a readable specialization. -/
abbrev VerticalBoundariesOne (p : ℕ) := C.VerticalBoundariesSucc p 0

/-- First vertical cohomology in column `p`. -/
abbrev VerticalH1 (p : ℕ) : Type _ := C.VerticalHSucc p 0

/-- The horizontal differential restricted to positive-degree vertical
cocycles. -/
def verticalHorizontalCocycles (p q : ℕ) :
    C.VerticalCocycles p (q + 1) →ₗ[R]
      C.VerticalCocycles (p + 1) (q + 1) where
  toFun x := ⟨C.dh p (q + 1) x.1, by
    have h := C.anticomm p (q + 1) x.1
    rw [x.2, map_zero, add_zero] at h
    exact h⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' a x := by
    apply Subtype.ext
    exact map_smul _ _ _

/-- Horizontal differentiation sends a vertical boundary to a vertical
boundary.  The minus sign is exactly the anticommuting convention. -/
theorem verticalHorizontalCocycles_maps_boundaries (p q : ℕ) :
    C.VerticalBoundariesSucc p q ≤
      (C.VerticalBoundariesSucc (p + 1) q).comap
        (C.verticalHorizontalCocycles p q) := by
  intro x hx
  rcases hx with ⟨y, hy⟩
  change C.dv p q y = x.1 at hy
  change C.dh p (q + 1) x.1 ∈ LinearMap.range (C.dv (p + 1) q)
  refine ⟨-C.dh p q y, ?_⟩
  rw [map_neg]
  have h := C.anticomm p q y
  rw [hy] at h
  exact (eq_neg_of_add_eq_zero_right h).symm

/-- The first-page horizontal map on positive-degree vertical cohomology. -/
def verticalHorizontal (p q : ℕ) :
    C.VerticalHSucc p q →ₗ[R] C.VerticalHSucc (p + 1) q :=
  (C.VerticalBoundariesSucc p q).mapQ
    (C.VerticalBoundariesSucc (p + 1) q)
    (C.verticalHorizontalCocycles p q)
    (C.verticalHorizontalCocycles_maps_boundaries p q)

@[simp]
theorem verticalHorizontal_mk (p q : ℕ)
    (x : C.VerticalCocycles p (q + 1)) :
    C.verticalHorizontal p q (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (C.verticalHorizontalCocycles p q x) :=
  rfl

/-- The horizontal map restricted to vertical degree-zero cocycles. -/
def bottomHorizontal (p : ℕ) :
    C.VerticalCocycles p 0 →ₗ[R] C.VerticalCocycles (p + 1) 0 where
  toFun x := ⟨C.dh p 0 x.1, by
    have h := C.anticomm p 0 x.1
    rw [x.2, map_zero, add_zero] at h
    exact h⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' a x := by
    apply Subtype.ext
    exact map_smul _ _ _

/-- Bottom-row cocycles in column five. -/
def BottomFiveCocycles : Submodule R (C.VerticalCocycles 5 0) :=
  LinearMap.ker (C.bottomHorizontal 5)

/-- Bottom-row boundaries entering column five. -/
def BottomFiveBoundaries : Submodule R C.BottomFiveCocycles :=
  (LinearMap.range (C.bottomHorizontal 4)).comap C.BottomFiveCocycles.subtype

/-- The bottom-row cohomology in column five. -/
abbrev BottomH5 : Type _ :=
  (↑C.BottomFiveCocycles : Type _) ⧸ C.BottomFiveBoundaries

/-- A linear choice of the vertical primitive used to define transgression.  Such a
choice exists whenever the horizontal image of every `(3,1)` vertical cocycle is
vertically exact. -/
structure TransgressionLift where
  lift : C.VerticalCocycles 3 1 →ₗ[R] C.obj 4 0
  lift_spec : ∀ a, C.dv 4 0 (lift a) = C.dh 3 1 a.1

/-- Vanishing of first vertical cohomology in column four produces the
linear family of primitives required by the transgression.  The only choice
made here is a linear splitting of `dv`; over a field its range is a
projective module, so this splitting is supplied by ordinary linear algebra.

This theorem is useful for keeping the literature boundary at the intrinsic
cohomology statement `H¹ = 0`, rather than postulating the much stronger
cochain-level `TransgressionLift` as data. -/
noncomputable def transgressionLiftOfNextH1Zero
    [Module.Projective R (LinearMap.range (C.dv 4 0))]
    (hzero : ∀ x : C.VerticalH1 4, x = 0) : C.TransgressionLift := by
  let toRange : C.VerticalCocycles 3 1 →ₗ[R]
      LinearMap.range (C.dv 4 0) :=
    { toFun := fun a ↦ ⟨C.dh 3 1 a.1, by
        let z : C.VerticalCocycles 4 1 :=
          ⟨C.dh 3 1 a.1, by
            have h := C.anticomm 3 1 a.1
            rw [a.2, map_zero, add_zero] at h
            exact h⟩
        have hz : (Submodule.Quotient.mk z : C.VerticalH1 4) = 0 :=
          hzero _
        rw [Submodule.Quotient.mk_eq_zero] at hz
        change C.dh 3 1 a.1 ∈ LinearMap.range (C.dv 4 0) at hz
        exact hz⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        exact map_add _ _ _
      map_smul' := by
        intro r a
        apply Subtype.ext
        exact map_smul _ _ _ }
  let splitExists :=
    (C.dv 4 0).rangeRestrict.exists_rightInverse_of_surjective
      (C.dv 4 0).range_rangeRestrict
  let split := Classical.choose splitExists
  have hsplit := Classical.choose_spec splitExists
  refine ⟨split.comp toRange, ?_⟩
  intro a
  have h := LinearMap.congr_fun hsplit (toRange a)
  exact congrArg Subtype.val h

variable (L : C.TransgressionLift)

/-- The representative-level transgression `a ↦ d_h b`. -/
def rawTransgression : C.VerticalCocycles 3 1 →ₗ[R] C.BottomFiveCocycles where
  toFun a := ⟨⟨C.dh 4 0 (L.lift a), by
    have hanti := C.anticomm 4 0 (L.lift a)
    have hhsq := C.dh_sq 3 1 a.1
    rw [L.lift_spec, hhsq, add_zero] at hanti
    exact hanti⟩, by
      apply Subtype.ext
      exact C.dh_sq 4 0 (L.lift a)⟩
  map_add' a b := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  map_smul' r a := by
    apply Subtype.ext
    apply Subtype.ext
    simp

theorem rawTransgression_maps_boundaries :
    C.VerticalBoundariesOne 3 ≤
      C.BottomFiveBoundaries.comap (C.rawTransgression L) := by
  intro a ha
  rcases ha with ⟨c, hc⟩
  change C.dv 3 0 c = a.1 at hc
  let k : C.VerticalCocycles 4 0 := ⟨L.lift a + C.dh 3 0 c, by
    have hanti := C.anticomm 3 0 c
    change C.dv 4 0 (L.lift a + C.dh 3 0 c) = 0
    rw [map_add, L.lift_spec, ← hc]
    simpa [add_comm] using hanti⟩
  change (C.rawTransgression L a : C.VerticalCocycles 5 0) ∈
    LinearMap.range (C.bottomHorizontal 4)
  refine ⟨k, ?_⟩
  apply Subtype.ext
  change C.dh 4 0 (L.lift a + C.dh 3 0 c) = C.dh 4 0 (L.lift a)
  rw [map_add, C.dh_sq]
  simp

/-- The cochain-level transgression on quotient cohomology. -/
def transgression : C.VerticalH1 3 →ₗ[R] C.BottomH5 :=
  (C.VerticalBoundariesOne 3).mapQ C.BottomFiveBoundaries
    (C.rawTransgression L) (C.rawTransgression_maps_boundaries L)

@[simp]
theorem transgression_mk (a : C.VerticalCocycles 3 1) :
    C.transgression L (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (C.rawTransgression L a) :=
  rfl

/-- The quotient transgression is independent of the chosen vertical primitives. -/
theorem transgression_independent (L₁ L₂ : C.TransgressionLift) :
    C.transgression L₁ = C.transgression L₂ := by
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := (C.VerticalBoundariesOne 3).mkQ_surjective x
  change Submodule.Quotient.mk (C.rawTransgression L₁ a) =
    Submodule.Quotient.mk (C.rawTransgression L₂ a)
  apply QuotientAddGroup.eq_iff_sub_mem.2
  change (C.rawTransgression L₁ a - C.rawTransgression L₂ a :
      C.VerticalCocycles 5 0) ∈ LinearMap.range (C.bottomHorizontal 4)
  let k : C.VerticalCocycles 4 0 := ⟨L₁.lift a - L₂.lift a, by
    change C.dv 4 0 (L₁.lift a - L₂.lift a) = 0
    rw [map_sub, L₁.lift_spec, L₂.lift_spec, sub_self]⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  change C.dh 4 0 (L₁.lift a - L₂.lift a) =
    C.dh 4 0 (L₁.lift a) - C.dh 4 0 (L₂.lift a)
  rw [map_sub]

/-! The two total-complex exactness statements are written componentwise.  This
prevents a hidden appeal to spectral-sequence convergence in the proof below. -/

/-- A total-degree-three primitive of the special total-degree-four cocycle
`a - b`. -/
structure TotalPrimitive4 (a : C.obj 3 1) (b : C.obj 4 0) where
  c03 : C.obj 0 3
  c12 : C.obj 1 2
  c21 : C.obj 2 1
  c30 : C.obj 3 0
  eq04 : C.dv 0 3 c03 = 0
  eq13 : C.dh 0 3 c03 + C.dv 1 2 c12 = 0
  eq22 : C.dh 1 2 c12 + C.dv 2 1 c21 = 0
  eq31 : C.dh 2 1 c21 + C.dv 3 0 c30 = a
  eq40 : C.dh 3 0 c30 = -b

/-- A total-degree-four primitive of a bottom-row total-degree-five cocycle. -/
structure TotalPrimitive5 (z : C.obj 5 0) where
  c04 : C.obj 0 4
  c13 : C.obj 1 3
  c22 : C.obj 2 2
  c31 : C.obj 3 1
  c40 : C.obj 4 0
  eq05 : C.dv 0 4 c04 = 0
  eq14 : C.dh 0 4 c04 + C.dv 1 3 c13 = 0
  eq23 : C.dh 1 3 c13 + C.dv 2 2 c22 = 0
  eq32 : C.dh 2 2 c22 + C.dv 3 1 c31 = 0
  eq41 : C.dh 3 1 c31 + C.dv 4 0 c40 = 0
  eq50 : C.dh 4 0 c40 = z

/-- Exactness of every augmented horizontal row.  The first field is
exactness at the augmentation term (injectivity of the first horizontal map);
the second is exactness in every positive column.  This is the precise
algebraic output of the measurable slicing argument in the article. -/
structure HorizontalExact : Prop where
  at_zero : ∀ q (x : C.obj 0 q), C.dh 0 q x = 0 → x = 0
  at_succ : ∀ p q (x : C.obj (p + 1) q),
    C.dh (p + 1) q x = 0 →
      ∃ y : C.obj p q, C.dh p q y = x

/-- The total-degree-four exactness datum used by transgression follows by an
explicit zig-zag through an exact horizontal row.  Thus total acyclicity is not
an independent page hypothesis. -/
theorem totalPrimitive4_of_horizontalExact
    (HE : C.HorizontalExact)
    (a : C.obj 3 1) (b : C.obj 4 0)
    (ha : C.dv 3 1 a = 0)
    (hab : C.dv 4 0 b = C.dh 3 1 a)
    (hb : C.dh 4 0 b = 0) :
    Nonempty (C.TotalPrimitive4 a b) := by
  have hnegb : C.dh 4 0 (-b) = 0 := by simp [hb]
  obtain ⟨c30, hc30⟩ := HE.at_succ 3 0 (-b) hnegb
  let x31 : C.obj 3 1 := a - C.dv 3 0 c30
  have hx31 : C.dh 3 1 x31 = 0 := by
    have hanti := C.anticomm 3 0 c30
    dsimp [x31]
    rw [map_sub, ← hab]
    have hc30' : C.dh 3 0 c30 = -b := hc30
    rw [hc30', map_neg] at hanti
    rw [eq_neg_of_add_eq_zero_right hanti]
    abel
  obtain ⟨c21, hc21⟩ := HE.at_succ 2 1 x31 hx31
  let x22 : C.obj 2 2 := -C.dv 2 1 c21
  have hx22 : C.dh 2 2 x22 = 0 := by
    have hanti := C.anticomm 2 1 c21
    have hx31v : C.dv 3 1 x31 = 0 := by
      dsimp [x31]
      rw [map_sub, ha, C.dv_sq, sub_zero]
    rw [hc21] at hanti
    rw [hx31v, zero_add] at hanti
    dsimp [x22]
    simpa using hanti
  obtain ⟨c12, hc12⟩ := HE.at_succ 1 2 x22 hx22
  let x13 : C.obj 1 3 := -C.dv 1 2 c12
  have hx13 : C.dh 1 3 x13 = 0 := by
    have hanti := C.anticomm 1 2 c12
    have hx22v : C.dv 2 2 x22 = 0 := by
      dsimp [x22]
      rw [map_neg, C.dv_sq, neg_zero]
    rw [hc12] at hanti
    rw [hx22v, zero_add] at hanti
    dsimp [x13]
    simpa using hanti
  obtain ⟨c03, hc03⟩ := HE.at_succ 0 3 x13 hx13
  have hc03v : C.dv 0 3 c03 = 0 := by
    apply HE.at_zero 4
    have hanti := C.anticomm 0 3 c03
    have hfirst : C.dv 1 3 (C.dh 0 3 c03) = 0 := by
      rw [hc03]
      dsimp [x13]
      rw [map_neg, C.dv_sq, neg_zero]
    simpa [hfirst] using hanti
  exact ⟨{
    c03 := c03
    c12 := c12
    c21 := c21
    c30 := c30
    eq04 := hc03v
    eq13 := by rw [hc03]; simp [x13]
    eq22 := by rw [hc12]; simp [x22]
    eq31 := by rw [hc21]; dsimp [x31]; abel
    eq40 := hc30 }⟩

/-- The corresponding total-degree-five primitive, again constructed solely
from horizontal row exactness. -/
theorem totalPrimitive5_of_horizontalExact
    (HE : C.HorizontalExact)
    (z : C.obj 5 0) (hzv : C.dv 5 0 z = 0)
    (hzh : C.dh 5 0 z = 0) :
    Nonempty (C.TotalPrimitive5 z) := by
  obtain ⟨c40, hc40⟩ := HE.at_succ 4 0 z hzh
  let x41 : C.obj 4 1 := -C.dv 4 0 c40
  have hx41 : C.dh 4 1 x41 = 0 := by
    have hanti := C.anticomm 4 0 c40
    have hfirst : C.dv 5 0 (C.dh 4 0 c40) = 0 := by
      rw [hc40]
      exact hzv
    dsimp [x41]
    simpa [hfirst] using hanti
  obtain ⟨c31, hc31⟩ := HE.at_succ 3 1 x41 hx41
  let x32 : C.obj 3 2 := -C.dv 3 1 c31
  have hx32 : C.dh 3 2 x32 = 0 := by
    have hanti := C.anticomm 3 1 c31
    rw [hc31] at hanti
    have hx41v : C.dv 4 1 x41 = 0 := by
      dsimp [x41]
      rw [map_neg, C.dv_sq, neg_zero]
    rw [hx41v, zero_add] at hanti
    dsimp [x32]
    simpa using hanti
  obtain ⟨c22, hc22⟩ := HE.at_succ 2 2 x32 hx32
  let x23 : C.obj 2 3 := -C.dv 2 2 c22
  have hx23 : C.dh 2 3 x23 = 0 := by
    have hanti := C.anticomm 2 2 c22
    rw [hc22] at hanti
    have hx32v : C.dv 3 2 x32 = 0 := by
      dsimp [x32]
      rw [map_neg, C.dv_sq, neg_zero]
    rw [hx32v, zero_add] at hanti
    dsimp [x23]
    simpa using hanti
  obtain ⟨c13, hc13⟩ := HE.at_succ 1 3 x23 hx23
  let x14 : C.obj 1 4 := -C.dv 1 3 c13
  have hx14 : C.dh 1 4 x14 = 0 := by
    have hanti := C.anticomm 1 3 c13
    rw [hc13] at hanti
    have hx23v : C.dv 2 3 x23 = 0 := by
      dsimp [x23]
      rw [map_neg, C.dv_sq, neg_zero]
    rw [hx23v, zero_add] at hanti
    dsimp [x14]
    simpa using hanti
  obtain ⟨c04, hc04⟩ := HE.at_succ 0 4 x14 hx14
  have hc04v : C.dv 0 4 c04 = 0 := by
    apply HE.at_zero 5
    have hanti := C.anticomm 0 4 c04
    have hfirst : C.dv 1 4 (C.dh 0 4 c04) = 0 := by
      rw [hc04]
      dsimp [x14]
      rw [map_neg, C.dv_sq, neg_zero]
    simpa [hfirst] using hanti
  exact ⟨{
    c04 := c04
    c13 := c13
    c22 := c22
    c31 := c31
    c40 := c40
    eq05 := hc04v
    eq14 := by rw [hc04]; simp [x14]
    eq23 := by rw [hc13]; simp [x23]
    eq32 := by rw [hc22]; simp [x32]
    eq41 := by rw [hc31]; simp [x41]
    eq50 := hc40 }⟩

/-- Exactly the low-degree hypotheses used in the single-surviving-
transgression argument. -/
structure SingleTransgressionHypotheses : Prop where
  totalExact4 : ∀ (a : C.obj 3 1) (b : C.obj 4 0),
    C.dv 3 1 a = 0 → C.dv 4 0 b = C.dh 3 1 a → C.dh 4 0 b = 0 →
      Nonempty (C.TotalPrimitive4 a b)
  totalExact5 : ∀ z : C.obj 5 0,
    C.dv 5 0 z = 0 → C.dh 5 0 z = 0 →
      Nonempty (C.TotalPrimitive5 z)
  restrictionH3_injective : ∀ (x : C.obj 0 3),
    C.dv 0 3 x = 0 →
    (∃ y : C.obj 1 2, C.dh 0 3 x = C.dv 1 2 y) →
      ∃ y : C.obj 0 2, x = C.dv 0 2 y
  restrictionH3_surjective : ∀ (x : C.obj 1 3),
    C.dv 1 3 x = 0 →
      ∃ y : C.obj 0 3, C.dv 0 3 y = 0 ∧
        ∃ w : C.obj 1 2, x = C.dh 0 3 y + C.dv 1 2 w
  H2Q_zero : ∀ (x : C.obj 1 2), C.dv 1 2 x = 0 →
    ∃ y : C.obj 1 1, x = C.dv 1 1 y
  H2L_zero : ∀ (x : C.obj 2 2), C.dv 2 2 x = 0 →
    ∃ y : C.obj 2 1, x = C.dv 2 1 y
  H4G_zero : ∀ (x : C.obj 0 4), C.dv 0 4 x = 0 →
    ∃ y : C.obj 0 3, x = C.dv 0 3 y
  incomingH1_zero : ∀ (x : C.obj 2 1), C.dv 2 1 x = 0 →
    ∃ y : C.obj 3 0, C.dh 2 1 x = C.dv 3 0 y

/-- The genuine first-page and low-degree cohomology inputs.  Unlike
`SingleTransgressionHypotheses`, this structure does not assume total
acyclicity: the latter is derived from `HorizontalExact` by the two explicit
zig-zags above. -/
structure TransgressionPageHypotheses : Prop where
  restrictionH3_injective : ∀ (x : C.obj 0 3),
    C.dv 0 3 x = 0 →
    (∃ y : C.obj 1 2, C.dh 0 3 x = C.dv 1 2 y) →
      ∃ y : C.obj 0 2, x = C.dv 0 2 y
  restrictionH3_surjective : ∀ (x : C.obj 1 3),
    C.dv 1 3 x = 0 →
      ∃ y : C.obj 0 3, C.dv 0 3 y = 0 ∧
        ∃ w : C.obj 1 2, x = C.dh 0 3 y + C.dv 1 2 w
  H2Q_zero : ∀ (x : C.obj 1 2), C.dv 1 2 x = 0 →
    ∃ y : C.obj 1 1, x = C.dv 1 1 y
  H2L_zero : ∀ (x : C.obj 2 2), C.dv 2 2 x = 0 →
    ∃ y : C.obj 2 1, x = C.dv 2 1 y
  H4G_zero : ∀ (x : C.obj 0 4), C.dv 0 4 x = 0 →
    ∃ y : C.obj 0 3, x = C.dv 0 3 y
  incomingH1_zero : ∀ (x : C.obj 2 1), C.dv 2 1 x = 0 →
    ∃ y : C.obj 3 0, C.dh 2 1 x = C.dv 3 0 y

/-- The same page information stated intrinsically on vertical cohomology.

These are the statements supplied by the stabilizer computations: the
degree-three restriction is an isomorphism, the three indicated cohomology
groups vanish, and the alternating sum of the three degree-one face
restrictions is zero.  Unlike `TransgressionPageHypotheses`, none of these
fields asks for a representative-level primitive. -/
structure TransgressionCohomologyInputs : Prop where
  restrictionH3_bijective : Function.Bijective (C.verticalHorizontal 0 2)
  H2Q_zero : ∀ x : C.VerticalHSucc 1 1, x = 0
  H2L_zero : ∀ x : C.VerticalHSucc 2 1, x = 0
  H4G_zero : ∀ x : C.VerticalHSucc 0 3, x = 0
  incomingH1_zero : C.verticalHorizontal 2 0 = 0

/-- Pass from quotient-level cohomology facts to the concrete primitives used
by the transgression chase.  This is the point where equality to zero in a
cohomology quotient is unfolded into an actual coboundary witness. -/
theorem transgressionPageHypothesesOfCohomology
    (P : C.TransgressionCohomologyInputs) :
    C.TransgressionPageHypotheses where
  restrictionH3_injective := by
    intro x hx hres
    let z : C.VerticalCocycles 0 3 := ⟨x, hx⟩
    have hzmap : C.verticalHorizontal 0 2
        (Submodule.Quotient.mk z) = 0 := by
      rw [C.verticalHorizontal_mk, Submodule.Quotient.mk_eq_zero]
      change C.dh 0 3 x ∈ LinearMap.range (C.dv 1 2)
      obtain ⟨y, hy⟩ := hres
      exact ⟨y, hy.symm⟩
    have hzzero : (Submodule.Quotient.mk z : C.VerticalHSucc 0 2) = 0 :=
      P.restrictionH3_bijective.1 <| by
        simpa using hzmap
    rw [Submodule.Quotient.mk_eq_zero] at hzzero
    change x ∈ LinearMap.range (C.dv 0 2) at hzzero
    obtain ⟨y, hy⟩ := hzzero
    exact ⟨y, hy.symm⟩
  restrictionH3_surjective := by
    intro x hx
    let z : C.VerticalCocycles 1 3 := ⟨x, hx⟩
    obtain ⟨a, ha⟩ := P.restrictionH3_bijective.2
      (Submodule.Quotient.mk z)
    obtain ⟨y, rfl⟩ := (C.VerticalBoundariesSucc 0 2).mkQ_surjective a
    change C.verticalHorizontal 0 2 (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk z at ha
    rw [C.verticalHorizontal_mk] at ha
    have hmem := QuotientAddGroup.eq_iff_sub_mem.mp ha
    change C.dh 0 3 y.1 - x ∈ LinearMap.range (C.dv 1 2) at hmem
    obtain ⟨w, hw⟩ := hmem
    refine ⟨y.1, y.2, -w, ?_⟩
    rw [map_neg, hw]
    module
  H2Q_zero := by
    intro x hx
    let z : C.VerticalCocycles 1 2 := ⟨x, hx⟩
    have hz := P.H2Q_zero
      (Submodule.Quotient.mk z : C.VerticalHSucc 1 1)
    rw [Submodule.Quotient.mk_eq_zero] at hz
    change x ∈ LinearMap.range (C.dv 1 1) at hz
    obtain ⟨y, hy⟩ := hz
    exact ⟨y, hy.symm⟩
  H2L_zero := by
    intro x hx
    let z : C.VerticalCocycles 2 2 := ⟨x, hx⟩
    have hz := P.H2L_zero
      (Submodule.Quotient.mk z : C.VerticalHSucc 2 1)
    rw [Submodule.Quotient.mk_eq_zero] at hz
    change x ∈ LinearMap.range (C.dv 2 1) at hz
    obtain ⟨y, hy⟩ := hz
    exact ⟨y, hy.symm⟩
  H4G_zero := by
    intro x hx
    let z : C.VerticalCocycles 0 4 := ⟨x, hx⟩
    have hz := P.H4G_zero
      (Submodule.Quotient.mk z : C.VerticalHSucc 0 3)
    rw [Submodule.Quotient.mk_eq_zero] at hz
    change x ∈ LinearMap.range (C.dv 0 3) at hz
    obtain ⟨y, hy⟩ := hz
    exact ⟨y, hy.symm⟩
  incomingH1_zero := by
    intro x hx
    let z : C.VerticalCocycles 2 1 := ⟨x, hx⟩
    have hz : C.verticalHorizontal 2 0
        (Submodule.Quotient.mk z) = 0 := by
      rw [P.incomingH1_zero]
      rfl
    rw [C.verticalHorizontal_mk, Submodule.Quotient.mk_eq_zero] at hz
    change C.dh 2 1 x ∈ LinearMap.range (C.dv 3 0) at hz
    obtain ⟨y, hy⟩ := hz
    exact ⟨y, hy.symm⟩

/-- Assemble exactly the hypotheses consumed by the kernel/range chase.  The
two total primitives are constructed in Lean from row exactness rather than
being supplied by a literature interface. -/
theorem singleTransgressionHypothesesOf
    (HE : C.HorizontalExact) (P : C.TransgressionPageHypotheses) :
    C.SingleTransgressionHypotheses where
  totalExact4 := C.totalPrimitive4_of_horizontalExact HE
  totalExact5 := C.totalPrimitive5_of_horizontalExact HE
  restrictionH3_injective := P.restrictionH3_injective
  restrictionH3_surjective := P.restrictionH3_surjective
  H2Q_zero := P.H2Q_zero
  H2L_zero := P.H2L_zero
  H4G_zero := P.H4G_zero
  incomingH1_zero := P.incomingH1_zero

variable (H : C.SingleTransgressionHypotheses)

include H

/-- Kernel calculation for the transgression, displayed as the component chase
through total degree four. -/
theorem transgression_injective : Function.Injective (C.transgression L) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro x hx
    change C.transgression L x = 0 at hx
    obtain ⟨a, rfl⟩ := (C.VerticalBoundariesOne 3).mkQ_surjective x
    change Submodule.Quotient.mk a ∈ (⊥ : Submodule R (C.VerticalH1 3))
    rw [Submodule.mem_bot]
    change Submodule.Quotient.mk (C.rawTransgression L a) = 0 at hx
    rw [Submodule.Quotient.mk_eq_zero] at hx
    change (C.rawTransgression L a : C.VerticalCocycles 5 0) ∈
      LinearMap.range (C.bottomHorizontal 4) at hx
    rcases hx with ⟨k, hk⟩
    let b : C.obj 4 0 := L.lift a - k.1
    have hbvert : C.dv 4 0 b = C.dh 3 1 a.1 := by
      rw [map_sub, L.lift_spec, k.2, sub_zero]
    have hbhoriz : C.dh 4 0 b = 0 := by
      change C.dh 4 0 (L.lift a - k.1) = 0
      rw [map_sub]
      have hk' := congrArg Subtype.val hk
      change C.dh 4 0 k.1 = C.dh 4 0 (L.lift a) at hk'
      rw [hk']
      exact sub_self _
    obtain ⟨P⟩ := H.totalExact4 a.1 b a.2 hbvert hbhoriz
    have hc03boundary : ∃ y : C.obj 0 2, P.c03 = C.dv 0 2 y := by
      apply H.restrictionH3_injective P.c03 P.eq04
      refine ⟨-P.c12, ?_⟩
      rw [map_neg]
      exact eq_neg_of_add_eq_zero_left P.eq13
    rcases hc03boundary with ⟨y02, hy02⟩
    let c12' : C.obj 1 2 := P.c12 - C.dh 0 2 y02
    have hc12' : C.dv 1 2 c12' = 0 := by
      have hanti := C.anticomm 0 2 y02
      have hEq := P.eq13
      rw [hy02] at hEq
      dsimp [c12']
      rw [map_sub, eq_neg_of_add_eq_zero_right hEq,
        eq_neg_of_add_eq_zero_left hanti, sub_self]
    obtain ⟨y11, hy11⟩ := H.H2Q_zero c12' hc12'
    let c21' : C.obj 2 1 := P.c21 - C.dh 1 1 y11
    have hc21' : C.dv 2 1 c21' = 0 := by
      have hanti := C.anticomm 1 1 y11
      have hc12 : P.c12 = C.dh 0 2 y02 + C.dv 1 1 y11 := by
        rw [← hy11]
        dsimp [c12']
        abel
      dsimp [c21']
      rw [map_sub]
      have hEq := P.eq22
      rw [hc12, map_add, C.dh_sq, zero_add] at hEq
      rw [eq_neg_of_add_eq_zero_right hEq,
        eq_neg_of_add_eq_zero_left hanti, sub_self]
    obtain ⟨y30, hy30⟩ := H.incomingH1_zero c21' hc21'
    rw [Submodule.Quotient.mk_eq_zero]
    change a.1 ∈ LinearMap.range (C.dv 3 0)
    refine ⟨y30 + P.c30, ?_⟩
    have hc21 : P.c21 = c21' + C.dh 1 1 y11 := by
      dsimp [c21']
      abel
    rw [map_add]
    have hEq := P.eq31
    rw [hc21, map_add, C.dh_sq, add_zero, hy30] at hEq
    exact hEq
  · exact bot_le

/-- Range calculation for the transgression, displayed as the component chase
through total degree five. -/
theorem transgression_surjective : Function.Surjective (C.transgression L) := by
  intro x
  obtain ⟨z, rfl⟩ := (C.BottomFiveBoundaries).mkQ_surjective x
  obtain ⟨P⟩ := H.totalExact5 z.1.1 z.1.2 (by
    have hz := z.2
    exact congrArg Subtype.val hz)
  obtain ⟨y03, hy03⟩ := H.H4G_zero P.c04 P.eq05
  let c13' : C.obj 1 3 := P.c13 - C.dh 0 3 y03
  have hc13' : C.dv 1 3 c13' = 0 := by
    have hanti := C.anticomm 0 3 y03
    have hEq := P.eq14
    rw [hy03] at hEq
    dsimp [c13']
    rw [map_sub, eq_neg_of_add_eq_zero_right hEq,
      eq_neg_of_add_eq_zero_left hanti, sub_self]
  obtain ⟨y03', hy03'cycle, y12, hy12⟩ :=
    H.restrictionH3_surjective c13' hc13'
  let c22' : C.obj 2 2 := P.c22 - C.dh 1 2 y12
  have hc22' : C.dv 2 2 c22' = 0 := by
    have hanti := C.anticomm 1 2 y12
    have hc13 : P.c13 = C.dh 0 3 y03 + C.dh 0 3 y03' +
        C.dv 1 2 y12 := by
      calc
        P.c13 = c13' + C.dh 0 3 y03 := by
          dsimp [c13']
          abel
        _ = C.dh 0 3 y03 + C.dh 0 3 y03' + C.dv 1 2 y12 := by
          rw [hy12]
          abel
    rw [map_sub]
    have hEq := P.eq23
    rw [hc13, map_add, map_add, C.dh_sq, C.dh_sq, zero_add,
      zero_add] at hEq
    rw [eq_neg_of_add_eq_zero_right hEq,
      eq_neg_of_add_eq_zero_left hanti, sub_self]
  obtain ⟨y21, hy21⟩ := H.H2L_zero c22' hc22'
  let aVal : C.obj 3 1 := -P.c31 + C.dh 2 1 y21
  have haCycle : C.dv 3 1 aVal = 0 := by
    have hanti := C.anticomm 2 1 y21
    have hc22 : P.c22 = C.dh 1 2 y12 + C.dv 2 1 y21 := by
      rw [← hy21]
      dsimp [c22']
      abel
    rw [map_add, map_neg, eq_neg_of_add_eq_zero_left hanti]
    have hEq := P.eq32
    rw [hc22, map_add, C.dh_sq, zero_add] at hEq
    rw [eq_neg_of_add_eq_zero_left hEq]
    abel
  let a : C.VerticalCocycles 3 1 := ⟨aVal, haCycle⟩
  refine ⟨Submodule.Quotient.mk a, ?_⟩
  rw [C.transgression_mk L]
  apply QuotientAddGroup.eq_iff_sub_mem.2
  change (C.rawTransgression L a - z : C.VerticalCocycles 5 0) ∈
    LinearMap.range (C.bottomHorizontal 4)
  let k : C.VerticalCocycles 4 0 := ⟨L.lift a - P.c40, by
    have haDh : C.dh 3 1 aVal = C.dv 4 0 P.c40 := by
      dsimp [aVal]
      rw [map_add, map_neg, C.dh_sq, add_zero]
      exact neg_eq_of_add_eq_zero_right P.eq41
    change C.dv 4 0 (L.lift a - P.c40) = 0
    rw [map_sub, L.lift_spec, haDh, sub_self]⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  change C.dh 4 0 (L.lift a - P.c40) =
    C.dh 4 0 (L.lift a) - z.1.1
  rw [map_sub, P.eq50]

/-- The single surviving low-degree transgression is an isomorphism.  This is
the paper's page argument, proved here without a trusted spectral sequence. -/
def singleTransgressionEquiv : C.VerticalH1 3 ≃ₗ[R] C.BottomH5 :=
  LinearEquiv.ofBijective (C.transgression L)
    ⟨C.transgression_injective L H, C.transgression_surjective L H⟩

end FirstQuadrantDoubleComplex

end

end Sp4
