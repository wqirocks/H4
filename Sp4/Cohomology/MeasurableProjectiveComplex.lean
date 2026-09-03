import Sp4.Cohomology.MeasurableProjectiveCoordinates
import Sp4.Cohomology.PfaffianComplex

/-!
# The measurable projective-action complex in Pfaffian coordinates

This file transports the concrete Pfaffian differentials to the actual subspaces of
effective-group invariant `L⁰` and `L∞` classes on generic projective configurations.
The definitions are accompanied by representative-level homogeneous face formulas;
thus the comparison is not merely an abstract conjugation of vector spaces.
-/

namespace Sp4
namespace ProjectiveAction

open MeasureTheory OrbitChain Pfaffian

noncomputable section

/-! ## Coordinate representatives -/

theorem coe_coordinateInvariantL0Equiv4 (f : L0 U4 measureU4) :
    ((coordinateInvariantL0Equiv4 f).1 : GenericConfig 4 → ℝ) =ᵐ[measureGeneric4]
      (f : U4 → ℝ) ∘ orbitCoord4 := by
  change
    (L0.pullbackₗ orbitCoord4 orbitCoord4_quasiMeasurePreserving f :
        GenericConfig 4 → ℝ) =ᵐ[measureGeneric4]
      (f : U4 → ℝ) ∘ orbitCoord4
  exact L0.coe_pullbackₗ orbitCoord4 orbitCoord4_quasiMeasurePreserving f

theorem coe_coordinateInvariantL0Equiv5 (f : L0 U5 measureU5) :
    ((coordinateInvariantL0Equiv5 f).1 : GenericConfig 5 → ℝ) =ᵐ[measureGeneric5]
      (f : U5 → ℝ) ∘ orbitCoord5 := by
  change
    (L0.pullbackₗ orbitCoord5 orbitCoord5_quasiMeasurePreserving f :
        GenericConfig 5 → ℝ) =ᵐ[measureGeneric5]
      (f : U5 → ℝ) ∘ orbitCoord5
  exact L0.coe_pullbackₗ orbitCoord5 orbitCoord5_quasiMeasurePreserving f

theorem coe_coordinateInvariantL0Equiv6 (f : L0 U6 measureU6) :
    ((coordinateInvariantL0Equiv6 f).1 : GenericConfig 6 → ℝ) =ᵐ[measureGeneric6]
      (f : U6 → ℝ) ∘ orbitCoord6 := by
  change
    (L0.pullbackₗ orbitCoord6 orbitCoord6_quasiMeasurePreserving f :
        GenericConfig 6 → ℝ) =ᵐ[measureGeneric6]
      (f : U6 → ℝ) ∘ orbitCoord6
  exact L0.coe_pullbackₗ orbitCoord6 orbitCoord6_quasiMeasurePreserving f

theorem coe_coordinateInvariantLinftyEquiv4 (f : Linfty U4 measureU4) :
    ((coordinateInvariantLinftyEquiv4 f).1 : GenericConfig 4 → ℝ) =ᵐ[measureGeneric4]
      (f : U4 → ℝ) ∘ orbitCoord4 := by
  change
    (Linfty.pullbackₗ orbitCoord4 orbitCoord4_quasiMeasurePreserving f :
        GenericConfig 4 → ℝ) =ᵐ[measureGeneric4]
      (f : U4 → ℝ) ∘ orbitCoord4
  exact Linfty.coeFn_pullbackₗ orbitCoord4 orbitCoord4_quasiMeasurePreserving f

theorem coe_coordinateInvariantLinftyEquiv5 (f : Linfty U5 measureU5) :
    ((coordinateInvariantLinftyEquiv5 f).1 : GenericConfig 5 → ℝ) =ᵐ[measureGeneric5]
      (f : U5 → ℝ) ∘ orbitCoord5 := by
  change
    (Linfty.pullbackₗ orbitCoord5 orbitCoord5_quasiMeasurePreserving f :
        GenericConfig 5 → ℝ) =ᵐ[measureGeneric5]
      (f : U5 → ℝ) ∘ orbitCoord5
  exact Linfty.coeFn_pullbackₗ orbitCoord5 orbitCoord5_quasiMeasurePreserving f

theorem coe_coordinateInvariantLinftyEquiv6 (f : Linfty U6 measureU6) :
    ((coordinateInvariantLinftyEquiv6 f).1 : GenericConfig 6 → ℝ) =ᵐ[measureGeneric6]
      (f : U6 → ℝ) ∘ orbitCoord6 := by
  change
    (Linfty.pullbackₗ orbitCoord6 orbitCoord6_quasiMeasurePreserving f :
        GenericConfig 6 → ℝ) =ᵐ[measureGeneric6]
      (f : U6 → ℝ) ∘ orbitCoord6
  exact Linfty.coeFn_pullbackₗ orbitCoord6 orbitCoord6_quasiMeasurePreserving f

/-! ## The actual invariant differentials -/

/-- The four-to-five differential on actual invariant measurable classes. -/
def actionD0 : ActionInvariantL0_4 →ₗ[ℝ] ActionInvariantL0_5 :=
  coordinateInvariantL0Equiv5.toLinearMap.comp
    ((D0 concreteFace4QuasiMeasurePreserving).comp
      coordinateInvariantL0Equiv4.symm.toLinearMap)

/-- The five-to-six differential on actual invariant measurable classes. -/
def actionE0 : ActionInvariantL0_5 →ₗ[ℝ] ActionInvariantL0_6 :=
  coordinateInvariantL0Equiv6.toLinearMap.comp
    ((E0 concreteFace5QuasiMeasurePreserving).comp
      coordinateInvariantL0Equiv5.symm.toLinearMap)

@[simp]
theorem actionD0_coordinate (f : L0 U4 measureU4) :
    actionD0 (coordinateInvariantL0Equiv4 f) =
      coordinateInvariantL0Equiv5
        (D0 concreteFace4QuasiMeasurePreserving f) := by
  simp [actionD0]

@[simp]
theorem actionE0_coordinate (f : L0 U5 measureU5) :
    actionE0 (coordinateInvariantL0Equiv5 f) =
      coordinateInvariantL0Equiv6
        (E0 concreteFace5QuasiMeasurePreserving f) := by
  simp [actionE0]

/-- The transported measurable operators form a complex. -/
theorem actionE0_actionD0 (F : ActionInvariantL0_4) :
    actionE0 (actionD0 F) = 0 := by
  let f := coordinateInvariantL0Equiv4.symm F
  have hF : F = coordinateInvariantL0Equiv4 f := by
    simpa [f]
  rw [hF, actionD0_coordinate, actionE0_coordinate,
    E0_D0 concreteFace4QuasiMeasurePreserving
      concreteFace5QuasiMeasurePreserving]
  exact LinearEquiv.map_zero coordinateInvariantL0Equiv6

/-- The four-to-five differential on actual invariant essentially bounded classes. -/
def actionDinf : ActionInvariantLinfty_4 →ₗ[ℝ] ActionInvariantLinfty_5 :=
  coordinateInvariantLinftyEquiv5.toLinearMap.comp
    ((Dinfₗ concreteFace4QuasiMeasurePreserving).comp
      coordinateInvariantLinftyEquiv4.symm.toLinearMap)

/-- The five-to-six differential on actual invariant essentially bounded classes. -/
def actionEinf : ActionInvariantLinfty_5 →ₗ[ℝ] ActionInvariantLinfty_6 :=
  coordinateInvariantLinftyEquiv6.toLinearMap.comp
    ((Einfₗ concreteFace5QuasiMeasurePreserving).comp
      coordinateInvariantLinftyEquiv5.symm.toLinearMap)

@[simp]
theorem actionDinf_coordinate (f : Linfty U4 measureU4) :
    actionDinf (coordinateInvariantLinftyEquiv4 f) =
      coordinateInvariantLinftyEquiv5
        (Dinfₗ concreteFace4QuasiMeasurePreserving f) := by
  simp [actionDinf]

@[simp]
theorem actionEinf_coordinate (f : Linfty U5 measureU5) :
    actionEinf (coordinateInvariantLinftyEquiv5 f) =
      coordinateInvariantLinftyEquiv6
        (Einfₗ concreteFace5QuasiMeasurePreserving f) := by
  simp [actionEinf]

/-- The bounded transported operators form a complex. -/
theorem actionEinf_actionDinf (F : ActionInvariantLinfty_4) :
    actionEinf (actionDinf F) = 0 := by
  let f := coordinateInvariantLinftyEquiv4.symm F
  have hF : F = coordinateInvariantLinftyEquiv4 f := by
    simpa [f]
  rw [hF, actionDinf_coordinate, actionEinf_coordinate]
  have hzero :
      Einfₗ concreteFace5QuasiMeasurePreserving
          (Dinfₗ concreteFace4QuasiMeasurePreserving f) = 0 := by
    exact Einf_Dinf concreteFace4QuasiMeasurePreserving
      concreteFace5QuasiMeasurePreserving f
  rw [hzero]
  exact LinearEquiv.map_zero coordinateInvariantLinftyEquiv6

/-! ## Cohomology of the actual action complex -/

/-- Degree-four measurable cocycles in the actual invariant action complex. -/
def ActionMeasurableCocycles : Submodule ℝ ActionInvariantL0_5 :=
  LinearMap.ker actionE0

/- The canonical `Submodule` subtype exposes both a direct additive-monoid
instance and the one inherited from its additive-group instance.  Fix the
latter locally so that a second submodule quotient has definitionally coherent
algebraic instances. -/
local instance actionMeasurableCocyclesAddCommMonoid :
    AddCommMonoid ActionMeasurableCocycles :=
  (inferInstance : AddCommGroup ActionMeasurableCocycles).toAddCommMonoid

local instance actionMeasurableCocyclesModule :
    Module ℝ ActionMeasurableCocycles :=
  SubmoduleClass.module ActionMeasurableCocycles

/-- Degree-four measurable action coboundaries. -/
def ActionMeasurableBoundaries : Submodule ℝ ActionMeasurableCocycles :=
  (LinearMap.range actionD0).comap ActionMeasurableCocycles.subtype

/-- Degree-four measurable cohomology of the generic projective action. -/
abbrev ActionMeasurableH4 : Type :=
  (ActionMeasurableCocycles : Type) ⧸ ActionMeasurableBoundaries

/-- Degree-four bounded cocycles in the actual invariant action complex. -/
def ActionBoundedCocycles : Submodule ℝ ActionInvariantLinfty_5 :=
  LinearMap.ker actionEinf

local instance actionBoundedCocyclesAddCommMonoid :
    AddCommMonoid ActionBoundedCocycles :=
  (inferInstance : AddCommGroup ActionBoundedCocycles).toAddCommMonoid

local instance actionBoundedCocyclesModule :
    Module ℝ ActionBoundedCocycles :=
  SubmoduleClass.module ActionBoundedCocycles

/-- Degree-four bounded action coboundaries. -/
def ActionBoundedBoundaries : Submodule ℝ ActionBoundedCocycles :=
  (LinearMap.range actionDinf).comap ActionBoundedCocycles.subtype

/-- Degree-four bounded cohomology of the generic projective action. -/
abbrev ActionBoundedH4 : Type :=
  (ActionBoundedCocycles : Type) ⧸ ActionBoundedBoundaries

/-- Pfaffian coordinates identify measurable cocycles with actual action cocycles. -/
def measurableCocyclesEquiv :
    Pfaffian.MeasurableCocycles ≃ₗ[ℝ] ActionMeasurableCocycles where
  toFun F := ⟨coordinateInvariantL0Equiv5 F.1, by
    change actionE0 (coordinateInvariantL0Equiv5 F.1) = 0
    rw [actionE0_coordinate, F.2]
    exact LinearEquiv.map_zero coordinateInvariantL0Equiv6⟩
  invFun F := ⟨coordinateInvariantL0Equiv5.symm F.1, by
    change E0 concreteFace5QuasiMeasurePreserving
      (coordinateInvariantL0Equiv5.symm F.1) = 0
    apply coordinateInvariantL0Equiv6.injective
    calc
      coordinateInvariantL0Equiv6
          (E0 concreteFace5QuasiMeasurePreserving
            (coordinateInvariantL0Equiv5.symm F.1)) =
          actionE0 (coordinateInvariantL0Equiv5
            (coordinateInvariantL0Equiv5.symm F.1)) :=
        (actionE0_coordinate _).symm
      _ = actionE0 F.1 := congrArg actionE0
        (coordinateInvariantL0Equiv5.apply_symm_apply F.1)
      _ = 0 := F.2
      _ = coordinateInvariantL0Equiv6 0 :=
        (LinearEquiv.map_zero coordinateInvariantL0Equiv6).symm⟩
  left_inv F := by
    apply Subtype.ext
    exact coordinateInvariantL0Equiv5.symm_apply_apply F.1
  right_inv F := by
    apply Subtype.ext
    exact coordinateInvariantL0Equiv5.apply_symm_apply F.1
  map_add' F H := by
    apply Subtype.ext
    exact map_add coordinateInvariantL0Equiv5 F.1 H.1
  map_smul' c F := by
    apply Subtype.ext
    exact map_smul coordinateInvariantL0Equiv5 c F.1

/-- Pfaffian coordinates identify bounded cocycles with actual action cocycles. -/
def boundedCocyclesEquiv :
    Pfaffian.BoundedCocycles ≃ₗ[ℝ] ActionBoundedCocycles where
  toFun F := ⟨coordinateInvariantLinftyEquiv5 F.1, by
    change actionEinf (coordinateInvariantLinftyEquiv5 F.1) = 0
    rw [actionEinf_coordinate, F.2]
    exact LinearEquiv.map_zero coordinateInvariantLinftyEquiv6⟩
  invFun F := ⟨coordinateInvariantLinftyEquiv5.symm F.1, by
    change Einfₗ concreteFace5QuasiMeasurePreserving
      (coordinateInvariantLinftyEquiv5.symm F.1) = 0
    apply coordinateInvariantLinftyEquiv6.injective
    calc
      coordinateInvariantLinftyEquiv6
          (Einfₗ concreteFace5QuasiMeasurePreserving
            (coordinateInvariantLinftyEquiv5.symm F.1)) =
          actionEinf (coordinateInvariantLinftyEquiv5
            (coordinateInvariantLinftyEquiv5.symm F.1)) :=
        (actionEinf_coordinate _).symm
      _ = actionEinf F.1 := congrArg actionEinf
        (coordinateInvariantLinftyEquiv5.apply_symm_apply F.1)
      _ = 0 := F.2
      _ = coordinateInvariantLinftyEquiv6 0 :=
        (LinearEquiv.map_zero coordinateInvariantLinftyEquiv6).symm⟩
  left_inv F := by
    apply Subtype.ext
    exact coordinateInvariantLinftyEquiv5.symm_apply_apply F.1
  right_inv F := by
    apply Subtype.ext
    exact coordinateInvariantLinftyEquiv5.apply_symm_apply F.1
  map_add' F H := by
    apply Subtype.ext
    exact map_add coordinateInvariantLinftyEquiv5 F.1 H.1
  map_smul' c F := by
    apply Subtype.ext
    exact map_smul coordinateInvariantLinftyEquiv5 c F.1

theorem measurableCocyclesEquiv_mem_boundaries
    (F : Pfaffian.MeasurableCocycles) :
    F ∈ Pfaffian.MeasurableBoundaries ↔
      measurableCocyclesEquiv F ∈ ActionMeasurableBoundaries := by
  change F.1 ∈ LinearMap.range
      (D0 concreteFace4QuasiMeasurePreserving) ↔
    coordinateInvariantL0Equiv5 F.1 ∈ LinearMap.range actionD0
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨coordinateInvariantL0Equiv4 f, ?_⟩
    rw [actionD0_coordinate, hf]
  · rintro ⟨A, hA⟩
    let f := coordinateInvariantL0Equiv4.symm A
    refine ⟨f, ?_⟩
    apply coordinateInvariantL0Equiv5.injective
    calc
      coordinateInvariantL0Equiv5
          (D0 concreteFace4QuasiMeasurePreserving f) =
        actionD0 (coordinateInvariantL0Equiv4 f) :=
          (actionD0_coordinate f).symm
      _ = actionD0 A := congrArg actionD0
        (coordinateInvariantL0Equiv4.apply_symm_apply A)
      _ = coordinateInvariantL0Equiv5 F.1 := hA

theorem boundedCocyclesEquiv_mem_boundaries
    (F : Pfaffian.BoundedCocycles) :
    F ∈ Pfaffian.BoundedBoundaries ↔
      boundedCocyclesEquiv F ∈ ActionBoundedBoundaries := by
  change F.1 ∈ LinearMap.range
      (Dinfₗ concreteFace4QuasiMeasurePreserving) ↔
    coordinateInvariantLinftyEquiv5 F.1 ∈ LinearMap.range actionDinf
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨coordinateInvariantLinftyEquiv4 f, ?_⟩
    rw [actionDinf_coordinate, hf]
  · rintro ⟨A, hA⟩
    let f := coordinateInvariantLinftyEquiv4.symm A
    refine ⟨f, ?_⟩
    apply coordinateInvariantLinftyEquiv5.injective
    calc
      coordinateInvariantLinftyEquiv5
          (Dinfₗ concreteFace4QuasiMeasurePreserving f) =
        actionDinf (coordinateInvariantLinftyEquiv4 f) :=
          (actionDinf_coordinate f).symm
      _ = actionDinf A := congrArg actionDinf
        (coordinateInvariantLinftyEquiv4.apply_symm_apply A)
      _ = coordinateInvariantLinftyEquiv5 F.1 := hA

theorem measurableCocyclesEquiv_map_boundaries :
    Pfaffian.MeasurableBoundaries.map
        measurableCocyclesEquiv.toLinearMap =
      ActionMeasurableBoundaries := by
  apply le_antisymm
  · rintro A ⟨F, hF, rfl⟩
    exact (measurableCocyclesEquiv_mem_boundaries F).1 hF
  · intro A hA
    let F := measurableCocyclesEquiv.symm A
    have hF : F ∈ Pfaffian.MeasurableBoundaries := by
      apply (measurableCocyclesEquiv_mem_boundaries F).2
      simpa [F] using hA
    exact ⟨F, hF, measurableCocyclesEquiv.apply_symm_apply A⟩

theorem boundedCocyclesEquiv_map_boundaries :
    Pfaffian.BoundedBoundaries.map boundedCocyclesEquiv.toLinearMap =
      ActionBoundedBoundaries := by
  apply le_antisymm
  · rintro A ⟨F, hF, rfl⟩
    exact (boundedCocyclesEquiv_mem_boundaries F).1 hF
  · intro A hA
    let F := boundedCocyclesEquiv.symm A
    have hF : F ∈ Pfaffian.BoundedBoundaries := by
      apply (boundedCocyclesEquiv_mem_boundaries F).2
      simpa [F] using hA
    exact ⟨F, hF, boundedCocyclesEquiv.apply_symm_apply A⟩

/-- The measurable Pfaffian quotient is the actual measurable action
cohomology, by a cochain-level equivalence commuting with both differentials. -/
def measurableH4Equiv :
    Pfaffian.MeasurableH4 ≃ₗ[ℝ] ActionMeasurableH4 :=
  Submodule.Quotient.equiv Pfaffian.MeasurableBoundaries
    ActionMeasurableBoundaries measurableCocyclesEquiv
    measurableCocyclesEquiv_map_boundaries

/-- The bounded Pfaffian quotient is the actual bounded action cohomology. -/
def boundedH4Equiv :
    Pfaffian.BoundedH4 ≃ₗ[ℝ] ActionBoundedH4 :=
  Submodule.Quotient.equiv Pfaffian.BoundedBoundaries
    ActionBoundedBoundaries boundedCocyclesEquiv
    boundedCocyclesEquiv_map_boundaries

/-! ## Homogeneous face formulas -/

theorem D_orbitCoord5_eq_face_sum (f : U4 → ℝ) (x : GenericConfig 5) :
    D f (orbitCoord5 x) =
      ∑ i : Fin 5, faceSign i * f (orbitCoord4 (face i x)) := by
  rw [D_eq_face_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [orbitCoord4_face]

theorem E_orbitCoord6_eq_face_sum (f : U5 → ℝ) (x : GenericConfig 6) :
    E f (orbitCoord6 x) =
      ∑ i : Fin 6, faceSign i * f (orbitCoord5 (face i x)) := by
  rw [E_eq_face_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [orbitCoord5_face]

/-- On a coordinate representative, `actionD0` is almost everywhere the
homogeneous five-face coboundary. -/
theorem coe_actionD0_coordinate (f : L0 U4 measureU4) :
    ((actionD0 (coordinateInvariantL0Equiv4 f)).1 : GenericConfig 5 → ℝ)
      =ᵐ[measureGeneric5]
        fun x => ∑ i : Fin 5, faceSign i * f (orbitCoord4 (face i x)) := by
  rw [actionD0_coordinate]
  refine (coe_coordinateInvariantL0Equiv5
    (D0 concreteFace4QuasiMeasurePreserving f)).trans ?_
  have hD := (coeFn_D0 concreteFace4QuasiMeasurePreserving f).comp_tendsto
    orbitCoord5_quasiMeasurePreserving.tendsto_ae
  filter_upwards [hD] with x hx
  change (D0 concreteFace4QuasiMeasurePreserving f) (orbitCoord5 x) =
    ∑ i : Fin 5, faceSign i * f (orbitCoord4 (face i x))
  exact hx.trans (D_orbitCoord5_eq_face_sum f x)

/-- On a coordinate representative, `actionE0` is almost everywhere the
homogeneous six-face coboundary. -/
theorem coe_actionE0_coordinate (f : L0 U5 measureU5) :
    ((actionE0 (coordinateInvariantL0Equiv5 f)).1 : GenericConfig 6 → ℝ)
      =ᵐ[measureGeneric6]
        fun x => ∑ i : Fin 6, faceSign i * f (orbitCoord5 (face i x)) := by
  rw [actionE0_coordinate]
  refine (coe_coordinateInvariantL0Equiv6
    (E0 concreteFace5QuasiMeasurePreserving f)).trans ?_
  have hE := (coeFn_E0 concreteFace5QuasiMeasurePreserving f).comp_tendsto
    orbitCoord6_quasiMeasurePreserving.tendsto_ae
  filter_upwards [hE] with x hx
  change (E0 concreteFace5QuasiMeasurePreserving f) (orbitCoord6 x) =
    ∑ i : Fin 6, faceSign i * f (orbitCoord5 (face i x))
  exact hx.trans (E_orbitCoord6_eq_face_sum f x)

end
end ProjectiveAction
end Sp4
