import Sp4.Measure.ProjectiveMeasureClass
import Sp4.Cohomology.MeasurableProjectiveComplex

/-!
# Pfaffian coordinates for the natural projective measure class

`MeasurableProjectiveCoordinates` proves translation-factor descent for the
concrete Haar-product representatives.  `ProjectiveMeasureClass` proves that
those representatives have exactly the null sets of the natural product
projective measure on the generic strata.  This file joins the two results:
it transports invariant `L⁰` and `L∞` spaces across equivalent measures and
thereby states the Lebesgue-coordinate theorem for the natural projective
measure itself.
-/

namespace Sp4

open MeasureTheory

noncomputable section

universe uG uX

namespace MeasureClassInvariant

variable {G : Type uG} {X : Type uX}
  [Group G] [MeasurableSpace X] [MulAction G X]

/-- Invariant `L⁰` classes for a nonsingular action. -/
def InvariantL0 (mu : Measure X)
    (hact : ∀ a : G, Measure.QuasiMeasurePreserving
      (fun x : X => a • x) mu mu) : Submodule ℝ (L0 X mu) where
  carrier F := ∀ a : G, L0.pullbackₗ (fun x : X => a • x) (hact a) F = F
  zero_mem' := fun a => LinearMap.map_zero _
  add_mem' := by
    intro F H hF hH a
    rw [LinearMap.map_add, hF a, hH a]
  smul_mem' := by
    intro c F hF a
    rw [LinearMap.map_smul, hF a]

/-- Invariant `L∞` classes for a nonsingular action. -/
def InvariantLinfty (mu : Measure X)
    (hact : ∀ a : G, Measure.QuasiMeasurePreserving
      (fun x : X => a • x) mu mu) : Submodule ℝ (Linfty X mu) where
  carrier F := ∀ a : G,
    Linfty.pullbackₗ (fun x : X => a • x) (hact a) F = F
  zero_mem' := fun a => LinearMap.map_zero _
  add_mem' := by
    intro F H hF hH a
    rw [LinearMap.map_add, hF a, hH a]
  smul_mem' := by
    intro c F hF a
    rw [LinearMap.map_smul, hF a]

variable {mu nu : Measure X}
  (hmunu : mu ≪ nu) (hnumu : nu ≪ mu)
  (hmu : ∀ a : G, Measure.QuasiMeasurePreserving
    (fun x : X => a • x) mu mu)
  (hnu : ∀ a : G, Measure.QuasiMeasurePreserving
    (fun x : X => a • x) nu nu)

theorem rebaseL0_commutes (a : G) (F : L0 X mu) :
    L0.measureClassEquiv hmunu hnumu
        (L0.pullbackₗ (fun x : X => a • x) (hmu a) F) =
      L0.pullbackₗ (fun x : X => a • x) (hnu a)
        (L0.measureClassEquiv hmunu hnumu F) := by
  let T := fun x : X => a • x
  let qmn : Measure.QuasiMeasurePreserving id nu mu :=
    ⟨measurable_id, by simpa using hnumu⟩
  change L0.pullbackₗ id qmn (L0.pullbackₗ T (hmu a) F) =
    L0.pullbackₗ T (hnu a) (L0.pullbackₗ id qmn F)
  calc
    _ = L0.pullbackₗ (T ∘ id) ((hmu a).comp qmn) F :=
      (L0.pullbackₗ_comp T (hmu a) id qmn F).symm
    _ = L0.pullbackₗ (id ∘ T) (qmn.comp (hnu a)) F := by
      congr 1
    _ = _ := L0.pullbackₗ_comp id qmn T (hnu a) F

theorem rebaseLinfty_commutes (a : G) (F : Linfty X mu) :
    Linfty.measureClassEquiv hmunu hnumu
        (Linfty.pullbackₗ (fun x : X => a • x) (hmu a) F) =
      Linfty.pullbackₗ (fun x : X => a • x) (hnu a)
        (Linfty.measureClassEquiv hmunu hnumu F) := by
  let T := fun x : X => a • x
  let qmn : Measure.QuasiMeasurePreserving id nu mu :=
    ⟨measurable_id, by simpa using hnumu⟩
  change Linfty.pullbackₗ id qmn (Linfty.pullbackₗ T (hmu a) F) =
    Linfty.pullbackₗ T (hnu a) (Linfty.pullbackₗ id qmn F)
  calc
    _ = Linfty.pullbackₗ (T ∘ id) ((hmu a).comp qmn) F :=
      (Linfty.pullbackₗ_comp T (hmu a) id qmn F).symm
    _ = Linfty.pullbackₗ (id ∘ T) (qmn.comp (hnu a)) F := by
      congr 1
    _ = _ := Linfty.pullbackₗ_comp id qmn T (hnu a) F

def invariantL0Map :
    InvariantL0 mu hmu →ₗ[ℝ] InvariantL0 nu hnu where
  toFun F := ⟨L0.measureClassEquiv hmunu hnumu F.1, by
    intro a
    rw [← rebaseL0_commutes hmunu hnumu hmu hnu, F.2 a]⟩
  map_add' F H := by
    apply Subtype.ext
    exact LinearEquiv.map_add _ F.1 H.1
  map_smul' c F := by
    apply Subtype.ext
    exact LinearEquiv.map_smul _ c F.1

theorem invariantL0Map_bijective :
    Function.Bijective (invariantL0Map hmunu hnumu hmu hnu) := by
  constructor
  · intro F H hFH
    apply Subtype.ext
    apply (L0.measureClassEquiv hmunu hnumu).injective
    exact congrArg Subtype.val hFH
  · intro F
    let f : L0 X mu := (L0.measureClassEquiv hmunu hnumu).symm F.1
    have hf : f ∈ InvariantL0 mu hmu := by
      intro a
      apply (L0.measureClassEquiv hmunu hnumu).injective
      rw [rebaseL0_commutes hmunu hnumu hmu hnu,
        LinearEquiv.apply_symm_apply]
      exact F.2 a
    refine ⟨⟨f, hf⟩, ?_⟩
    apply Subtype.ext
    exact (L0.measureClassEquiv hmunu hnumu).apply_symm_apply F.1

/-- Invariant `L⁰` spaces are unchanged by replacing a measure by an
equivalent representative. -/
noncomputable def invariantL0Equiv :
    InvariantL0 mu hmu ≃ₗ[ℝ] InvariantL0 nu hnu :=
  LinearEquiv.ofBijective (invariantL0Map hmunu hnumu hmu hnu)
    (invariantL0Map_bijective hmunu hnumu hmu hnu)

def invariantLinftyMap :
    InvariantLinfty mu hmu →ₗ[ℝ] InvariantLinfty nu hnu where
  toFun F := ⟨Linfty.measureClassEquiv hmunu hnumu F.1, by
    intro a
    rw [← rebaseLinfty_commutes hmunu hnumu hmu hnu, F.2 a]⟩
  map_add' F H := by
    apply Subtype.ext
    exact LinearEquiv.map_add _ F.1 H.1
  map_smul' c F := by
    apply Subtype.ext
    exact LinearEquiv.map_smul _ c F.1

theorem invariantLinftyMap_bijective :
    Function.Bijective (invariantLinftyMap hmunu hnumu hmu hnu) := by
  constructor
  · intro F H hFH
    apply Subtype.ext
    apply (Linfty.measureClassEquiv hmunu hnumu).injective
    exact congrArg Subtype.val hFH
  · intro F
    let f : Linfty X mu := (Linfty.measureClassEquiv hmunu hnumu).symm F.1
    have hf : f ∈ InvariantLinfty mu hmu := by
      intro a
      apply (Linfty.measureClassEquiv hmunu hnumu).injective
      rw [rebaseLinfty_commutes hmunu hnumu hmu hnu,
        LinearEquiv.apply_symm_apply]
      exact F.2 a
    refine ⟨⟨f, hf⟩, ?_⟩
    apply Subtype.ext
    exact (Linfty.measureClassEquiv hmunu hnumu).apply_symm_apply F.1

/-- Invariant `L∞` spaces are unchanged by replacing a measure by an
equivalent representative. -/
noncomputable def invariantLinftyEquiv :
    InvariantLinfty mu hmu ≃ₗ[ℝ] InvariantLinfty nu hnu :=
  LinearEquiv.ofBijective (invariantLinftyMap hmunu hnumu hmu hnu)
    (invariantLinftyMap_bijective hmunu hnumu hmu hnu)

/-- Measure-class rebasing preserves the inherited essential-supremum norm
on invariant subspaces. -/
@[simp]
theorem norm_invariantLinftyEquiv_apply
    (F : InvariantLinfty mu hmu) :
    ‖invariantLinftyEquiv hmunu hnumu hmu hnu F‖ = ‖F‖ := by
  change ‖Linfty.measureClassEquiv hmunu hnumu F.1‖ = ‖F.1‖
  exact Linfty.norm_measureClassEquiv_apply hmunu hnumu F.1

/-- Isometric form of invariant `L∞` measure-class rebasing. -/
noncomputable def invariantLinftyIsometryEquiv :
    InvariantLinfty mu hmu ≃ₗᵢ[ℝ] InvariantLinfty nu hnu where
  toLinearEquiv := invariantLinftyEquiv hmunu hnumu hmu hnu
  norm_map' := norm_invariantLinftyEquiv_apply hmunu hnumu hmu hnu

end MeasureClassInvariant

namespace ProjectiveAction

open OrbitChain Pfaffian ProjectiveMeasureClass

abbrev NaturalActionInvariantL0_4 :=
  MeasureClassInvariant.InvariantL0
    (naturalGenericMeasure 4 (by norm_num))
    effective_smul_naturalGenericMeasure4_quasiMeasurePreserving

abbrev NaturalActionInvariantL0_5 :=
  MeasureClassInvariant.InvariantL0
    (naturalGenericMeasure 5 (by norm_num))
    effective_smul_naturalGenericMeasure5_quasiMeasurePreserving

abbrev NaturalActionInvariantL0_6 :=
  MeasureClassInvariant.InvariantL0
    (naturalGenericMeasure 6 (by norm_num))
    effective_smul_naturalGenericMeasure6_quasiMeasurePreserving

abbrev NaturalActionInvariantLinfty_4 :=
  MeasureClassInvariant.InvariantLinfty
    (naturalGenericMeasure 4 (by norm_num))
    effective_smul_naturalGenericMeasure4_quasiMeasurePreserving

abbrev NaturalActionInvariantLinfty_5 :=
  MeasureClassInvariant.InvariantLinfty
    (naturalGenericMeasure 5 (by norm_num))
    effective_smul_naturalGenericMeasure5_quasiMeasurePreserving

abbrev NaturalActionInvariantLinfty_6 :=
  MeasureClassInvariant.InvariantLinfty
    (naturalGenericMeasure 6 (by norm_num))
    effective_smul_naturalGenericMeasure6_quasiMeasurePreserving

noncomputable def naturalInvariantL0Equiv4 :
    NaturalActionInvariantL0_4 ≃ₗ[ℝ] ActionInvariantL0_4 :=
  MeasureClassInvariant.invariantL0Equiv
    naturalGenericMeasure4_absolutelyContinuous_measureGeneric4
    measureGeneric4_absolutelyContinuous_naturalGenericMeasure4
    effective_smul_naturalGenericMeasure4_quasiMeasurePreserving
    (fun a => (measurePreserving_effective_smul4 a).quasiMeasurePreserving)

noncomputable def naturalInvariantL0Equiv5 :
    NaturalActionInvariantL0_5 ≃ₗ[ℝ] ActionInvariantL0_5 :=
  MeasureClassInvariant.invariantL0Equiv
    naturalGenericMeasure5_absolutelyContinuous_measureGeneric5
    measureGeneric5_absolutelyContinuous_naturalGenericMeasure5
    effective_smul_naturalGenericMeasure5_quasiMeasurePreserving
    (fun a => (measurePreserving_effective_smul5 a).quasiMeasurePreserving)

noncomputable def naturalInvariantL0Equiv6 :
    NaturalActionInvariantL0_6 ≃ₗ[ℝ] ActionInvariantL0_6 :=
  MeasureClassInvariant.invariantL0Equiv
    naturalGenericMeasure6_absolutelyContinuous_measureGeneric6
    measureGeneric6_absolutelyContinuous_naturalGenericMeasure6
    effective_smul_naturalGenericMeasure6_quasiMeasurePreserving
    (fun a => (measurePreserving_effective_smul6 a).quasiMeasurePreserving)

noncomputable def naturalInvariantLinftyEquiv4 :
    NaturalActionInvariantLinfty_4 ≃ₗ[ℝ] ActionInvariantLinfty_4 :=
  MeasureClassInvariant.invariantLinftyEquiv
    naturalGenericMeasure4_absolutelyContinuous_measureGeneric4
    measureGeneric4_absolutelyContinuous_naturalGenericMeasure4
    effective_smul_naturalGenericMeasure4_quasiMeasurePreserving
    (fun a => (measurePreserving_effective_smul4 a).quasiMeasurePreserving)

noncomputable def naturalInvariantLinftyEquiv5 :
    NaturalActionInvariantLinfty_5 ≃ₗ[ℝ] ActionInvariantLinfty_5 :=
  MeasureClassInvariant.invariantLinftyEquiv
    naturalGenericMeasure5_absolutelyContinuous_measureGeneric5
    measureGeneric5_absolutelyContinuous_naturalGenericMeasure5
    effective_smul_naturalGenericMeasure5_quasiMeasurePreserving
    (fun a => (measurePreserving_effective_smul5 a).quasiMeasurePreserving)

noncomputable def naturalInvariantLinftyEquiv6 :
    NaturalActionInvariantLinfty_6 ≃ₗ[ℝ] ActionInvariantLinfty_6 :=
  MeasureClassInvariant.invariantLinftyEquiv
    naturalGenericMeasure6_absolutelyContinuous_measureGeneric6
    measureGeneric6_absolutelyContinuous_naturalGenericMeasure6
    effective_smul_naturalGenericMeasure6_quasiMeasurePreserving
    (fun a => (measurePreserving_effective_smul6 a).quasiMeasurePreserving)

/-- Isometric rebasing from the natural four-point projective measure to the
Haar–Pfaffian representative. -/
noncomputable def naturalInvariantLinftyIsometryEquiv4 :
    NaturalActionInvariantLinfty_4 ≃ₗᵢ[ℝ] ActionInvariantLinfty_4 :=
  MeasureClassInvariant.invariantLinftyIsometryEquiv
    naturalGenericMeasure4_absolutelyContinuous_measureGeneric4
    measureGeneric4_absolutelyContinuous_naturalGenericMeasure4
    effective_smul_naturalGenericMeasure4_quasiMeasurePreserving
    (fun a => (measurePreserving_effective_smul4 a).quasiMeasurePreserving)

/-- Isometric rebasing from the natural five-point projective measure to the
Haar–Pfaffian representative. -/
noncomputable def naturalInvariantLinftyIsometryEquiv5 :
    NaturalActionInvariantLinfty_5 ≃ₗᵢ[ℝ] ActionInvariantLinfty_5 :=
  MeasureClassInvariant.invariantLinftyIsometryEquiv
    naturalGenericMeasure5_absolutelyContinuous_measureGeneric5
    measureGeneric5_absolutelyContinuous_naturalGenericMeasure5
    effective_smul_naturalGenericMeasure5_quasiMeasurePreserving
    (fun a => (measurePreserving_effective_smul5 a).quasiMeasurePreserving)

/-- Isometric rebasing from the natural six-point projective measure to the
Haar–Pfaffian representative. -/
noncomputable def naturalInvariantLinftyIsometryEquiv6 :
    NaturalActionInvariantLinfty_6 ≃ₗᵢ[ℝ] ActionInvariantLinfty_6 :=
  MeasureClassInvariant.invariantLinftyIsometryEquiv
    naturalGenericMeasure6_absolutelyContinuous_measureGeneric6
    measureGeneric6_absolutelyContinuous_naturalGenericMeasure6
    effective_smul_naturalGenericMeasure6_quasiMeasurePreserving
    (fun a => (measurePreserving_effective_smul6 a).quasiMeasurePreserving)

/-- Natural-projective four-point invariant `L⁰` classes are precisely
measurable functions on `U₄`. -/
noncomputable def naturalCoordinateInvariantL0Equiv4 :
    L0 U4 measureU4 ≃ₗ[ℝ] NaturalActionInvariantL0_4 :=
  coordinateInvariantL0Equiv4.trans naturalInvariantL0Equiv4.symm

/-- Natural-projective five-point invariant `L⁰` classes are precisely
measurable functions on `U₅`. -/
noncomputable def naturalCoordinateInvariantL0Equiv5 :
    L0 U5 measureU5 ≃ₗ[ℝ] NaturalActionInvariantL0_5 :=
  coordinateInvariantL0Equiv5.trans naturalInvariantL0Equiv5.symm

/-- Natural-projective six-point invariant `L⁰` classes are precisely
measurable functions on `U₆`. -/
noncomputable def naturalCoordinateInvariantL0Equiv6 :
    L0 U6 measureU6 ≃ₗ[ℝ] NaturalActionInvariantL0_6 :=
  coordinateInvariantL0Equiv6.trans naturalInvariantL0Equiv6.symm

/-- The natural-projective `L∞` quotient in degree three. -/
noncomputable def naturalCoordinateInvariantLinftyEquiv4 :
    Linfty U4 measureU4 ≃ₗ[ℝ] NaturalActionInvariantLinfty_4 :=
  coordinateInvariantLinftyEquiv4.trans naturalInvariantLinftyEquiv4.symm

/-- The natural-projective `L∞` quotient in degree four. -/
noncomputable def naturalCoordinateInvariantLinftyEquiv5 :
    Linfty U5 measureU5 ≃ₗ[ℝ] NaturalActionInvariantLinfty_5 :=
  coordinateInvariantLinftyEquiv5.trans naturalInvariantLinftyEquiv5.symm

/-- The natural-projective `L∞` quotient in degree five. -/
noncomputable def naturalCoordinateInvariantLinftyEquiv6 :
    Linfty U6 measureU6 ≃ₗ[ℝ] NaturalActionInvariantLinfty_6 :=
  coordinateInvariantLinftyEquiv6.trans naturalInvariantLinftyEquiv6.symm

/-- Isometric natural-projective coordinate theorem in degree three. -/
noncomputable def naturalCoordinateInvariantLinftyIsometryEquiv4 :
    Linfty U4 measureU4 ≃ₗᵢ[ℝ] NaturalActionInvariantLinfty_4 :=
  coordinateInvariantLinftyIsometryEquiv4.trans
    naturalInvariantLinftyIsometryEquiv4.symm

/-- Isometric natural-projective coordinate theorem in degree four. -/
noncomputable def naturalCoordinateInvariantLinftyIsometryEquiv5 :
    Linfty U5 measureU5 ≃ₗᵢ[ℝ] NaturalActionInvariantLinfty_5 :=
  coordinateInvariantLinftyIsometryEquiv5.trans
    naturalInvariantLinftyIsometryEquiv5.symm

/-- Isometric natural-projective coordinate theorem in degree five. -/
noncomputable def naturalCoordinateInvariantLinftyIsometryEquiv6 :
    Linfty U6 measureU6 ≃ₗᵢ[ℝ] NaturalActionInvariantLinfty_6 :=
  coordinateInvariantLinftyIsometryEquiv6.trans
    naturalInvariantLinftyIsometryEquiv6.symm

/-! ## The natural-measure projective action complex

The following complex is defined on the restriction of the actual product
projective measure, rather than on the convenient Haar-product representative.
Its differentials are transported through the coordinate maps just proved;
the coordinate formulas below make the transport explicit.
-/

/-- Four-to-five differential on invariant `L⁰` classes for the natural
projective measure. -/
def naturalActionD0 :
    NaturalActionInvariantL0_4 →ₗ[ℝ] NaturalActionInvariantL0_5 :=
  naturalCoordinateInvariantL0Equiv5.toLinearMap.comp
    ((D0 concreteFace4QuasiMeasurePreserving).comp
      naturalCoordinateInvariantL0Equiv4.symm.toLinearMap)

/-- Five-to-six differential on invariant `L⁰` classes for the natural
projective measure. -/
def naturalActionE0 :
    NaturalActionInvariantL0_5 →ₗ[ℝ] NaturalActionInvariantL0_6 :=
  naturalCoordinateInvariantL0Equiv6.toLinearMap.comp
    ((E0 concreteFace5QuasiMeasurePreserving).comp
      naturalCoordinateInvariantL0Equiv5.symm.toLinearMap)

@[simp]
theorem naturalActionD0_coordinate (f : L0 U4 measureU4) :
    naturalActionD0 (naturalCoordinateInvariantL0Equiv4 f) =
      naturalCoordinateInvariantL0Equiv5
        (D0 concreteFace4QuasiMeasurePreserving f) := by
  simp [naturalActionD0]

@[simp]
theorem naturalActionE0_coordinate (f : L0 U5 measureU5) :
    naturalActionE0 (naturalCoordinateInvariantL0Equiv5 f) =
      naturalCoordinateInvariantL0Equiv6
        (E0 concreteFace5QuasiMeasurePreserving f) := by
  simp [naturalActionE0]

/-- The natural-measure operators form a complex. -/
theorem naturalActionE0_naturalActionD0
    (F : NaturalActionInvariantL0_4) :
    naturalActionE0 (naturalActionD0 F) = 0 := by
  let f := naturalCoordinateInvariantL0Equiv4.symm F
  have hF : F = naturalCoordinateInvariantL0Equiv4 f := by
    simpa [f]
  rw [hF, naturalActionD0_coordinate, naturalActionE0_coordinate,
    E0_D0 concreteFace4QuasiMeasurePreserving
      concreteFace5QuasiMeasurePreserving]
  exact LinearEquiv.map_zero naturalCoordinateInvariantL0Equiv6

/-- Degree-four measurable cocycles for the natural projective measure. -/
def NaturalActionMeasurableCocycles :
    Submodule ℝ NaturalActionInvariantL0_5 :=
  LinearMap.ker naturalActionE0

local instance naturalActionMeasurableCocyclesAddCommMonoid :
    AddCommMonoid NaturalActionMeasurableCocycles :=
  (inferInstance : AddCommGroup NaturalActionMeasurableCocycles).toAddCommMonoid

local instance naturalActionMeasurableCocyclesModule :
    Module ℝ NaturalActionMeasurableCocycles :=
  SubmoduleClass.module NaturalActionMeasurableCocycles

/-- Degree-four measurable boundaries for the natural projective measure. -/
def NaturalActionMeasurableBoundaries :
    Submodule ℝ NaturalActionMeasurableCocycles :=
  (LinearMap.range naturalActionD0).comap
    NaturalActionMeasurableCocycles.subtype

/-- Degree-four measurable projective-action cohomology formed with the
natural projective measure class. -/
abbrev NaturalActionMeasurableH4 : Type :=
  (NaturalActionMeasurableCocycles : Type) ⧸
    NaturalActionMeasurableBoundaries

/-- Natural projective coordinates identify Pfaffian measurable cocycles with
the cocycles of the actual natural-measure action complex. -/
def naturalMeasurableCocyclesEquiv :
    Pfaffian.MeasurableCocycles ≃ₗ[ℝ] NaturalActionMeasurableCocycles where
  toFun F := ⟨naturalCoordinateInvariantL0Equiv5 F.1, by
    change naturalActionE0 (naturalCoordinateInvariantL0Equiv5 F.1) = 0
    rw [naturalActionE0_coordinate, F.2]
    exact LinearEquiv.map_zero naturalCoordinateInvariantL0Equiv6⟩
  invFun F := ⟨naturalCoordinateInvariantL0Equiv5.symm F.1, by
    change E0 concreteFace5QuasiMeasurePreserving
      (naturalCoordinateInvariantL0Equiv5.symm F.1) = 0
    apply naturalCoordinateInvariantL0Equiv6.injective
    calc
      naturalCoordinateInvariantL0Equiv6
          (E0 concreteFace5QuasiMeasurePreserving
            (naturalCoordinateInvariantL0Equiv5.symm F.1)) =
          naturalActionE0 (naturalCoordinateInvariantL0Equiv5
            (naturalCoordinateInvariantL0Equiv5.symm F.1)) :=
        (naturalActionE0_coordinate _).symm
      _ = naturalActionE0 F.1 := congrArg naturalActionE0
        (naturalCoordinateInvariantL0Equiv5.apply_symm_apply F.1)
      _ = 0 := F.2
      _ = naturalCoordinateInvariantL0Equiv6 0 :=
        (LinearEquiv.map_zero naturalCoordinateInvariantL0Equiv6).symm⟩
  left_inv F := by
    apply Subtype.ext
    exact naturalCoordinateInvariantL0Equiv5.symm_apply_apply F.1
  right_inv F := by
    apply Subtype.ext
    exact naturalCoordinateInvariantL0Equiv5.apply_symm_apply F.1
  map_add' F H := by
    apply Subtype.ext
    exact map_add naturalCoordinateInvariantL0Equiv5 F.1 H.1
  map_smul' c F := by
    apply Subtype.ext
    exact map_smul naturalCoordinateInvariantL0Equiv5 c F.1

theorem naturalMeasurableCocyclesEquiv_mem_boundaries
    (F : Pfaffian.MeasurableCocycles) :
    F ∈ Pfaffian.MeasurableBoundaries ↔
      naturalMeasurableCocyclesEquiv F ∈
        NaturalActionMeasurableBoundaries := by
  change F.1 ∈ LinearMap.range
      (D0 concreteFace4QuasiMeasurePreserving) ↔
    naturalCoordinateInvariantL0Equiv5 F.1 ∈
      LinearMap.range naturalActionD0
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨naturalCoordinateInvariantL0Equiv4 f, ?_⟩
    rw [naturalActionD0_coordinate, hf]
  · rintro ⟨A, hA⟩
    let f := naturalCoordinateInvariantL0Equiv4.symm A
    refine ⟨f, ?_⟩
    apply naturalCoordinateInvariantL0Equiv5.injective
    calc
      naturalCoordinateInvariantL0Equiv5
          (D0 concreteFace4QuasiMeasurePreserving f) =
        naturalActionD0 (naturalCoordinateInvariantL0Equiv4 f) :=
          (naturalActionD0_coordinate f).symm
      _ = naturalActionD0 A := congrArg naturalActionD0
        (naturalCoordinateInvariantL0Equiv4.apply_symm_apply A)
      _ = naturalCoordinateInvariantL0Equiv5 F.1 := hA

theorem naturalMeasurableCocyclesEquiv_map_boundaries :
    Pfaffian.MeasurableBoundaries.map
        naturalMeasurableCocyclesEquiv.toLinearMap =
      NaturalActionMeasurableBoundaries := by
  apply le_antisymm
  · rintro A ⟨F, hF, rfl⟩
    exact (naturalMeasurableCocyclesEquiv_mem_boundaries F).1 hF
  · intro A hA
    let F := naturalMeasurableCocyclesEquiv.symm A
    have hF : F ∈ Pfaffian.MeasurableBoundaries := by
      apply (naturalMeasurableCocyclesEquiv_mem_boundaries F).2
      simpa [F] using hA
    exact ⟨F, hF, naturalMeasurableCocyclesEquiv.apply_symm_apply A⟩

/-- The Pfaffian measurable quotient is the degree-four action cohomology for
the natural product projective measure. -/
def naturalMeasurableH4Equiv :
    Pfaffian.MeasurableH4 ≃ₗ[ℝ] NaturalActionMeasurableH4 :=
  Submodule.Quotient.equiv Pfaffian.MeasurableBoundaries
    NaturalActionMeasurableBoundaries naturalMeasurableCocyclesEquiv
    naturalMeasurableCocyclesEquiv_map_boundaries

/-! ### Bounded natural-measure complex -/

/-- Four-to-five differential on invariant `L∞` classes for the natural
projective measure. -/
def naturalActionDinf :
    NaturalActionInvariantLinfty_4 →ₗ[ℝ] NaturalActionInvariantLinfty_5 :=
  naturalCoordinateInvariantLinftyEquiv5.toLinearMap.comp
    ((Dinfₗ concreteFace4QuasiMeasurePreserving).comp
      naturalCoordinateInvariantLinftyEquiv4.symm.toLinearMap)

/-- Five-to-six differential on invariant `L∞` classes for the natural
projective measure. -/
def naturalActionEinf :
    NaturalActionInvariantLinfty_5 →ₗ[ℝ] NaturalActionInvariantLinfty_6 :=
  naturalCoordinateInvariantLinftyEquiv6.toLinearMap.comp
    ((Einfₗ concreteFace5QuasiMeasurePreserving).comp
      naturalCoordinateInvariantLinftyEquiv5.symm.toLinearMap)

@[simp]
theorem naturalActionDinf_coordinate (f : Linfty U4 measureU4) :
    naturalActionDinf (naturalCoordinateInvariantLinftyEquiv4 f) =
      naturalCoordinateInvariantLinftyEquiv5
        (Dinfₗ concreteFace4QuasiMeasurePreserving f) := by
  simp [naturalActionDinf]

@[simp]
theorem naturalActionEinf_coordinate (f : Linfty U5 measureU5) :
    naturalActionEinf (naturalCoordinateInvariantLinftyEquiv5 f) =
      naturalCoordinateInvariantLinftyEquiv6
        (Einfₗ concreteFace5QuasiMeasurePreserving f) := by
  simp [naturalActionEinf]

/-- The bounded natural-measure operators form a complex. -/
theorem naturalActionEinf_naturalActionDinf
    (F : NaturalActionInvariantLinfty_4) :
    naturalActionEinf (naturalActionDinf F) = 0 := by
  let f := naturalCoordinateInvariantLinftyEquiv4.symm F
  have hF : F = naturalCoordinateInvariantLinftyEquiv4 f := by
    simpa [f]
  rw [hF, naturalActionDinf_coordinate, naturalActionEinf_coordinate]
  have hzero :
      Einfₗ concreteFace5QuasiMeasurePreserving
          (Dinfₗ concreteFace4QuasiMeasurePreserving f) = 0 :=
    Einf_Dinf concreteFace4QuasiMeasurePreserving
      concreteFace5QuasiMeasurePreserving f
  rw [hzero]
  exact LinearEquiv.map_zero naturalCoordinateInvariantLinftyEquiv6

/-- Degree-four bounded cocycles for the natural projective measure. -/
def NaturalActionBoundedCocycles :
    Submodule ℝ NaturalActionInvariantLinfty_5 :=
  LinearMap.ker naturalActionEinf

local instance naturalActionBoundedCocyclesAddCommMonoid :
    AddCommMonoid NaturalActionBoundedCocycles :=
  (inferInstance : AddCommGroup NaturalActionBoundedCocycles).toAddCommMonoid

local instance naturalActionBoundedCocyclesModule :
    Module ℝ NaturalActionBoundedCocycles :=
  SubmoduleClass.module NaturalActionBoundedCocycles

/-- Degree-four bounded boundaries for the natural projective measure. -/
def NaturalActionBoundedBoundaries :
    Submodule ℝ NaturalActionBoundedCocycles :=
  (LinearMap.range naturalActionDinf).comap NaturalActionBoundedCocycles.subtype

/-- Degree-four bounded projective-action cohomology formed with the natural
projective measure class. -/
abbrev NaturalActionBoundedH4 : Type :=
  (NaturalActionBoundedCocycles : Type) ⧸ NaturalActionBoundedBoundaries

/-- Natural projective coordinates identify Pfaffian bounded cocycles with
bounded cocycles of the natural-measure action complex. -/
def naturalBoundedCocyclesEquiv :
    Pfaffian.BoundedCocycles ≃ₗ[ℝ] NaturalActionBoundedCocycles where
  toFun F := ⟨naturalCoordinateInvariantLinftyEquiv5 F.1, by
    change naturalActionEinf
      (naturalCoordinateInvariantLinftyEquiv5 F.1) = 0
    rw [naturalActionEinf_coordinate, F.2]
    exact LinearEquiv.map_zero naturalCoordinateInvariantLinftyEquiv6⟩
  invFun F := ⟨naturalCoordinateInvariantLinftyEquiv5.symm F.1, by
    change Einfₗ concreteFace5QuasiMeasurePreserving
      (naturalCoordinateInvariantLinftyEquiv5.symm F.1) = 0
    apply naturalCoordinateInvariantLinftyEquiv6.injective
    calc
      naturalCoordinateInvariantLinftyEquiv6
          (Einfₗ concreteFace5QuasiMeasurePreserving
            (naturalCoordinateInvariantLinftyEquiv5.symm F.1)) =
          naturalActionEinf (naturalCoordinateInvariantLinftyEquiv5
            (naturalCoordinateInvariantLinftyEquiv5.symm F.1)) :=
        (naturalActionEinf_coordinate _).symm
      _ = naturalActionEinf F.1 := congrArg naturalActionEinf
        (naturalCoordinateInvariantLinftyEquiv5.apply_symm_apply F.1)
      _ = 0 := F.2
      _ = naturalCoordinateInvariantLinftyEquiv6 0 :=
        (LinearEquiv.map_zero naturalCoordinateInvariantLinftyEquiv6).symm⟩
  left_inv F := by
    apply Subtype.ext
    exact naturalCoordinateInvariantLinftyEquiv5.symm_apply_apply F.1
  right_inv F := by
    apply Subtype.ext
    exact naturalCoordinateInvariantLinftyEquiv5.apply_symm_apply F.1
  map_add' F H := by
    apply Subtype.ext
    exact map_add naturalCoordinateInvariantLinftyEquiv5 F.1 H.1
  map_smul' c F := by
    apply Subtype.ext
    exact map_smul naturalCoordinateInvariantLinftyEquiv5 c F.1

theorem naturalBoundedCocyclesEquiv_mem_boundaries
    (F : Pfaffian.BoundedCocycles) :
    F ∈ Pfaffian.BoundedBoundaries ↔
      naturalBoundedCocyclesEquiv F ∈ NaturalActionBoundedBoundaries := by
  change F.1 ∈ LinearMap.range
      (Dinfₗ concreteFace4QuasiMeasurePreserving) ↔
    naturalCoordinateInvariantLinftyEquiv5 F.1 ∈
      LinearMap.range naturalActionDinf
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨naturalCoordinateInvariantLinftyEquiv4 f, ?_⟩
    rw [naturalActionDinf_coordinate, hf]
  · rintro ⟨A, hA⟩
    let f := naturalCoordinateInvariantLinftyEquiv4.symm A
    refine ⟨f, ?_⟩
    apply naturalCoordinateInvariantLinftyEquiv5.injective
    calc
      naturalCoordinateInvariantLinftyEquiv5
          (Dinfₗ concreteFace4QuasiMeasurePreserving f) =
        naturalActionDinf (naturalCoordinateInvariantLinftyEquiv4 f) :=
          (naturalActionDinf_coordinate f).symm
      _ = naturalActionDinf A := congrArg naturalActionDinf
        (naturalCoordinateInvariantLinftyEquiv4.apply_symm_apply A)
      _ = naturalCoordinateInvariantLinftyEquiv5 F.1 := hA

theorem naturalBoundedCocyclesEquiv_map_boundaries :
    Pfaffian.BoundedBoundaries.map naturalBoundedCocyclesEquiv.toLinearMap =
      NaturalActionBoundedBoundaries := by
  apply le_antisymm
  · rintro A ⟨F, hF, rfl⟩
    exact (naturalBoundedCocyclesEquiv_mem_boundaries F).1 hF
  · intro A hA
    let F := naturalBoundedCocyclesEquiv.symm A
    have hF : F ∈ Pfaffian.BoundedBoundaries := by
      apply (naturalBoundedCocyclesEquiv_mem_boundaries F).2
      simpa [F] using hA
    exact ⟨F, hF, naturalBoundedCocyclesEquiv.apply_symm_apply A⟩

/-- The Pfaffian bounded quotient is the degree-four action cohomology for the
natural product projective measure.  It is induced by the isometric cochain
coordinate maps above. -/
def naturalBoundedH4Equiv :
    Pfaffian.BoundedH4 ≃ₗ[ℝ] NaturalActionBoundedH4 :=
  Submodule.Quotient.equiv Pfaffian.BoundedBoundaries
    NaturalActionBoundedBoundaries naturalBoundedCocyclesEquiv
    naturalBoundedCocyclesEquiv_map_boundaries

end ProjectiveAction

end
end Sp4
