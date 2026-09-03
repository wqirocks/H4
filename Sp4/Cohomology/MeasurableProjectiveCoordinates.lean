import Sp4.Measure.TranslationInvariant

/-!
# Measurable projective-action invariants in Pfaffian coordinates

This file upgrades the pointwise orbit classification to genuine quotient
spaces of almost-everywhere functions.  A reusable product-chart theorem
shows that, for a free measurable action parametrized by `G × Y`, invariant
`L⁰` and invariant `L∞` classes are exactly the pullbacks of classes on
`Y`.  It is then instantiated for four, five, and six generic projective
points with `G = PSp(4,ℂ)` and `Y = U₄,U₅,U₆`.
-/

namespace Sp4

open MeasureTheory

noncomputable section

universe uG uX uY

namespace MeasurableOrbit

variable {G : Type uG} {X : Type uX} {Y : Type uY}
  [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [MeasurableSpace X] [MeasurableSpace Y] [MulAction G X]
  (muG : Measure G) (muY : Measure Y) (muX : Measure X)
  [SFinite muG] [SFinite muY] [muG.IsMulLeftInvariant] [NeZero muG]

/-- A measurable free-orbit product chart, including exactly the measure and
equivariance facts used by translation descent. -/
structure ProductChart where
  equiv : G × Y ≃ᵐ X
  measurePreserving : MeasurePreserving equiv (muG.prod muY) muX
  coordinate : X → Y
  coordinateQMP : Measure.QuasiMeasurePreserving coordinate muX muY
  coordinate_equiv : ∀ p : G × Y, coordinate (equiv p) = p.2
  coordinate_smul : ∀ a : G, ∀ x : X, coordinate (a • x) = coordinate x
  actionMeasurePreserving : ∀ a : G,
    MeasurePreserving (fun x : X => a • x) muX muX
  equivariant : ∀ a : G, ∀ p : G × Y,
    equiv (a * p.1, p.2) = a • equiv p

variable {muG : Measure G} {muY : Measure Y} {muX : Measure X}
  [SFinite muG] [SFinite muY] [muG.IsMulLeftInvariant] [NeZero muG]

namespace ProductChart

variable (C : ProductChart muG muY muX)

theorem symm_snd (x : X) : (C.equiv.symm x).2 = C.coordinate x := by
  let p := C.equiv.symm x
  calc
    p.2 = C.coordinate (C.equiv p) := (C.coordinate_equiv p).symm
    _ = C.coordinate x := congrArg C.coordinate (C.equiv.apply_symm_apply x)

/-- Invariant measurable classes on the action space. -/
def InvariantL0 : Submodule ℝ (L0 X muX) where
  carrier F := ∀ a : G,
    L0.pullbackₗ (fun x : X => a • x)
      (C.actionMeasurePreserving a).quasiMeasurePreserving F = F
  zero_mem' := fun a => LinearMap.map_zero _
  add_mem' := by
    intro F H hF hH a
    rw [LinearMap.map_add, hF a, hH a]
  smul_mem' := by
    intro c F hF a
    rw [LinearMap.map_smul, hF a]

/-- Pull a class on the orbit space back along the orbit coordinate. -/
def coordinateL0 : L0 Y muY →ₗ[ℝ] C.InvariantL0 where
  toFun f := ⟨L0.pullbackₗ C.coordinate C.coordinateQMP f, by
    intro a
    apply AEEqFun.ext
    let T := fun x : X => a • x
    let hT := (C.actionMeasurePreserving a).quasiMeasurePreserving
    let P := L0.pullbackₗ C.coordinate C.coordinateQMP f
    have houter := L0.coe_pullbackₗ T hT P
    have hinnerT := (L0.coe_pullbackₗ C.coordinate C.coordinateQMP f).comp_tendsto
      hT.tendsto_ae
    have hinner := L0.coe_pullbackₗ C.coordinate C.coordinateQMP f
    filter_upwards [houter, hinnerT, hinner] with x ho hit hi
    change (L0.pullbackₗ T hT P : X → ℝ) x = P (T x) at ho
    change P (T x) = f (C.coordinate (T x)) at hit
    change P x = f (C.coordinate x) at hi
    calc
      _ = P (T x) := ho
      _ = f (C.coordinate (T x)) := hit
      _ = f (C.coordinate x) := by rw [C.coordinate_smul]
      _ = P x := hi.symm⟩
  map_add' f g := by
    apply Subtype.ext
    exact LinearMap.map_add _ f g
  map_smul' c f := by
    apply Subtype.ext
    exact LinearMap.map_smul _ c f

theorem coordinateL0_injective : Function.Injective C.coordinateL0 := by
  intro f g hfg
  apply TranslationInvariant.comp_snd_injective (mu := muG) (nu := muY)
  apply AEEqFun.ext
  let he := C.measurePreserving.quasiMeasurePreserving
  let Pf := L0.pullbackₗ C.coordinate C.coordinateQMP f
  let Pg := L0.pullbackₗ C.coordinate C.coordinateQMP g
  have hclasses : Pf = Pg := congrArg Subtype.val hfg
  have hclassesAE : (Pf : X → ℝ) =ᵐ[muX] Pg := by rw [hclasses]
  have hclassesE := hclassesAE.comp_tendsto he.tendsto_ae
  have hfE := (L0.coe_pullbackₗ C.coordinate C.coordinateQMP f).comp_tendsto
    he.tendsto_ae
  have hgE := (L0.coe_pullbackₗ C.coordinate C.coordinateQMP g).comp_tendsto
    he.tendsto_ae
  have hfSnd := L0.coe_pullbackₗ Prod.snd
    (Measure.quasiMeasurePreserving_snd (μ := muG) (ν := muY)) f
  have hgSnd := L0.coe_pullbackₗ Prod.snd
    (Measure.quasiMeasurePreserving_snd (μ := muG) (ν := muY)) g
  filter_upwards [hfSnd, hgSnd, hfE, hgE, hclassesE] with p hfs hgs hfe hge hc
  change _ = f (C.coordinate (C.equiv p)) at hfe
  change _ = g (C.coordinate (C.equiv p)) at hge
  rw [C.coordinate_equiv] at hfe hge
  exact hfs.trans (hfe.symm.trans (hc.trans (hge.trans hgs.symm)))

theorem invariant_ae (F : C.InvariantL0) (a : G) :
    (F.1 : X → ℝ) ∘ (fun x => a • x) =ᵐ[muX] (F.1 : X → ℝ) := by
  let T := fun x : X => a • x
  let hT := (C.actionMeasurePreserving a).quasiMeasurePreserving
  have hpull := L0.coe_pullbackₗ T hT F.1
  have hclass : (L0.pullbackₗ T hT F.1 : X → ℝ) =ᵐ[muX] F.1 := by
    rw [F.2 a]
  exact hpull.symm.trans hclass

theorem coordinateL0_surjective : Function.Surjective C.coordinateL0 := by
  intro F
  let he := C.measurePreserving.quasiMeasurePreserving
  let P : L0 (G × Y) (muG.prod muY) := L0.pullbackₗ C.equiv he F.1
  let Pinv : TranslationInvariant.LeftInvariantL0 (mu := muG) (nu := muY) := ⟨P, by
    intro a
    apply AEEqFun.ext
    let T := TranslationInvariant.leftProduct (Y := Y) a
    let hT := (TranslationInvariant.measurePreserving_leftProduct
      (mu := muG) (nu := muY) a).quasiMeasurePreserving
    have houter := L0.coe_pullbackₗ T hT P
    have hPE := (L0.coe_pullbackₗ C.equiv he F.1).comp_tendsto hT.tendsto_ae
    have hP := L0.coe_pullbackₗ C.equiv he F.1
    have hactE := (C.invariant_ae F a).comp_tendsto he.tendsto_ae
    filter_upwards [houter, hPE, hP, hactE] with p ho hpe hp ha
    change _ = P (T p) at ho
    change P (T p) = F.1 (C.equiv (T p)) at hpe
    change P p = F.1 (C.equiv p) at hp
    change F.1 (a • C.equiv p) = F.1 (C.equiv p) at ha
    have hET : C.equiv (T p) = a • C.equiv p := by
      simpa only [T, TranslationInvariant.leftProduct] using C.equivariant a p
    exact ho.trans (hpe.trans ((congrArg F.1 hET).trans (ha.trans hp.symm)))⟩
  obtain ⟨f, hf⟩ := TranslationInvariant.sndInvariantL0_surjective
    (mu := muG) (nu := muY) Pinv
  refine ⟨f, ?_⟩
  apply Subtype.ext
  apply AEEqFun.ext
  have hfactor : L0.pullbackₗ Prod.snd
      (Measure.quasiMeasurePreserving_snd (μ := muG) (ν := muY)) f = P :=
    congrArg Subtype.val hf
  have hfactorAE :
      (L0.pullbackₗ Prod.snd
        (Measure.quasiMeasurePreserving_snd (μ := muG) (ν := muY)) f : G × Y → ℝ)
          =ᵐ[muG.prod muY] P := by rw [hfactor]
  have hsnd := L0.coe_pullbackₗ Prod.snd
    (Measure.quasiMeasurePreserving_snd (μ := muG) (ν := muY)) f
  have hP := L0.coe_pullbackₗ C.equiv he F.1
  have heqProd : (f : Y → ℝ) ∘ Prod.snd =ᵐ[muG.prod muY]
      (F.1 : X → ℝ) ∘ C.equiv := hsnd.symm.trans (hfactorAE.trans hP)
  have heqX := heqProd.comp_tendsto
    (MeasurePreserving.symm C.equiv C.measurePreserving).quasiMeasurePreserving.tendsto_ae
  have hcoord := L0.coe_pullbackₗ C.coordinate C.coordinateQMP f
  filter_upwards [hcoord, heqX] with x hc hex
  change _ = f (C.coordinate x) at hc
  change f ((C.equiv.symm x).2) = F.1 (C.equiv (C.equiv.symm x)) at hex
  rw [C.symm_snd, C.equiv.apply_symm_apply] at hex
  exact hc.trans hex

noncomputable def coordinateL0Equiv : L0 Y muY ≃ₗ[ℝ] C.InvariantL0 :=
  LinearEquiv.ofBijective C.coordinateL0
    ⟨C.coordinateL0_injective, C.coordinateL0_surjective⟩

/-- Invariant essentially bounded classes on the action space. -/
def InvariantLinfty : Submodule ℝ (Linfty X muX) where
  carrier F := ∀ a : G,
    Linfty.pullbackₗ (fun x : X => a • x)
      (C.actionMeasurePreserving a).quasiMeasurePreserving F = F
  zero_mem' := fun a => LinearMap.map_zero _
  add_mem' := by
    intro F H hF hH a
    rw [LinearMap.map_add, hF a, hH a]
  smul_mem' := by
    intro c F hF a
    rw [LinearMap.map_smul, hF a]

/-- Pull back an `L∞` class along the orbit coordinate. -/
noncomputable def coordinateLinfty : Linfty Y muY →ₗ[ℝ] C.InvariantLinfty where
  toFun f := ⟨Linfty.pullbackₗ C.coordinate C.coordinateQMP f, by
    intro a
    apply Subtype.ext
    apply AEEqFun.ext
    let T := fun x : X => a • x
    let hT := (C.actionMeasurePreserving a).quasiMeasurePreserving
    let P := Linfty.pullbackₗ C.coordinate C.coordinateQMP f
    have houter := Linfty.coeFn_pullbackₗ T hT P
    have hinnerT := (Linfty.coeFn_pullbackₗ C.coordinate C.coordinateQMP f).comp_tendsto
      hT.tendsto_ae
    have hinner := Linfty.coeFn_pullbackₗ C.coordinate C.coordinateQMP f
    filter_upwards [houter, hinnerT, hinner] with x ho hit hi
    change (Linfty.pullbackₗ T hT P : X → ℝ) x = P (T x) at ho
    change P (T x) = f (C.coordinate (T x)) at hit
    change P x = f (C.coordinate x) at hi
    calc
      _ = P (T x) := ho
      _ = f (C.coordinate (T x)) := hit
      _ = f (C.coordinate x) := by rw [C.coordinate_smul]
      _ = P x := hi.symm⟩
  map_add' f g := by
    apply Subtype.ext
    exact LinearMap.map_add _ f g
  map_smul' c f := by
    apply Subtype.ext
    exact LinearMap.map_smul _ c f

/-- Orbit-coordinate pullback is an isometry for the essential-supremum
norm.  The reverse inequality is obtained after pulling back through the
measure-preserving product chart, where the function is just a pullback by
the second projection. -/
@[simp]
theorem norm_coordinateLinfty (f : Linfty Y muY) :
    ‖C.coordinateLinfty f‖ = ‖f‖ := by
  let P : Linfty X muX := (C.coordinateLinfty f).1
  let E : Linfty (G × Y) (muG.prod muY) :=
    Lp.compMeasurePreserving C.equiv C.measurePreserving P
  let qmp := Measure.quasiMeasurePreserving_snd (μ := muG) (ν := muY)
  let S : Linfty (G × Y) (muG.prod muY) :=
    Linfty.pullbackₗ Prod.snd qmp f
  have hES : E = S := by
    apply Subtype.ext
    apply AEEqFun.ext
    have hE := Lp.coeFn_compMeasurePreserving P C.measurePreserving
    have hP := (Linfty.coeFn_pullbackₗ C.coordinate C.coordinateQMP f).comp_tendsto
      C.measurePreserving.quasiMeasurePreserving.tendsto_ae
    have hS := Linfty.coeFn_pullbackₗ Prod.snd qmp f
    filter_upwards [hE, hP, hS] with p he hp hs
    calc
      E p = P (C.equiv p) := he
      _ = f (C.coordinate (C.equiv p)) := hp
      _ = f p.2 := congrArg f (C.coordinate_equiv p)
      _ = S p := hs.symm
  change ‖P‖ = ‖f‖
  calc
    ‖P‖ = ‖E‖ := (Lp.norm_compMeasurePreserving P C.measurePreserving).symm
    _ = ‖S‖ := congrArg norm hES
    _ = ‖f‖ := by
      have h := TranslationInvariant.norm_sndInvariantLinfty
        (mu := muG) (nu := muY) f
      change ‖Linfty.pullbackₗ Prod.snd qmp f‖ = ‖f‖ at h
      exact h

theorem coordinateLinfty_injective : Function.Injective C.coordinateLinfty := by
  intro f g hfg
  apply Subtype.ext
  apply TranslationInvariant.comp_snd_injective (mu := muG) (nu := muY)
  apply AEEqFun.ext
  let he := C.measurePreserving.quasiMeasurePreserving
  let Pf := Linfty.pullbackₗ C.coordinate C.coordinateQMP f
  let Pg := Linfty.pullbackₗ C.coordinate C.coordinateQMP g
  have hclasses : Pf = Pg := congrArg Subtype.val hfg
  have hclassesAE : (Pf : X → ℝ) =ᵐ[muX] Pg := by rw [hclasses]
  have hclassesE := hclassesAE.comp_tendsto he.tendsto_ae
  have hfE := (Linfty.coeFn_pullbackₗ C.coordinate C.coordinateQMP f).comp_tendsto
    he.tendsto_ae
  have hgE := (Linfty.coeFn_pullbackₗ C.coordinate C.coordinateQMP g).comp_tendsto
    he.tendsto_ae
  have hfSnd := Linfty.coeFn_pullbackₗ Prod.snd
    (Measure.quasiMeasurePreserving_snd (μ := muG) (ν := muY)) f
  have hgSnd := Linfty.coeFn_pullbackₗ Prod.snd
    (Measure.quasiMeasurePreserving_snd (μ := muG) (ν := muY)) g
  filter_upwards [hfSnd, hgSnd, hfE, hgE, hclassesE] with p hfs hgs hfe hge hc
  change _ = f (C.coordinate (C.equiv p)) at hfe
  change _ = g (C.coordinate (C.equiv p)) at hge
  rw [C.coordinate_equiv] at hfe hge
  exact hfs.trans (hfe.symm.trans (hc.trans (hge.trans hgs.symm)))

theorem invariantLinfty_ae (F : C.InvariantLinfty) (a : G) :
    (F.1 : X → ℝ) ∘ (fun x => a • x) =ᵐ[muX] (F.1 : X → ℝ) := by
  let T := fun x : X => a • x
  let hT := (C.actionMeasurePreserving a).quasiMeasurePreserving
  have hpull := Linfty.coeFn_pullbackₗ T hT F.1
  have hclass : (Linfty.pullbackₗ T hT F.1 : X → ℝ) =ᵐ[muX] F.1 := by
    rw [F.2 a]
  exact hpull.symm.trans hclass

theorem coordinateLinfty_surjective : Function.Surjective C.coordinateLinfty := by
  intro F
  let he := C.measurePreserving.quasiMeasurePreserving
  let P : Linfty (G × Y) (muG.prod muY) := Linfty.pullbackₗ C.equiv he F.1
  let Pinv : TranslationInvariant.LeftInvariantLinfty (mu := muG) (nu := muY) := ⟨P, by
    intro a
    apply Subtype.ext
    apply AEEqFun.ext
    let T := TranslationInvariant.leftProduct (Y := Y) a
    let hT := (TranslationInvariant.measurePreserving_leftProduct
      (mu := muG) (nu := muY) a).quasiMeasurePreserving
    have houter := Linfty.coeFn_pullbackₗ T hT P
    have hPE := (Linfty.coeFn_pullbackₗ C.equiv he F.1).comp_tendsto hT.tendsto_ae
    have hP := Linfty.coeFn_pullbackₗ C.equiv he F.1
    have hactE := (C.invariantLinfty_ae F a).comp_tendsto he.tendsto_ae
    filter_upwards [houter, hPE, hP, hactE] with p ho hpe hp ha
    change _ = P (T p) at ho
    change P (T p) = F.1 (C.equiv (T p)) at hpe
    change P p = F.1 (C.equiv p) at hp
    change F.1 (a • C.equiv p) = F.1 (C.equiv p) at ha
    have hET : C.equiv (T p) = a • C.equiv p := by
      simpa only [T, TranslationInvariant.leftProduct] using C.equivariant a p
    exact ho.trans (hpe.trans ((congrArg F.1 hET).trans (ha.trans hp.symm)))⟩
  obtain ⟨f, hf⟩ := TranslationInvariant.sndInvariantLinfty_surjective
    (mu := muG) (nu := muY) Pinv
  refine ⟨f, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply AEEqFun.ext
  have hfactor : Linfty.pullbackₗ Prod.snd
      (Measure.quasiMeasurePreserving_snd (μ := muG) (ν := muY)) f = P :=
    congrArg Subtype.val hf
  have hfactorAE :
      (Linfty.pullbackₗ Prod.snd
        (Measure.quasiMeasurePreserving_snd (μ := muG) (ν := muY)) f : G × Y → ℝ)
          =ᵐ[muG.prod muY] P := by rw [hfactor]
  have hsnd := Linfty.coeFn_pullbackₗ Prod.snd
    (Measure.quasiMeasurePreserving_snd (μ := muG) (ν := muY)) f
  have hP := Linfty.coeFn_pullbackₗ C.equiv he F.1
  have heqProd : (f : Y → ℝ) ∘ Prod.snd =ᵐ[muG.prod muY]
      (F.1 : X → ℝ) ∘ C.equiv := hsnd.symm.trans (hfactorAE.trans hP)
  have heqX := heqProd.comp_tendsto
    (MeasurePreserving.symm C.equiv C.measurePreserving).quasiMeasurePreserving.tendsto_ae
  have hcoord := Linfty.coeFn_pullbackₗ C.coordinate C.coordinateQMP f
  filter_upwards [hcoord, heqX] with x hc hex
  change _ = f (C.coordinate x) at hc
  change f ((C.equiv.symm x).2) = F.1 (C.equiv (C.equiv.symm x)) at hex
  rw [C.symm_snd, C.equiv.apply_symm_apply] at hex
  exact hc.trans hex

noncomputable def coordinateLinftyEquiv :
    Linfty Y muY ≃ₗ[ℝ] C.InvariantLinfty :=
  LinearEquiv.ofBijective C.coordinateLinfty
    ⟨C.coordinateLinfty_injective, C.coordinateLinfty_surjective⟩

/-- The orbit-coordinate identification is a linear isometric equivalence,
not merely an algebraic equivalence. -/
noncomputable def coordinateLinftyIsometryEquiv :
    Linfty Y muY ≃ₗᵢ[ℝ] C.InvariantLinfty where
  toLinearEquiv := C.coordinateLinftyEquiv
  norm_map' := C.norm_coordinateLinfty

end ProductChart
end MeasurableOrbit

namespace ProjectiveAction

open OrbitChain Pfaffian

/-- The measurable effective-group product chart in degree three. -/
def measurableOrbitChart4 : MeasurableOrbit.ProductChart
    effectiveHaar measureU4 measureGeneric4 where
  equiv := orbitProductMeasurableEquiv4
  measurePreserving := orbitProductMeasurePreserving4
  coordinate := orbitCoord4
  coordinateQMP := orbitCoord4_quasiMeasurePreserving
  coordinate_equiv := fun p => orbitCoord4_orbitProductEquiv4 p.1 p.2
  coordinate_smul := orbitCoord4_effective_smul
  actionMeasurePreserving := measurePreserving_effective_smul4
  equivariant := fun a p => (effective_smul_orbitProductEquiv4 a p.1 p.2).symm

/-- The measurable effective-group product chart in degree four. -/
def measurableOrbitChart5 : MeasurableOrbit.ProductChart
    effectiveHaar measureU5 measureGeneric5 where
  equiv := orbitProductMeasurableEquiv5
  measurePreserving := orbitProductMeasurePreserving5
  coordinate := orbitCoord5
  coordinateQMP := orbitCoord5_quasiMeasurePreserving
  coordinate_equiv := fun p => orbitCoord5_orbitProductEquiv5 p.1 p.2
  coordinate_smul := orbitCoord5_effective_smul
  actionMeasurePreserving := measurePreserving_effective_smul5
  equivariant := fun a p => (effective_smul_orbitProductEquiv5 a p.1 p.2).symm

/-- The measurable effective-group product chart in degree five. -/
def measurableOrbitChart6 : MeasurableOrbit.ProductChart
    effectiveHaar measureU6 measureGeneric6 where
  equiv := orbitProductMeasurableEquiv6
  measurePreserving := orbitProductMeasurePreserving6
  coordinate := orbitCoord6
  coordinateQMP := orbitCoord6_quasiMeasurePreserving
  coordinate_equiv := fun p => orbitCoord6_orbitProductEquiv6 p.1 p.2
  coordinate_smul := orbitCoord6_effective_smul
  actionMeasurePreserving := measurePreserving_effective_smul6
  equivariant := fun a p => (effective_smul_orbitProductEquiv6 a p.1 p.2).symm

/-- Actual `L⁰` effective-action invariants on four generic points. -/
abbrev ActionInvariantL0_4 := measurableOrbitChart4.InvariantL0

/-- Actual `L⁰` effective-action invariants on five generic points. -/
abbrev ActionInvariantL0_5 := measurableOrbitChart5.InvariantL0

/-- Actual `L⁰` effective-action invariants on six generic points. -/
abbrev ActionInvariantL0_6 := measurableOrbitChart6.InvariantL0

/-- Actual `L∞` effective-action invariants on four generic points. -/
abbrev ActionInvariantLinfty_4 := measurableOrbitChart4.InvariantLinfty

/-- Actual `L∞` effective-action invariants on five generic points. -/
abbrev ActionInvariantLinfty_5 := measurableOrbitChart5.InvariantLinfty

/-- Actual `L∞` effective-action invariants on six generic points. -/
abbrev ActionInvariantLinfty_6 := measurableOrbitChart6.InvariantLinfty

/-- Four-point invariant `L⁰` cochains are exactly `L⁰(U₄)`. -/
noncomputable def coordinateInvariantL0Equiv4 :
    L0 U4 measureU4 ≃ₗ[ℝ] ActionInvariantL0_4 :=
  measurableOrbitChart4.coordinateL0Equiv

/-- Five-point invariant `L⁰` cochains are exactly `L⁰(U₅)`. -/
noncomputable def coordinateInvariantL0Equiv5 :
    L0 U5 measureU5 ≃ₗ[ℝ] ActionInvariantL0_5 :=
  measurableOrbitChart5.coordinateL0Equiv

/-- Six-point invariant `L⁰` cochains are exactly `L⁰(U₆)`. -/
noncomputable def coordinateInvariantL0Equiv6 :
    L0 U6 measureU6 ≃ₗ[ℝ] ActionInvariantL0_6 :=
  measurableOrbitChart6.coordinateL0Equiv

/-- Four-point invariant `L∞` cochains are exactly `L∞(U₄)`. -/
noncomputable def coordinateInvariantLinftyEquiv4 :
    Linfty U4 measureU4 ≃ₗ[ℝ] ActionInvariantLinfty_4 :=
  measurableOrbitChart4.coordinateLinftyEquiv

/-- Five-point invariant `L∞` cochains are exactly `L∞(U₅)`. -/
noncomputable def coordinateInvariantLinftyEquiv5 :
    Linfty U5 measureU5 ≃ₗ[ℝ] ActionInvariantLinfty_5 :=
  measurableOrbitChart5.coordinateLinftyEquiv

/-- Six-point invariant `L∞` cochains are exactly `L∞(U₆)`. -/
noncomputable def coordinateInvariantLinftyEquiv6 :
    Linfty U6 measureU6 ≃ₗ[ℝ] ActionInvariantLinfty_6 :=
  measurableOrbitChart6.coordinateLinftyEquiv

/-- Isometric form of the four-point invariant-coordinate theorem. -/
noncomputable def coordinateInvariantLinftyIsometryEquiv4 :
    Linfty U4 measureU4 ≃ₗᵢ[ℝ] ActionInvariantLinfty_4 :=
  measurableOrbitChart4.coordinateLinftyIsometryEquiv

/-- Isometric form of the five-point invariant-coordinate theorem. -/
noncomputable def coordinateInvariantLinftyIsometryEquiv5 :
    Linfty U5 measureU5 ≃ₗᵢ[ℝ] ActionInvariantLinfty_5 :=
  measurableOrbitChart5.coordinateLinftyIsometryEquiv

/-- Isometric form of the six-point invariant-coordinate theorem. -/
noncomputable def coordinateInvariantLinftyIsometryEquiv6 :
    Linfty U6 measureU6 ≃ₗᵢ[ℝ] ActionInvariantLinfty_6 :=
  measurableOrbitChart6.coordinateLinftyIsometryEquiv

end ProjectiveAction
end
end Sp4
