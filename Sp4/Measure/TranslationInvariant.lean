import Sp4.Measure.ProjectiveOrbit
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Descent of translation-invariant almost-everywhere functions

Let a measurable group `G` carry a nonzero sigma-finite left-invariant
measure, and let `Y` be another sigma-finite measure space.  This file proves,
without choosing invariant representatives, that the left-translation
invariants in `L⁰(G × Y)` are exactly the pullbacks of `L⁰(Y)`.  The same
argument proves the `L∞` statement and checks that essential boundedness
descends.

The proof uses Fubini twice.  Starting from invariance separately for every
translation, measurability permits the two group variables to be exchanged;
quasi-invariance under right translation then shows that almost every group
section agrees with one fixed section.
-/

namespace Sp4

open MeasureTheory

noncomputable section

universe u v

namespace TranslationInvariant

variable {G : Type u} {Y : Type v}
  [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [MeasurableSpace Y]
  {mu : Measure G} {nu : Measure Y}
  [SFinite mu] [SFinite nu] [mu.IsMulLeftInvariant] [NeZero mu]

def leftProduct (a : G) : G × Y → G × Y :=
  fun p => (a * p.1, p.2)

theorem measurePreserving_leftProduct (a : G) :
    MeasurePreserving (leftProduct (Y := Y) a) (mu.prod nu) (mu.prod nu) := by
  exact (measurePreserving_mul_left mu a).prod (MeasurePreserving.id nu)

theorem exists_comp_snd_of_left_invariant
    (F : (G × Y) →ₘ[mu.prod nu] ℝ)
    (hF : ∀ a : G,
      F.compMeasurePreserving (leftProduct (Y := Y) a)
        (measurePreserving_leftProduct (mu := mu) (nu := nu) a) = F) :
    ∃ f : Y →ₘ[nu] ℝ,
      f.compQuasiMeasurePreserving Prod.snd
        (Measure.quasiMeasurePreserving_snd (μ := mu) (ν := nu)) = F := by
  let f : G × Y → ℝ := F.aestronglyMeasurable.mk F
  have hf : StronglyMeasurable f :=
    F.aestronglyMeasurable.stronglyMeasurable_mk
  have hFf : (F : G × Y → ℝ) =ᵐ[mu.prod nu] f :=
    F.aestronglyMeasurable.ae_eq_mk
  have hinv (a : G) :
      (fun p : G × Y => f (a * p.1, p.2)) =ᵐ[mu.prod nu] f := by
    let T := leftProduct (Y := Y) a
    let hT := measurePreserving_leftProduct (mu := mu) (nu := nu) a
    have hclass :
        (F.compMeasurePreserving T hT : G × Y → ℝ) =ᵐ[mu.prod nu] F := by
      rw [hF a]
    have hrepComp : f ∘ T =ᵐ[mu.prod nu] (F : G × Y → ℝ) ∘ T :=
      hFf.symm.comp_tendsto hT.quasiMeasurePreserving.tendsto_ae
    have hcoeComp :
        (F : G × Y → ℝ) ∘ T =ᵐ[mu.prod nu]
          (F.compMeasurePreserving T hT : G × Y → ℝ) :=
      (F.coeFn_compMeasurePreserving hT).symm
    simpa only [Function.comp_def, T, leftProduct] using
      hrepComp.trans (hcoeComp.trans (hclass.trans hFf))
  have hall : ∀ᵐ a ∂mu, ∀ᵐ p ∂mu.prod nu,
      f (a * p.1, p.2) = f p :=
    Filter.Eventually.of_forall hinv
  have hleft : StronglyMeasurable
      (fun z : G × (G × Y) => f (z.1 * z.2.1, z.2.2)) := by
    exact hf.comp_measurable (by fun_prop)
  have hright : StronglyMeasurable
      (fun z : G × (G × Y) => f z.2) :=
    hf.comp_measurable measurable_snd
  have hset : MeasurableSet
      {z : G × (G × Y) | f (z.1 * z.2.1, z.2.2) = f z.2} :=
    hleft.measurableSet_eq_fun hright
  have hswap : ∀ᵐ p ∂mu.prod nu, ∀ᵐ a ∂mu,
      f (a * p.1, p.2) = f p :=
    (Measure.ae_ae_comm hset).mp hall
  have hdecomp : ∀ᵐ g ∂mu, ∀ᵐ y ∂nu, ∀ᵐ a ∂mu,
      f (a * g, y) = f (g, y) :=
    Measure.ae_ae_of_ae_prod hswap
  obtain ⟨g0, hg0⟩ := hdecomp.exists
  have hsections : ∀ᵐ y ∂nu, ∀ᵐ g ∂mu,
      f (g, y) = f (g0, y) := by
    filter_upwards [hg0] with y hy
    simpa [mul_assoc] using
      (quasiMeasurePreserving_mul_right mu g0⁻¹).ae hy
  have hsec : StronglyMeasurable (fun y : Y => f (g0, y)) :=
    hf.comp_measurable measurable_prodMk_left
  have hleft' : StronglyMeasurable
      (fun z : Y × G => f (z.2, z.1)) :=
    hf.comp_measurable measurable_swap
  have hright' : StronglyMeasurable
      (fun z : Y × G => f (g0, z.1)) :=
    hsec.comp_measurable measurable_fst
  have hset' : MeasurableSet
      {z : Y × G | f (z.2, z.1) = f (g0, z.1)} :=
    hleft'.measurableSet_eq_fun hright'
  have hsections' : ∀ᵐ g ∂mu, ∀ᵐ y ∂nu,
      f (g, y) = f (g0, y) :=
    (Measure.ae_ae_comm hset').mp hsections
  have hprod : ∀ᵐ p ∂mu.prod nu, f p = f (g0, p.2) := by
    have hset'' : MeasurableSet
        {p : G × Y | f p = f (g0, p.2)} :=
      hf.measurableSet_eq_fun (hsec.comp_measurable measurable_snd)
    exact (Measure.ae_prod_iff_ae_ae hset'').mpr hsections'
  let f0 : Y →ₘ[nu] ℝ := AEEqFun.mk (fun y => f (g0, y)) hsec.aestronglyMeasurable
  refine ⟨f0, AEEqFun.ext ?_⟩
  have hcomp := AEEqFun.coeFn_compQuasiMeasurePreserving f0
    (Measure.quasiMeasurePreserving_snd (μ := mu) (ν := nu))
  have hf0 : (f0 : Y → ℝ) =ᵐ[nu] fun y => f (g0, y) :=
    AEEqFun.coeFn_mk _ _
  have hprod' : (fun p : G × Y => f (g0, p.2)) =ᵐ[mu.prod nu] f :=
    hprod.mono fun _ hp => hp.symm
  exact hcomp.trans ((hf0.comp_tendsto
    (Measure.quasiMeasurePreserving_snd (μ := mu) (ν := nu)).tendsto_ae).trans
      (hprod'.trans hFf.symm))

theorem comp_snd_injective : Function.Injective
    (fun f : Y →ₘ[nu] ℝ =>
      f.compQuasiMeasurePreserving Prod.snd
        (Measure.quasiMeasurePreserving_snd (μ := mu) (ν := nu))) := by
  intro f g hfg
  apply AEEqFun.ext
  let qmp := Measure.quasiMeasurePreserving_snd (μ := mu) (ν := nu)
  have hf := AEEqFun.coeFn_compQuasiMeasurePreserving f qmp
  have hg := AEEqFun.coeFn_compQuasiMeasurePreserving g qmp
  have hfg' : f.compQuasiMeasurePreserving Prod.snd qmp =
      g.compQuasiMeasurePreserving Prod.snd qmp := by
    simpa only [qmp] using hfg
  have hclasses :
      (f.compQuasiMeasurePreserving Prod.snd qmp : G × Y → ℝ) =ᵐ[mu.prod nu]
        (g.compQuasiMeasurePreserving Prod.snd qmp : G × Y → ℝ) := by
    rw [hfg']
  have hprod : (f : Y → ℝ) ∘ Prod.snd =ᵐ[mu.prod nu]
      (g : Y → ℝ) ∘ Prod.snd :=
    hf.symm.trans (hclasses.trans hg)
  have hsections : ∀ᵐ _x ∂mu, (f : Y → ℝ) =ᵐ[nu] g :=
    Measure.ae_ae_of_ae_prod hprod
  exact hsections.exists.choose_spec

/-- `L⁰` classes invariant under every left translation in the first
factor of `G × Y`. -/
def LeftInvariantL0 : Submodule ℝ ((G × Y) →ₘ[mu.prod nu] ℝ) where
  carrier F := ∀ a : G,
    L0.pullbackₗ (leftProduct (Y := Y) a)
      (measurePreserving_leftProduct (mu := mu) (nu := nu) a).quasiMeasurePreserving F = F
  zero_mem' := by
    intro a
    exact LinearMap.map_zero _
  add_mem' := by
    intro F H hF hH a
    rw [LinearMap.map_add, hF a, hH a]
  smul_mem' := by
    intro c F hF a
    rw [LinearMap.map_smul, hF a]

theorem mem_leftInvariantL0 (F : (G × Y) →ₘ[mu.prod nu] ℝ) :
    F ∈ LeftInvariantL0 (mu := mu) (nu := nu) ↔
      ∀ a : G,
        L0.pullbackₗ (leftProduct (Y := Y) a)
          (measurePreserving_leftProduct (mu := mu) (nu := nu) a).quasiMeasurePreserving F = F :=
  Iff.rfl

/-- Pullback by the second projection, with its left-invariance proof. -/
def sndInvariantL0 :
    (Y →ₘ[nu] ℝ) →ₗ[ℝ] LeftInvariantL0 (mu := mu) (nu := nu) where
  toFun f := ⟨L0.pullbackₗ Prod.snd
      (Measure.quasiMeasurePreserving_snd (μ := mu) (ν := nu)) f, by
    intro a
    apply AEEqFun.ext
    let T := leftProduct (Y := Y) a
    let hT := (measurePreserving_leftProduct (mu := mu) (nu := nu) a).quasiMeasurePreserving
    let qmp := Measure.quasiMeasurePreserving_snd (μ := mu) (ν := nu)
    let P := L0.pullbackₗ Prod.snd qmp f
    have houter := L0.coe_pullbackₗ T hT P
    have hinnerT := (L0.coe_pullbackₗ Prod.snd qmp f).comp_tendsto hT.tendsto_ae
    have hinner := L0.coe_pullbackₗ Prod.snd qmp f
    filter_upwards [houter, hinnerT, hinner] with p hp ho hi
    simpa only [Function.comp_def, T, leftProduct] using hp.trans (ho.trans hi.symm)⟩
  map_add' f g := by
    apply Subtype.ext
    exact LinearMap.map_add _ f g
  map_smul' c f := by
    apply Subtype.ext
    exact LinearMap.map_smul _ c f

theorem sndInvariantL0_injective :
    Function.Injective (sndInvariantL0 (mu := mu) (nu := nu)) := by
  intro f g h
  apply comp_snd_injective (mu := mu) (nu := nu)
  exact congrArg Subtype.val h

theorem sndInvariantL0_surjective :
    Function.Surjective (sndInvariantL0 (mu := mu) (nu := nu)) := by
  intro F
  have hInv : ∀ a : G,
      F.1.compMeasurePreserving (leftProduct (Y := Y) a)
        (measurePreserving_leftProduct (mu := mu) (nu := nu) a) = F.1 := by
    intro a
    exact F.2 a
  obtain ⟨f, hf⟩ := exists_comp_snd_of_left_invariant
    (mu := mu) (nu := nu) F.1 hInv
  refine ⟨f, ?_⟩
  apply Subtype.ext
  exact hf

/-- Translation descent: invariant `L⁰(G × Y)` is canonically linearly
equivalent to `L⁰(Y)`. -/
noncomputable def leftInvariantL0Equiv :
    (Y →ₘ[nu] ℝ) ≃ₗ[ℝ] LeftInvariantL0 (mu := mu) (nu := nu) :=
  LinearEquiv.ofBijective (sndInvariantL0 (mu := mu) (nu := nu))
    ⟨sndInvariantL0_injective (mu := mu) (nu := nu),
      sndInvariantL0_surjective (mu := mu) (nu := nu)⟩

/-- `L∞` classes invariant under every left translation in the first
factor of `G × Y`. -/
def LeftInvariantLinfty : Submodule ℝ (Linfty (G × Y) (mu.prod nu)) where
  carrier F := ∀ a : G,
    Linfty.pullbackₗ (leftProduct (Y := Y) a)
      (measurePreserving_leftProduct (mu := mu) (nu := nu) a).quasiMeasurePreserving F = F
  zero_mem' := by
    intro a
    exact LinearMap.map_zero _
  add_mem' := by
    intro F H hF hH a
    rw [LinearMap.map_add, hF a, hH a]
  smul_mem' := by
    intro c F hF a
    rw [LinearMap.map_smul, hF a]

theorem mem_leftInvariantLinfty (F : Linfty (G × Y) (mu.prod nu)) :
    F ∈ LeftInvariantLinfty (mu := mu) (nu := nu) ↔
      ∀ a : G,
        Linfty.pullbackₗ (leftProduct (Y := Y) a)
          (measurePreserving_leftProduct (mu := mu) (nu := nu) a).quasiMeasurePreserving F = F :=
  Iff.rfl

/-- Pullback by the second projection on invariant `L∞`. -/
noncomputable def sndInvariantLinfty :
    Linfty Y nu →ₗ[ℝ] LeftInvariantLinfty (mu := mu) (nu := nu) where
  toFun f := ⟨Linfty.pullbackₗ Prod.snd
      (Measure.quasiMeasurePreserving_snd (μ := mu) (ν := nu)) f, by
    intro a
    apply Subtype.ext
    apply AEEqFun.ext
    let T := leftProduct (Y := Y) a
    let hT := (measurePreserving_leftProduct (mu := mu) (nu := nu) a).quasiMeasurePreserving
    let qmp := Measure.quasiMeasurePreserving_snd (μ := mu) (ν := nu)
    let P := Linfty.pullbackₗ Prod.snd qmp f
    have houter := Linfty.coeFn_pullbackₗ T hT P
    have hinnerT := (Linfty.coeFn_pullbackₗ Prod.snd qmp f).comp_tendsto hT.tendsto_ae
    have hinner := Linfty.coeFn_pullbackₗ Prod.snd qmp f
    filter_upwards [houter, hinnerT, hinner] with p hp ho hi
    simpa only [Function.comp_def, T, leftProduct] using hp.trans (ho.trans hi.symm)⟩
  map_add' f g := by
    apply Subtype.ext
    exact LinearMap.map_add _ f g
  map_smul' c f := by
    apply Subtype.ext
    exact LinearMap.map_smul _ c f

/-- Pullback by the second projection preserves the essential-supremum norm
when the first-factor measure is nonzero. -/
@[simp]
theorem norm_sndInvariantLinfty (f : Linfty Y nu) :
    ‖sndInvariantLinfty (mu := mu) (nu := nu) f‖ = ‖f‖ := by
  let qmp := Measure.quasiMeasurePreserving_snd (μ := mu) (ν := nu)
  let P : Linfty (G × Y) (mu.prod nu) := Linfty.pullbackₗ Prod.snd qmp f
  change ‖P‖ = ‖f‖
  apply le_antisymm
  · exact Linfty.norm_pullbackₗ_le Prod.snd qmp f
  · have hpull := Linfty.coeFn_pullbackₗ Prod.snd qmp f
    have hboundP := Linfty.ae_abs_le_norm P
    have hboundProd : ∀ᵐ p ∂mu.prod nu, |f p.2| ≤ ‖P‖ := by
      filter_upwards [hpull, hboundP] with p hp hb
      calc
        |f p.2| = |P p| := congrArg abs hp.symm
        _ ≤ ‖P‖ := hb
    have hboundSections : ∀ᵐ _g ∂mu, ∀ᵐ y ∂nu, |f y| ≤ ‖P‖ :=
      Measure.ae_ae_of_ae_prod hboundProd
    exact Linfty.norm_le_of_ae_abs_le f ‖P‖ (norm_nonneg _)
      hboundSections.exists.choose_spec

theorem sndInvariantLinfty_injective :
    Function.Injective (sndInvariantLinfty (mu := mu) (nu := nu)) := by
  intro f g h
  apply Subtype.ext
  apply comp_snd_injective (mu := mu) (nu := nu)
  exact congrArg (fun z : LeftInvariantLinfty (mu := mu) (nu := nu) => z.1.1) h

theorem sndInvariantLinfty_surjective :
    Function.Surjective (sndInvariantLinfty (mu := mu) (nu := nu)) := by
  intro F
  let F0 : LeftInvariantL0 (mu := mu) (nu := nu) := ⟨F.1.1, by
    intro a
    let hT := (measurePreserving_leftProduct (mu := mu) (nu := nu) a).quasiMeasurePreserving
    change F.1.1.compQuasiMeasurePreserving (leftProduct (Y := Y) a)
      hT = F.1.1
    exact congrArg Subtype.val (F.2 a)⟩
  obtain ⟨f, hf⟩ := sndInvariantL0_surjective (mu := mu) (nu := nu) F0
  have hfactor : L0.pullbackₗ Prod.snd
      (Measure.quasiMeasurePreserving_snd (μ := mu) (ν := nu)) f = F.1.1 :=
    congrArg Subtype.val hf
  let qmp := Measure.quasiMeasurePreserving_snd (μ := mu) (ν := nu)
  have hpull := L0.coe_pullbackₗ Prod.snd qmp f
  have hclass :
      (L0.pullbackₗ Prod.snd qmp f : G × Y → ℝ) =ᵐ[mu.prod nu]
        (F.1.1 : G × Y → ℝ) := by
    rw [hfactor]
  have hboundProd : ∀ᵐ p ∂mu.prod nu, |f p.2| ≤ ‖F.1‖ := by
    have hpullF : (f : Y → ℝ) ∘ Prod.snd =ᵐ[mu.prod nu]
        (F.1.1 : G × Y → ℝ) := hpull.symm.trans hclass
    filter_upwards [hpullF, Linfty.ae_abs_le_norm F.1] with p hp hb
    change f p.2 = F.1.1 p at hp
    rw [hp]
    exact hb
  have hboundSections : ∀ᵐ _g ∂mu, ∀ᵐ y ∂nu, |f y| ≤ ‖F.1‖ :=
    Measure.ae_ae_of_ae_prod hboundProd
  have hbound : ∀ᵐ y ∂nu, |f y| ≤ ‖F.1‖ :=
    hboundSections.exists.choose_spec
  let b : Linfty Y nu := Linfty.ofClassBound f ‖F.1‖ (norm_nonneg _) hbound
  refine ⟨b, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change L0.pullbackₗ Prod.snd qmp b.1 = F.1.1
  rw [show b.1 = f by rfl]
  exact hfactor

/-- Translation descent also preserves essential boundedness. -/
noncomputable def leftInvariantLinftyEquiv :
    Linfty Y nu ≃ₗ[ℝ] LeftInvariantLinfty (mu := mu) (nu := nu) :=
  LinearEquiv.ofBijective (sndInvariantLinfty (mu := mu) (nu := nu))
    ⟨sndInvariantLinfty_injective (mu := mu) (nu := nu),
      sndInvariantLinfty_surjective (mu := mu) (nu := nu)⟩

end TranslationInvariant
end
end Sp4
