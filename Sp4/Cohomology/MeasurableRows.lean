import Sp4.Basic.FinTuple
import Sp4.Measure.L0
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Exact measurable deletion rows

This file builds the augmented deletion complex on finite powers of a probability
space, with an arbitrary measured parameter space carried along.  The pointwise
cone identity is separated from the Fubini argument used to choose a legitimate
slice of an almost-everywhere class.
-/

namespace Sp4
namespace MeasurableRows

open MeasureTheory
open scoped BigOperators

noncomputable section

universe uX uZ

/-- Product probability measure on ordered `n`-tuples. -/
def tupleMeasure {X : Type uX} [MeasurableSpace X]
    (mu : Measure X) (n : ℕ) : Measure (FinTuple X n) :=
  Measure.pi fun _ => mu

instance tupleMeasure.instSigmaFinite
    {X : Type uX} [MeasurableSpace X] (mu : Measure X)
    [SigmaFinite mu] (n : ℕ) :
    SigmaFinite (tupleMeasure mu n) := by
  unfold tupleMeasure
  infer_instance

instance tupleMeasure.instIsProbabilityMeasure
    {X : Type uX} [MeasurableSpace X] (mu : Measure X)
    [IsProbabilityMeasure mu] (n : ℕ) :
    IsProbabilityMeasure (tupleMeasure mu n) := by
  unfold tupleMeasure
  infer_instance

/-- Delete one tuple coordinate while retaining an auxiliary parameter. -/
def parameterFace {X : Type uX} {Z : Type uZ} {n : ℕ}
    (i : Fin (n + 1)) : FinTuple X (n + 1) × Z → FinTuple X n × Z :=
  fun x => (FinTuple.delete i x.1, x.2)

/-- The pointwise alternating deletion operator. -/
def pointCoboundary {X : Type uX} {Z : Type uZ} {n : ℕ}
    (f : FinTuple X n × Z → ℝ) : FinTuple X (n + 1) × Z → ℝ :=
  fun x => ∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val * f (parameterFace i x)

@[simp]
theorem delete_cons_zero {X : Type uX} {n : ℕ}
    (y : X) (x : FinTuple X n) :
    FinTuple.delete 0 (Fin.cons y x) = x := by
  funext i
  simp [FinTuple.delete]

@[simp]
theorem delete_cons_succ {X : Type uX} {n : ℕ}
    (y : X) (x : FinTuple X (n + 1)) (i : Fin (n + 1)) :
    FinTuple.delete i.succ (Fin.cons y x) =
      Fin.cons y (FinTuple.delete i x) := by
  exact Fin.cons_comp_succ_succAbove y x i

/-- Expanding the coboundary after adjoining a first vertex. -/
theorem pointCoboundary_cons {X : Type uX} {Z : Type uZ} {n : ℕ}
    (f : FinTuple X (n + 1) × Z → ℝ) (y : X)
    (x : FinTuple X (n + 1) × Z) :
    pointCoboundary f (Fin.cons y x.1, x.2) =
      f x - pointCoboundary (fun w : FinTuple X n × Z =>
        f (Fin.cons y w.1, w.2)) x := by
  rw [pointCoboundary, Fin.sum_univ_succ]
  simp only [parameterFace, delete_cons_zero, delete_cons_succ,
    Fin.val_zero, Fin.val_succ, pow_zero, one_mul]
  rw [pointCoboundary]
  simp only [parameterFace]
  have hterm (i : Fin (n + 1)) :
      (-1 : ℝ) ^ (i.val + 1) *
          f (Fin.cons y (FinTuple.delete i x.1), x.2) =
        -((-1 : ℝ) ^ i.val *
          f (Fin.cons y (FinTuple.delete i x.1), x.2)) := by
    rw [pow_succ]
    ring
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib]
  ring

/-- The cone identity `δs + sδ = id`, before passing to a.e. classes. -/
theorem point_cone_identity {X : Type uX} {Z : Type uZ} {n : ℕ}
    (f : FinTuple X (n + 1) × Z → ℝ) (y : X)
    (x : FinTuple X (n + 1) × Z) :
    pointCoboundary (fun w : FinTuple X n × Z =>
        f (Fin.cons y w.1, w.2)) x +
      pointCoboundary f (Fin.cons y x.1, x.2) = f x := by
  rw [pointCoboundary_cons]
  ring

/-- The pointwise deletion differential squares to zero. -/
theorem pointCoboundary_sq {X : Type uX} {Z : Type uZ} {n : ℕ}
    (f : FinTuple X n × Z → ℝ) (x : FinTuple X (n + 2) × Z) :
    pointCoboundary (pointCoboundary f) x = 0 := by
  simp only [pointCoboundary, parameterFace, Finset.mul_sum]
  rw [← Fintype.sum_prod_type']
  let swapPair : Fin (n + 2) × Fin (n + 1) →
      Fin (n + 2) × Fin (n + 1) :=
    fun p => (p.1.succAbove p.2, p.2.predAbove p.1)
  classical
  apply Finset.sum_involution (s := Finset.univ)
    (fun p _ => swapPair p)
  · rintro ⟨j, i⟩ _
    have hsign := Fin.neg_one_pow_succAbove_add_predAbove
      (R := ℝ) j i
    rw [FinTuple.delete_delete_swap x.1 i j]
    dsimp [swapPair]
    change
      (-1 : ℝ) ^ j.val * ((-1 : ℝ) ^ i.val * _) +
        (-1 : ℝ) ^ (j.succAbove i).val *
          ((-1 : ℝ) ^ (i.predAbove j).val * _) = 0
    rw [← mul_assoc, ← mul_assoc]
    rw [← pow_add, ← pow_add, hsign]
    ring
  · intro p _ _ hp
    exact Fin.succAbove_ne p.1 p.2 (congrArg Prod.fst hp)
  · simp
  · rintro ⟨j, i⟩ _
    apply Prod.ext
    · exact Fin.succAbove_succAbove_predAbove j i
    · exact Fin.predAbove_predAbove_succAbove j i

variable {X : Type uX} {Z : Type uZ}
  [MeasurableSpace X] [MeasurableSpace Z]
  (mu : Measure X) (nu : Measure Z)
  [IsProbabilityMeasure mu] [SFinite nu]

/-- Coordinate deletion preserves the product probability measure. -/
theorem measurePreserving_delete {n : ℕ} (i : Fin (n + 1)) :
    MeasurePreserving (FinTuple.delete i)
      (tupleMeasure mu (n + 1)) (tupleMeasure mu n) := by
  have hsplit := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => mu) i
  have hsnd : MeasurePreserving Prod.snd
      (mu.prod (tupleMeasure mu n)) (tupleMeasure mu n) :=
    measurePreserving_snd
  have h := hsnd.comp hsplit
  convert h using 1
  · funext x
    rfl
  · rfl

/-- Deletion in the tuple factor preserves the product measure with parameters. -/
theorem measurePreserving_parameterFace {n : ℕ} (i : Fin (n + 1)) :
    MeasurePreserving (parameterFace (Z := Z) i)
      ((tupleMeasure mu (n + 1)).prod nu)
      ((tupleMeasure mu n).prod nu) := by
  exact (measurePreserving_delete mu i).prod (MeasurePreserving.id nu)

/-- Split off the first tuple coordinate and retain the auxiliary parameter. -/
def splitFirst (n : ℕ) :
    (FinTuple X (n + 1) × Z) ≃ᵐ X × (FinTuple X n × Z) :=
  ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0).prodCongr
      (MeasurableEquiv.refl Z)).trans
    MeasurableEquiv.prodAssoc

/-- Splitting off the first coordinate preserves the iterated product measure. -/
theorem measurePreserving_splitFirst (n : ℕ) :
    MeasurePreserving (splitFirst (X := X) (Z := Z) n)
      ((tupleMeasure mu (n + 1)).prod nu)
      (mu.prod ((tupleMeasure mu n).prod nu)) := by
  exact
    (measurePreserving_prodAssoc mu (tupleMeasure mu n) nu).comp
      ((measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => mu) 0).prod (MeasurePreserving.id nu))

@[simp]
theorem splitFirst_cons (n : ℕ) (y : X) (x : FinTuple X n) (z : Z) :
    splitFirst (X := X) (Z := Z) n (Fin.cons y x, z) = (y, (x, z)) := by
  rfl

@[simp]
theorem splitFirst_symm_apply (n : ℕ) (y : X) (x : FinTuple X n) (z : Z) :
    (splitFirst (X := X) (Z := Z) n).symm (y, (x, z)) = (Fin.cons y x, z) := by
  apply (splitFirst (X := X) (Z := Z) n).injective
  simp

/-- One deletion face on `L⁰` classes. -/
def face (n : ℕ) (i : Fin (n + 1)) :
    L0 (FinTuple X n × Z) ((tupleMeasure mu n).prod nu) →ₗ[ℝ]
      L0 (FinTuple X (n + 1) × Z) ((tupleMeasure mu (n + 1)).prod nu) :=
  L0.pullbackₗ (parameterFace (Z := Z) i)
    (measurePreserving_parameterFace mu nu i).quasiMeasurePreserving

@[simp]
theorem coe_face {n : ℕ} (i : Fin (n + 1))
    (f : L0 (FinTuple X n × Z) ((tupleMeasure mu n).prod nu)) :
    (face mu nu n i f : FinTuple X (n + 1) × Z → ℝ)
      =ᵐ[(tupleMeasure mu (n + 1)).prod nu]
        f ∘ parameterFace i :=
  L0.coe_pullbackₗ (parameterFace i)
    (measurePreserving_parameterFace mu nu i).quasiMeasurePreserving f

/-- Alternating deletion on `L⁰` classes. -/
def coboundary (n : ℕ) :
    L0 (FinTuple X n × Z) ((tupleMeasure mu n).prod nu) →ₗ[ℝ]
      L0 (FinTuple X (n + 1) × Z) ((tupleMeasure mu (n + 1)).prod nu) :=
  L0.weightedPullbackₗ (fun i => parameterFace (Z := Z) i)
    (fun i => (measurePreserving_parameterFace mu nu i).quasiMeasurePreserving)
    (fun i => (-1 : ℝ) ^ i.val)

theorem coboundary_eq_sum_faces (n : ℕ) :
    coboundary mu nu n =
      ∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val • face mu nu n i := by
  rfl

theorem coe_coboundary {n : ℕ}
    (f : L0 (FinTuple X n × Z) ((tupleMeasure mu n).prod nu)) :
    (coboundary mu nu n f : FinTuple X (n + 1) × Z → ℝ)
      =ᵐ[(tupleMeasure mu (n + 1)).prod nu] pointCoboundary f := by
  exact L0.coeFn_weightedPullbackₗ
    (fun i => parameterFace (Z := Z) i)
    (fun i => (measurePreserving_parameterFace mu nu i).quasiMeasurePreserving)
    (fun i => (-1 : ℝ) ^ i.val) f

theorem pointCoboundary_ae_congr {n : ℕ}
    {f g : FinTuple X n × Z → ℝ}
    (hfg : f =ᵐ[(tupleMeasure mu n).prod nu] g) :
    pointCoboundary f
      =ᵐ[(tupleMeasure mu (n + 1)).prod nu] pointCoboundary g := by
  have hfaces : ∀ᵐ x ∂(tupleMeasure mu (n + 1)).prod nu,
      ∀ i : Fin (n + 1), f (parameterFace i x) = g (parameterFace i x) :=
    Filter.eventually_all.2 fun i =>
      (measurePreserving_parameterFace mu nu i).quasiMeasurePreserving.ae hfg
  filter_upwards [hfaces] with x hx
  simp only [pointCoboundary]
  apply Finset.sum_congr rfl
  intro i _
  rw [hx i]

/-- Alternating deletion on `L⁰` is a cochain complex. -/
theorem coboundary_sq {n : ℕ}
    (f : L0 (FinTuple X n × Z) ((tupleMeasure mu n).prod nu)) :
    coboundary mu nu (n + 1) (coboundary mu nu n f) = 0 := by
  apply AEEqFun.ext
  have houter := coe_coboundary mu nu (coboundary mu nu n f)
  have hinner := pointCoboundary_ae_congr mu nu (coe_coboundary mu nu f)
  filter_upwards [houter, hinner,
    (AEEqFun.coeFn_zero :
      ((0 : L0 (FinTuple X (n + 2) × Z)
        ((tupleMeasure mu (n + 2)).prod nu)) :
          FinTuple X (n + 2) × Z → ℝ)
        =ᵐ[(tupleMeasure mu (n + 2)).prod nu]
          (0 : FinTuple X (n + 2) × Z → ℝ))] with x ho hi hz
  rw [ho, hi, pointCoboundary_sq]
  exact hz.symm

/-- Every positive-degree measurable cocycle in the deletion row is a
coboundary.  The primitive is obtained by adjoining one suitably chosen first
coordinate; Fubini supplies a coordinate for which both measurability and the
cocycle identity hold on the required slices. -/
theorem exists_primitive {n : ℕ}
    (F : L0 (FinTuple X (n + 1) × Z)
      ((tupleMeasure mu (n + 1)).prod nu))
    (hF : coboundary mu nu (n + 1) F = 0) :
    ∃ f : L0 (FinTuple X n × Z) ((tupleMeasure mu n).prod nu),
      coboundary mu nu n f = F := by
  let e := splitFirst (X := X) (Z := Z) n
  have he : MeasurePreserving e
      ((tupleMeasure mu (n + 1)).prod nu)
      (mu.prod ((tupleMeasure mu n).prod nu)) :=
    measurePreserving_splitFirst mu nu n
  have hmeasProd : AEStronglyMeasurable
      (fun p : X × (FinTuple X n × Z) => F (e.symm p))
      (mu.prod ((tupleMeasure mu n).prod nu)) :=
    F.aestronglyMeasurable.comp_quasiMeasurePreserving
      he.symm.quasiMeasurePreserving
  have hmeasSlices : ∀ᵐ y ∂mu,
      AEStronglyMeasurable
        (fun w : FinTuple X n × Z => F (Fin.cons y w.1, w.2))
        ((tupleMeasure mu n).prod nu) := by
    have h := hmeasProd.prodMk_left
    filter_upwards [h] with y hy
    convert hy using 1
    funext w
    rcases w with ⟨x, z⟩
    simp [e]
  have hdeltaZero :
      (pointCoboundary F : FinTuple X (n + 2) × Z → ℝ)
        =ᵐ[((tupleMeasure mu (n + 2)).prod nu)] 0 := by
    have hrep := coe_coboundary mu nu F
    have hzero :
        ((coboundary mu nu (n + 1) F :
            L0 (FinTuple X (n + 2) × Z)
              ((tupleMeasure mu (n + 2)).prod nu)) :
              FinTuple X (n + 2) × Z → ℝ)
          =ᵐ[((tupleMeasure mu (n + 2)).prod nu)] 0 := by
      rw [hF]
      exact AEEqFun.coeFn_zero
    exact hrep.symm.trans hzero
  have hslicedZero : ∀ᵐ y ∂mu, ∀ᵐ x ∂((tupleMeasure mu (n + 1)).prod nu),
      pointCoboundary F (Fin.cons y x.1, x.2) = 0 := by
    let e' := splitFirst (X := X) (Z := Z) (n + 1)
    have he' : MeasurePreserving e'
        ((tupleMeasure mu (n + 2)).prod nu)
        (mu.prod ((tupleMeasure mu (n + 1)).prod nu)) :=
      measurePreserving_splitFirst mu nu (n + 1)
    have hpull := he'.symm.quasiMeasurePreserving.ae hdeltaZero
    have hcurry := Measure.ae_ae_of_ae_prod hpull
    filter_upwards [hcurry] with y hy
    filter_upwards [hy] with x hx
    rcases x with ⟨x, z⟩
    simpa [e'] using hx
  obtain ⟨y, hyMeas, hyZero⟩ := (hmeasSlices.and hslicedZero).exists
  let f : L0 (FinTuple X n × Z) ((tupleMeasure mu n).prod nu) :=
    AEEqFun.mk (fun w : FinTuple X n × Z => F (Fin.cons y w.1, w.2)) hyMeas
  refine ⟨f, ?_⟩
  apply AEEqFun.ext
  have hout := coe_coboundary mu nu f
  have hf : (f : FinTuple X n × Z → ℝ)
      =ᵐ[((tupleMeasure mu n).prod nu)]
        (fun w : FinTuple X n × Z => F (Fin.cons y w.1, w.2)) := by
    exact AEEqFun.coeFn_mk _ _
  have hcongr := pointCoboundary_ae_congr mu nu hf
  filter_upwards [hout, hcongr, hyZero] with x houtx hcongrx hzerox
  rw [houtx, hcongrx]
  simpa [hzerox] using point_cone_identity F y x

/-- The first map of the augmented measurable deletion row is injective. -/
theorem coboundary_zero_injective :
    Function.Injective (coboundary mu nu 0) := by
  intro f g hfg
  have hdiff : coboundary mu nu 0 (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  have hdeltaZero :
      pointCoboundary
          ((f - g : L0 (FinTuple X 0 × Z) ((tupleMeasure mu 0).prod nu)) :
            FinTuple X 0 × Z → ℝ)
        =ᵐ[((tupleMeasure mu 1).prod nu)] 0 := by
    have hrep := coe_coboundary mu nu (f - g)
    have hzero :
        ((coboundary mu nu 0 (f - g) :
            L0 (FinTuple X 1 × Z) ((tupleMeasure mu 1).prod nu)) :
              FinTuple X 1 × Z → ℝ)
          =ᵐ[((tupleMeasure mu 1).prod nu)] 0 := by
      rw [hdiff]
      exact AEEqFun.coeFn_zero
    exact hrep.symm.trans hzero
  let e := splitFirst (X := X) (Z := Z) 0
  have he : MeasurePreserving e
      ((tupleMeasure mu 1).prod nu)
      (mu.prod ((tupleMeasure mu 0).prod nu)) :=
    measurePreserving_splitFirst mu nu 0
  have hpull := he.symm.quasiMeasurePreserving.ae hdeltaZero
  have hcurry := Measure.ae_ae_of_ae_prod hpull
  obtain ⟨y, hy⟩ := hcurry.exists
  have hdiffZero :
      ((f - g : L0 (FinTuple X 0 × Z) ((tupleMeasure mu 0).prod nu)) :
          FinTuple X 0 × Z → ℝ)
        =ᵐ[((tupleMeasure mu 0).prod nu)] 0 := by
    filter_upwards [hy] with w hw
    rcases w with ⟨x, z⟩
    have hw' : pointCoboundary
        ((f - g : L0 (FinTuple X 0 × Z) ((tupleMeasure mu 0).prod nu)) :
          FinTuple X 0 × Z → ℝ) (Fin.cons y x, z) = 0 := by
      simpa [e] using hw
    simpa [pointCoboundary, parameterFace] using hw'
  have hsub : f - g = 0 := by
    apply AEEqFun.ext
    exact hdiffZero.trans AEEqFun.coeFn_zero.symm
  exact sub_eq_zero.mp hsub

end
end MeasurableRows
end Sp4
