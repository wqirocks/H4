import Sp4.Measure.NaturalProjectiveOrbit
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Haar-product measures on generic projective configurations

The effective projective group acts freely on every generic configuration of
at least four points.  The global orbit charts proved in
`ProjectiveCoordinates` therefore identify the four-, five-, and six-point
configuration spaces with `PSp(4,ℂ) × Uₙ`.

This file puts the natural Haar measure on the group factor, transports the
product measures through those charts, and proves that the effective action is
measure preserving.  Thus the measurable action complex used below is an
actual `L⁰`/`L∞` complex, not a space of chosen representatives.
-/

namespace Sp4
namespace ProjectiveAction

noncomputable section

open MeasureTheory OrbitChain Pfaffian

/-! ## The effective lcsc group and its Haar measure -/

/-- A fixed left Haar measure on `PSp(4,ℂ)`. -/
noncomputable abbrev effectiveHaar : Measure EffectiveSymplecticGroup :=
  MeasureTheory.Measure.haar

/-! ## Transported configuration measures -/

/-- Haar times the chosen Pfaffian probability, transported to generic
four-point configurations. -/
def measureGeneric4 : Measure (GenericConfig 4) :=
  Measure.map orbitProductMeasurableEquiv4 (effectiveHaar.prod measureU4)

/-- Haar times the chosen Pfaffian probability, transported to generic
five-point configurations. -/
def measureGeneric5 : Measure (GenericConfig 5) :=
  Measure.map orbitProductMeasurableEquiv5 (effectiveHaar.prod measureU5)

/-- Haar times the chosen Pfaffian probability, transported to generic
six-point configurations. -/
def measureGeneric6 : Measure (GenericConfig 6) :=
  Measure.map orbitProductMeasurableEquiv6 (effectiveHaar.prod measureU6)

theorem orbitProductMeasurePreserving4 :
    MeasurePreserving orbitProductMeasurableEquiv4
      (effectiveHaar.prod measureU4) measureGeneric4 :=
  ⟨orbitProductMeasurableEquiv4.measurable, rfl⟩

theorem orbitProductMeasurePreserving5 :
    MeasurePreserving orbitProductMeasurableEquiv5
      (effectiveHaar.prod measureU5) measureGeneric5 :=
  ⟨orbitProductMeasurableEquiv5.measurable, rfl⟩

theorem orbitProductMeasurePreserving6 :
    MeasurePreserving orbitProductMeasurableEquiv6
      (effectiveHaar.prod measureU6) measureGeneric6 :=
  ⟨orbitProductMeasurableEquiv6.measurable, rfl⟩

theorem orbitProductMeasurePreserving4_symm :
    MeasurePreserving orbitProductMeasurableEquiv4.symm measureGeneric4
      (effectiveHaar.prod measureU4) :=
  ⟨orbitProductMeasurableEquiv4.symm.measurable, by
    simp [measureGeneric4]⟩

theorem orbitProductMeasurePreserving5_symm :
    MeasurePreserving orbitProductMeasurableEquiv5.symm measureGeneric5
      (effectiveHaar.prod measureU5) :=
  ⟨orbitProductMeasurableEquiv5.symm.measurable, by
    simp [measureGeneric5]⟩

theorem orbitProductMeasurePreserving6_symm :
    MeasurePreserving orbitProductMeasurableEquiv6.symm measureGeneric6
      (effectiveHaar.prod measureU6) :=
  ⟨orbitProductMeasurableEquiv6.symm.measurable, by
    simp [measureGeneric6]⟩

@[simp] theorem orbitProductMeasurableEquiv4_symm_snd
    (x : GenericConfig 4) :
    (orbitProductEquiv4.symm x).2 = orbitCoord4 x := by
  let p := orbitProductEquiv4.symm x
  calc
    p.2 = orbitCoord4 (orbitProductEquiv4 p) :=
      (orbitCoord4_orbitProductEquiv4 p.1 p.2).symm
    _ = orbitCoord4 x := congrArg orbitCoord4
      (orbitProductEquiv4.apply_symm_apply x)

@[simp] theorem orbitProductMeasurableEquiv5_symm_snd
    (x : GenericConfig 5) :
    (orbitProductEquiv5.symm x).2 = orbitCoord5 x := by
  let p := orbitProductEquiv5.symm x
  calc
    p.2 = orbitCoord5 (orbitProductEquiv5 p) :=
      (orbitCoord5_orbitProductEquiv5 p.1 p.2).symm
    _ = orbitCoord5 x := congrArg orbitCoord5
      (orbitProductEquiv5.apply_symm_apply x)

@[simp] theorem orbitProductMeasurableEquiv6_symm_snd
    (x : GenericConfig 6) :
    (orbitProductEquiv6.symm x).2 = orbitCoord6 x := by
  let p := orbitProductEquiv6.symm x
  calc
    p.2 = orbitCoord6 (orbitProductEquiv6 p) :=
      (orbitCoord6_orbitProductEquiv6 p.1 p.2).symm
    _ = orbitCoord6 x := congrArg orbitCoord6
      (orbitProductEquiv6.apply_symm_apply x)

/-- The orbit coordinate is nonsingular for the transported four-point
measure. -/
theorem orbitCoord4_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving orbitCoord4 measureGeneric4 measureU4 := by
  convert ((Measure.quasiMeasurePreserving_snd
      (μ := effectiveHaar) (ν := measureU4)).comp
    orbitProductMeasurePreserving4_symm.quasiMeasurePreserving) using 1
  funext x
  exact (orbitProductMeasurableEquiv4_symm_snd x).symm

/-- The orbit coordinate is nonsingular for the transported five-point
measure. -/
theorem orbitCoord5_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving orbitCoord5 measureGeneric5 measureU5 := by
  convert ((Measure.quasiMeasurePreserving_snd
      (μ := effectiveHaar) (ν := measureU5)).comp
    orbitProductMeasurePreserving5_symm.quasiMeasurePreserving) using 1
  funext x
  exact (orbitProductMeasurableEquiv5_symm_snd x).symm

/-- The orbit coordinate is nonsingular for the transported six-point
measure. -/
theorem orbitCoord6_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving orbitCoord6 measureGeneric6 measureU6 := by
  convert ((Measure.quasiMeasurePreserving_snd
      (μ := effectiveHaar) (ν := measureU6)).comp
    orbitProductMeasurePreserving6_symm.quasiMeasurePreserving) using 1
  funext x
  exact (orbitProductMeasurableEquiv6_symm_snd x).symm

/-! ## Invariance of the transported measures -/

@[simp] theorem effective_smul_orbitProductEquiv4
    (a g : EffectiveSymplecticGroup) (q : U4) :
    a • orbitProductEquiv4 (g, q) = orbitProductEquiv4 (a * g, q) := by
  rw [orbitProductEquiv4_apply, orbitProductEquiv4_apply, mul_smul]

@[simp] theorem effective_smul_orbitProductEquiv5
    (a g : EffectiveSymplecticGroup) (q : U5) :
    a • orbitProductEquiv5 (g, q) = orbitProductEquiv5 (a * g, q) := by
  rw [orbitProductEquiv5_apply, orbitProductEquiv5_apply, mul_smul]

@[simp] theorem effective_smul_orbitProductEquiv6
    (a g : EffectiveSymplecticGroup) (q : U6) :
    a • orbitProductEquiv6 (g, q) = orbitProductEquiv6 (a * g, q) := by
  rw [orbitProductEquiv6_apply, orbitProductEquiv6_apply, mul_smul]

@[simp] theorem orbitCoord4_effective_smul
    (a : EffectiveSymplecticGroup) (x : GenericConfig 4) :
    orbitCoord4 (a • x) = orbitCoord4 x := by
  induction a using Quotient.inductionOn' with
  | _ g =>
      change orbitCoord4 (smulGeneric g x) = orbitCoord4 x
      exact orbitCoord4_smulGeneric g x

@[simp] theorem orbitCoord5_effective_smul
    (a : EffectiveSymplecticGroup) (x : GenericConfig 5) :
    orbitCoord5 (a • x) = orbitCoord5 x := by
  induction a using Quotient.inductionOn' with
  | _ g =>
      change orbitCoord5 (smulGeneric g x) = orbitCoord5 x
      exact orbitCoord5_smulGeneric g x

@[simp] theorem orbitCoord6_effective_smul
    (a : EffectiveSymplecticGroup) (x : GenericConfig 6) :
    orbitCoord6 (a • x) = orbitCoord6 x := by
  induction a using Quotient.inductionOn' with
  | _ g =>
      change orbitCoord6 (smulGeneric g x) = orbitCoord6 x
      exact orbitCoord6_smulGeneric g x

theorem measurePreserving_leftProduct4 (a : EffectiveSymplecticGroup) :
    MeasurePreserving (fun p : EffectiveSymplecticGroup × U4 =>
      (a * p.1, p.2))
      (effectiveHaar.prod measureU4) (effectiveHaar.prod measureU4) := by
  exact (measurePreserving_mul_left effectiveHaar a).prod
    (MeasurePreserving.id measureU4)

theorem measurePreserving_leftProduct5 (a : EffectiveSymplecticGroup) :
    MeasurePreserving (fun p : EffectiveSymplecticGroup × U5 =>
      (a * p.1, p.2))
      (effectiveHaar.prod measureU5) (effectiveHaar.prod measureU5) := by
  exact (measurePreserving_mul_left effectiveHaar a).prod
    (MeasurePreserving.id measureU5)

theorem measurePreserving_leftProduct6 (a : EffectiveSymplecticGroup) :
    MeasurePreserving (fun p : EffectiveSymplecticGroup × U6 =>
      (a * p.1, p.2))
      (effectiveHaar.prod measureU6) (effectiveHaar.prod measureU6) := by
  exact (measurePreserving_mul_left effectiveHaar a).prod
    (MeasurePreserving.id measureU6)

/-- The effective projective action preserves the four-point measure. -/
theorem measurePreserving_effective_smul4 (a : EffectiveSymplecticGroup) :
    MeasurePreserving (fun x : GenericConfig 4 => a • x)
      measureGeneric4 measureGeneric4 := by
  have h := orbitProductMeasurePreserving4.comp
    ((measurePreserving_leftProduct4 a).comp
      orbitProductMeasurePreserving4_symm)
  convert h using 1
  funext x
  let p := orbitProductEquiv4.symm x
  calc
    a • x = a • orbitProductEquiv4 p := congrArg (fun z => a • z)
      (orbitProductEquiv4.apply_symm_apply x).symm
    _ = orbitProductEquiv4 (a * p.1, p.2) :=
      effective_smul_orbitProductEquiv4 a p.1 p.2

/-- The effective projective action preserves the five-point measure. -/
theorem measurePreserving_effective_smul5 (a : EffectiveSymplecticGroup) :
    MeasurePreserving (fun x : GenericConfig 5 => a • x)
      measureGeneric5 measureGeneric5 := by
  have h := orbitProductMeasurePreserving5.comp
    ((measurePreserving_leftProduct5 a).comp
      orbitProductMeasurePreserving5_symm)
  convert h using 1
  funext x
  let p := orbitProductEquiv5.symm x
  calc
    a • x = a • orbitProductEquiv5 p := congrArg (fun z => a • z)
      (orbitProductEquiv5.apply_symm_apply x).symm
    _ = orbitProductEquiv5 (a * p.1, p.2) :=
      effective_smul_orbitProductEquiv5 a p.1 p.2

/-- The effective projective action preserves the six-point measure. -/
theorem measurePreserving_effective_smul6 (a : EffectiveSymplecticGroup) :
    MeasurePreserving (fun x : GenericConfig 6 => a • x)
      measureGeneric6 measureGeneric6 := by
  have h := orbitProductMeasurePreserving6.comp
    ((measurePreserving_leftProduct6 a).comp
      orbitProductMeasurePreserving6_symm)
  convert h using 1
  funext x
  let p := orbitProductEquiv6.symm x
  calc
    a • x = a • orbitProductEquiv6 p := congrArg (fun z => a • z)
      (orbitProductEquiv6.apply_symm_apply x).symm
    _ = orbitProductEquiv6 (a * p.1, p.2) :=
      effective_smul_orbitProductEquiv6 a p.1 p.2

end
end ProjectiveAction
end Sp4
