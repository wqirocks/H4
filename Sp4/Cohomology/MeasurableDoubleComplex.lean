import Sp4.Cohomology.DoubleComplex
import Sp4.Cohomology.MeasurableRows

/-!
# The inhomogeneous measurable double complex

The horizontal direction of the Moore projective double complex is completely
formal: after translation descent it is alternating deletion in the projective
variables.  This file packages that concrete row together with arbitrary vertical
Moore differentials.  Only the vertical differential and its compatibility with
deletion remain input; horizontal exactness is proved here by the Fubini contraction
from `MeasurableRows`.
-/

namespace Sp4
namespace MeasurableDoubleComplex

open MeasureTheory

noncomputable section

universe uX uG

variable {X : Type uX} {G : Type uG}
  [MeasurableSpace X] [MeasurableSpace G]
  (muX : Measure X) (muG : Measure G)
  [IsProbabilityMeasure muX] [SigmaFinite muG]

/-- Inhomogeneous measurable cochains with `p` projective variables and `q`
group variables. -/
abbrev Cochain (p q : ℕ) :=
  L0 (FinTuple X p × FinTuple G q)
    ((MeasurableRows.tupleMeasure muX p).prod
      (MeasurableRows.tupleMeasure muG q))

/-- The genuinely external part of the inhomogeneous Moore bicomplex: its vertical
differential, its square-zero identity, and its commutation with deletion.  For the
standard homogeneous/inhomogeneous bar differential these formulas are finite
cochain calculations; keeping the data explicit prevents an appeal to an unnamed
spectral sequence. -/
structure VerticalData where
  dv : ∀ p q, Cochain muX muG p q →ₗ[ℝ] Cochain muX muG p (q + 1)
  dv_sq : ∀ p q x, dv p (q + 1) (dv p q x) = 0
  commutesFace : ∀ p q (i : Fin (p + 1)) x,
    dv (p + 1) q
        (MeasurableRows.face muX
          (MeasurableRows.tupleMeasure muG q) p i x) =
      MeasurableRows.face muX
        (MeasurableRows.tupleMeasure muG (q + 1)) p i (dv p q x)

namespace VerticalData

variable (V : VerticalData muX muG)

/-- The Moore differential commutes with the alternating deletion operator
because it commutes with every individual projective face. -/
theorem commutes (p q : ℕ) (x : Cochain muX muG p q) :
    V.dv (p + 1) q
        (MeasurableRows.coboundary muX
          (MeasurableRows.tupleMeasure muG q) p x) =
      MeasurableRows.coboundary muX
        (MeasurableRows.tupleMeasure muG (q + 1)) p (V.dv p q x) := by
  rw [MeasurableRows.coboundary_eq_sum_faces,
    MeasurableRows.coboundary_eq_sum_faces]
  simp only [LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [LinearMap.smul_apply, map_smul]
  rw [V.commutesFace]

/-- The sign-twisted deletion differential used by the article. -/
def dh (p q : ℕ) : Cochain muX muG p q →ₗ[ℝ] Cochain muX muG (p + 1) q :=
  (-1 : ℝ) ^ q •
    MeasurableRows.coboundary muX
      (MeasurableRows.tupleMeasure muG q) p

/-- The concrete first-quadrant double complex. -/
def toDoubleComplex : FirstQuadrantDoubleComplex ℝ where
  obj p q := ModuleCat.of ℝ (Cochain muX muG p q)
  dv := V.dv
  dh := dh muX muG
  dv_sq := V.dv_sq
  dh_sq := by
    intro p q x
    simp only [dh, LinearMap.smul_apply, map_smul]
    rw [MeasurableRows.coboundary_sq]
    simp
  anticomm := by
    intro p q x
    simp only [dh, LinearMap.smul_apply, map_smul]
    rw [V.commutes]
    rw [pow_succ]
    module

@[simp]
theorem toDoubleComplex_obj (p q : ℕ) :
    V.toDoubleComplex.obj p q = ModuleCat.of ℝ (Cochain muX muG p q) :=
  rfl

@[simp]
theorem toDoubleComplex_dv (p q : ℕ) :
    V.toDoubleComplex.dv p q = V.dv p q :=
  rfl

@[simp]
theorem toDoubleComplex_dh (p q : ℕ) :
    V.toDoubleComplex.dh p q = dh muX muG p q :=
  rfl

/-- Fubini exactness of every horizontal row of the concrete bicomplex. -/
theorem horizontalExact : V.toDoubleComplex.HorizontalExact where
  at_zero := by
    intro q x hx
    have hs : (-1 : ℝ) ^ q ≠ 0 := pow_ne_zero _ (by norm_num)
    have hdelta : MeasurableRows.coboundary muX
        (MeasurableRows.tupleMeasure muG q) 0 x = 0 := by
      change (-1 : ℝ) ^ q •
          MeasurableRows.coboundary muX
            (MeasurableRows.tupleMeasure muG q) 0 x = 0 at hx
      exact (smul_eq_zero.mp hx).resolve_left hs
    apply MeasurableRows.coboundary_zero_injective muX
      (MeasurableRows.tupleMeasure muG q)
    calc
      MeasurableRows.coboundary muX
          (MeasurableRows.tupleMeasure muG q) 0 x = 0 := hdelta
      _ = MeasurableRows.coboundary muX
          (MeasurableRows.tupleMeasure muG q) 0 0 :=
        (map_zero _).symm
  at_succ := by
    intro p q x hx
    let s : ℝ := (-1 : ℝ) ^ q
    have hs : s ≠ 0 := pow_ne_zero _ (by norm_num)
    have hdelta : MeasurableRows.coboundary muX
        (MeasurableRows.tupleMeasure muG q) (p + 1) x = 0 := by
      change s •
          MeasurableRows.coboundary muX
            (MeasurableRows.tupleMeasure muG q) (p + 1) x = 0 at hx
      exact (smul_eq_zero.mp hx).resolve_left hs
    obtain ⟨y, hy⟩ := MeasurableRows.exists_primitive muX
      (MeasurableRows.tupleMeasure muG q) x hdelta
    refine ⟨s⁻¹ • y, ?_⟩
    change s • MeasurableRows.coboundary muX
      (MeasurableRows.tupleMeasure muG q) p (s⁻¹ • y) =
        (x : Cochain muX muG (p + 1) q)
    rw [map_smul, hy]
    exact smul_inv_smul₀ hs x

end VerticalData

/-! ## Bundled models -/

/-- A choice of probability representative on the projective space, a sigma-finite
representative on the group, and the associated vertical Moore differential. -/
structure Model (X : Type uX) (G : Type uG)
    [MeasurableSpace X] [MeasurableSpace G] where
  projectiveMeasure : Measure X
  groupMeasure : Measure G
  projectiveProbability : IsProbabilityMeasure projectiveMeasure
  groupSigmaFinite : SigmaFinite groupMeasure
  vertical : @VerticalData X G _ _ projectiveMeasure groupMeasure
    projectiveProbability groupSigmaFinite

namespace Model

variable {X : Type uX} {G : Type uG}
  [MeasurableSpace X] [MeasurableSpace G]
  (M : Model X G)

/-- The double complex carried by a bundled measurable model. -/
def complex : FirstQuadrantDoubleComplex ℝ := by
  letI := M.projectiveProbability
  letI := M.groupSigmaFinite
  exact M.vertical.toDoubleComplex

/-- Horizontal exactness is a theorem of the bundled model, not supplied data. -/
theorem horizontalExact : M.complex.HorizontalExact := by
  letI := M.projectiveProbability
  letI := M.groupSigmaFinite
  exact M.vertical.horizontalExact

end Model

end
end MeasurableDoubleComplex
end Sp4
