import Sp4.Measure.SmoothProbability
import Sp4.Symplectic.Topology

/-!
# An explicit smooth measure-class representative on complex projective space

This small module isolates the concrete affine-chart Gaussian used throughout
the project.  It is deliberately independent of all external measure-class
theorems, so those theorems can refer to this measure without creating an
import cycle.
-/

namespace Sp4.ProjectiveGaussian

open MeasureTheory
open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev AffineCoordinates := Fin 3 → ℂ

def affineVector (z : AffineCoordinates) : SymplecticVector :=
  ![1, z 0, z 1, z 2]

theorem affineVector_ne_zero (z : AffineCoordinates) : affineVector z ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simpa [affineVector] using h0

def affinePoint (z : AffineCoordinates) : ProjectivePoint :=
  Projectivization.mk ℂ (affineVector z) (affineVector_ne_zero z)

theorem measurable_affinePoint : Measurable affinePoint := by
  apply measurable_projectivization_mk
  · apply measurable_pi_lambda
    intro i
    fin_cases i <;> simp [affineVector] <;> measurability

/-- The pushforward of a nondegenerate Gaussian through the standard affine
chart.  Its null sets are exactly the Fubini--Study null sets. -/
def measureProjective : Measure ProjectivePoint :=
  Measure.map affinePoint (standardComplexGaussianPi 3)

instance : IsProbabilityMeasure measureProjective :=
  Measure.isProbabilityMeasure_map measurable_affinePoint.aemeasurable

end

end Sp4.ProjectiveGaussian
