import Sp4.Cohomology.DoubleComplex
import Sp4.Cohomology.AffineClass
import Sp4.Cohomology.FiniteGroupContraction
import Sp4.Cohomology.NaturalProjectiveCoordinates
import Sp4.Cohomology.MeasurableDoubleComplex
import Sp4.Cohomology.FirstPageFaces
import Sp4.Cohomology.ParabolicWeights
import Sp4.Measure.ProjectiveProbability

/-!
# Literature interface for the measurable projective resolution

The structure below is deliberately data-rich.  It does not assume that the
ordinary cohomology is two-dimensional or that the horizontal rows are exact.
Instead it supplies the vertical Moore differential, the exact quotient-level
low-degree cohomology facts used by the article, and the two cochain-model
identifications.
`MeasurableDoubleComplex.horizontalExact` proves row exactness by Fubini, and
`transgressionPageHypothesesOfCohomology` unfolds quotient vanishing into actual
coboundary witnesses.  `ordinaryH4Equiv` then invokes the independently
kernel-checked diagram chase in `DoubleComplex.lean`.

The fields are the formal boundary for the following earlier results:

* C. C. Moore, *Group extensions and cohomology for locally compact groups. III*,
  Trans. Amer. Math. Soc. 221 (1976), Theorems 2 and 6;
* T. Austin and C. C. Moore, *Continuity properties of measurable group
  cohomology*, Math. Ann. 356 (2013), Theorem A;
* van Est naturality and the continuous Hochschild--Serre theorem in the exact
  low degrees listed in the source article.

The article-specific input to Hochschild--Serre is not hidden in that boundary:
`ParabolicWeights.lean` proves the concrete unique factorization `Q = U L`,
normality of `U` in the actual line parabolic, the contact bracket, the weights
`r,r,r²`, positivity on every nonzero real exterior degree, invertibility of
`T_r-1`, and combines it with the kernel-checked central-element prism.  Only
the existence, convergence, and edge-map identification of the continuous
Hochschild--Serre spectral sequence remain external.

No affine cocycle, period calculation, boundedness assertion, or final vanishing
statement occurs in the interface.

The finite-stabilizer vanishing used after Moore--Shapiro is not an interface
field: `FiniteGroupCohomology.exists_invariant_primitive` proves it by the
explicit atomic averaging contraction.
-/

namespace Sp4
namespace Pfaffian

noncomputable section

/-- Parameterized measurable Shapiro data for the concrete projective/group
measures carried by a bundled model. -/
abbrev ProjectiveShapiroInterface
    (M : MeasurableDoubleComplex.Model
      ProjectivePoint ProjectiveAction.EffectiveSymplecticGroup) :=
  @MeasurableDoubleComplex.ShapiroNaturalityInterface
    ProjectivePoint ProjectiveAction.EffectiveSymplecticGroup
    inferInstance inferInstance M.projectiveMeasure M.groupMeasure
    M.projectiveProbability M.groupSigmaFinite M.vertical

/-- Literature interface for the vertical Moore calculation and its two endpoint
identifications.  The horizontal differential, its signs, its square-zero law, and
row exactness are all constructed internally from `ambient`. -/
structure ProjectiveResolutionInterface where
  ambient : MeasurableDoubleComplex.Model
    ProjectivePoint ProjectiveAction.EffectiveSymplecticGroup
  projectiveMeasure_eq :
    ambient.projectiveMeasure = ProjectiveProbability.measureProjective
  groupMeasure_eq : ambient.groupMeasure = ProjectiveAction.effectiveHaar
  shapiro : ProjectiveShapiroInterface ambient
  lowStabilizer :
    letI := ambient.projectiveProbability
    letI := ambient.groupSigmaFinite
    shapiro.LowDegreeStabilizerInputs
  finiteColumnH1 : ambient.complex.VerticalH1 4 ≃+
    FiniteGroupCohomology.HSucc
      (K := Unit) (V := L0 U4 measureU4) 0
  /-- Moore's degree-zero identification, followed only by restriction from
  full projective powers to their conull generic strata.  Its target uses the
  natural projective measure; the article-specific passage to Pfaffian
  coordinates is proved internally in `NaturalProjectiveCoordinates.lean`. -/
  targetNatural : ambient.complex.BottomH5 ≃ₗ[ℝ]
    ProjectiveAction.NaturalActionMeasurableH4

namespace ProjectiveResolutionInterface

/-- The abstract Moore model is based on the concrete Gaussian projective
probability constructed in `ProjectiveProbability.lean`. -/
theorem ae_pair_in_standardOrbit (I : ProjectiveResolutionInterface) :
    ∀ᵐ x ∂MeasurableRows.tupleMeasure I.ambient.projectiveMeasure 2,
      ∃ g : SymplecticGroup,
        g • x = ProjectiveStabilizers.standardPair := by
  rw [I.projectiveMeasure_eq]
  exact ProjectiveProbability.ae_pair_in_standardOrbit

/-- The concrete Gaussian measure likewise gives the standard strong triple
as the conull three-point orbit used by Shapiro. -/
theorem ae_triple_in_standardOrbit (I : ProjectiveResolutionInterface) :
    ∀ᵐ x ∂MeasurableRows.tupleMeasure I.ambient.projectiveMeasure 3,
      ∃ g : SymplecticGroup, g • x = TwoFree.standardTriple := by
  rw [I.projectiveMeasure_eq]
  exact ProjectiveProbability.ae_triple_in_standardOrbit

/-- On every later positive column, the Gaussian-conull generic locus has
central symplectic stabilizer (and hence trivial effective stabilizer). -/
theorem ae_generic_stabilizer_is_center (I : ProjectiveResolutionInterface)
    (n : ℕ) :
    ∀ᵐ x ∂MeasurableRows.tupleMeasure I.ambient.projectiveMeasure (4 + n),
      ∀ g : SymplecticGroup, g • x = x →
        g = 1 ∨ g = centralNeg := by
  rw [I.projectiveMeasure_eq]
  exact ProjectiveProbability.ae_generic_stabilizer_is_center n

/-- Assemble the page hypotheses from the individual stabilizer calculations.
The signed alternating face formula is a theorem, not an interface field. -/
def lowDegree (I : ProjectiveResolutionInterface) :
    I.ambient.complex.TransgressionCohomologyInputs := by
  letI := I.ambient.projectiveProbability
  letI := I.ambient.groupSigmaFinite
  change (I.ambient.vertical.toDoubleComplex).TransgressionCohomologyInputs
  exact I.shapiro.transgressionCohomologyInputs
    I.ambient.projectiveMeasure I.ambient.groupMeasure I.ambient.vertical
    I.lowStabilizer

/-- The positive-degree column over a generic five-tuple vanishes by
parameterized Shapiro followed by the internally proved finite-group averaging
contraction. -/
theorem nextH1_zero (I : ProjectiveResolutionInterface)
    (x : I.ambient.complex.VerticalH1 4) : x = 0 := by
  apply I.finiteColumnH1.injective
  rw [map_zero]
  exact FiniteGroupCohomology.cohomologySucc_eq_zero
    (K := Unit) (V := L0 U4 measureU4) 0 (I.finiteColumnH1 x)

/-- The vertical primitive used by transgression is constructed from the
intrinsic next-column vanishing; it is not part of the literature interface. -/
noncomputable def lift (I : ProjectiveResolutionInterface) :
    I.ambient.complex.TransgressionLift :=
  I.ambient.complex.transgressionLiftOfNextH1Zero I.nextH1_zero

/-- The left endpoint is no longer interface data: Shapiro, the explicit
triple-stabilizer splitting, and the elementary continuous-character
calculation canonically identify it with the real dual of `ℂ`. -/
noncomputable def source (I : ProjectiveResolutionInterface) :
    (ℂ →ₗ[ℝ] ℝ) ≃ₗ[ℝ] I.ambient.complex.VerticalH1 3 := by
  letI := I.ambient.projectiveProbability
  letI := I.ambient.groupSigmaFinite
  exact ProjectiveStabilizers.tripleCharactersEquivComplexDual.symm |>.trans
    I.lowStabilizer.tripleH1Characters.symm |>.trans
    (I.shapiro.shapiro 3 0).symm

/-- The ordinary cohomology computation.  The middle equivalence is the explicit
low-degree transgression proved in `DoubleComplex.lean`. -/
def ordinaryH4Equiv (I : ProjectiveResolutionInterface) :
    (ℂ →ₗ[ℝ] ℝ) ≃ₗ[ℝ] MeasurableH4 :=
  I.source.trans
    ((I.ambient.complex.singleTransgressionEquiv I.lift
      (I.ambient.complex.singleTransgressionHypothesesOf
        I.ambient.horizontalExact
        (I.ambient.complex.transgressionPageHypothesesOfCohomology
          I.lowDegree))).trans
      (I.targetNatural.trans
        ProjectiveAction.naturalMeasurableH4Equiv.symm))

/-- Since the target has the same finite dimension as the real dual of `ℂ`, the
already-proved injectivity of `Θ` implies surjectivity. -/
theorem theta_surjective (I : ProjectiveResolutionInterface) :
    Function.Surjective theta := by
  let e := I.ordinaryH4Equiv
  let T : (ℂ →ₗ[ℝ] ℝ) →ₗ[ℝ] (ℂ →ₗ[ℝ] ℝ) :=
    e.symm.toLinearMap.comp theta
  have hTinj : Function.Injective T :=
    e.symm.injective.comp theta_injective
  have hTsurj : Function.Surjective T := T.surjective_of_injective hTinj
  intro y
  obtain ⟨x, hx⟩ := hTsurj (e.symm y)
  refine ⟨x, ?_⟩
  apply e.symm.injective
  exact hx

/-- The article's explicit affine cocycle spans ordinary measurable action
cohomology. -/
def thetaEquiv (I : ProjectiveResolutionInterface) :
    (ℂ →ₗ[ℝ] ℝ) ≃ₗ[ℝ] MeasurableH4 :=
  LinearEquiv.ofBijective theta ⟨theta_injective, I.theta_surjective⟩

@[simp]
theorem thetaEquiv_apply (I : ProjectiveResolutionInterface)
    (ell : ℂ →ₗ[ℝ] ℝ) : I.thetaEquiv ell = theta ell :=
  rfl

end ProjectiveResolutionInterface

end
end Pfaffian
end Sp4
