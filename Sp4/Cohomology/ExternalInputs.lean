import Sp4.Measure.SmoothProbability
import Sp4.Measure.SmoothSubmersion
import Sp4.Measure.FibreIntegration
import Sp4.Measure.ProjectiveGaussian
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Prod

/-!
Named interfaces for results proved in earlier literature.

Every declaration in this file is an external theorem rather than one of the
article's original arguments.  Its statement is kept sufficiently general that no
conclusion specific to the article is postulated.
-/

namespace Sp4

open MeasureTheory

noncomputable section

universe u v w

/-- **External input (Struble's metrization theorem).**  Every Hausdorff,
second-countable, locally compact topological group is Polish in its given
topology.

Struble proves the stronger statement that such a group admits a compatible
left-invariant proper metric.  A proper metric is complete, so this gives the
`PolishSpace` conclusion used below for the effective symplectic quotient.

Source: Raimond A. Struble, *Metrics in locally compact groups*, Compositio
Mathematica 28 (1974), no. 3, 217--222, main theorem. -/
axiom polishSpace_of_lcsc_topologicalGroup
    (G : Type u) [Group G] [TopologicalSpace G] [T2Space G]
    [SecondCountableTopology G] [LocallyCompactSpace G]
    [IsTopologicalGroup G] : PolishSpace G

/-- **External input (zero set of a nontrivial analytic function).**  A
nontrivial complex-analytic scalar function on a finite product of finite
complex coordinate spaces has a null zero set for the product standard
Gaussian measure.

The underlying real and imaginary parts are real analytic.  At least one is
not identically zero, and Proposition 0 of Boris S. Mityagin, *The Zero Set of
a Real Analytic Function*, Mathematical Notes 107 (2020), 529--530,
DOI 10.1134/S0001434620030189 (arXiv:1512.07276), says that its zero set has
Lebesgue measure zero.  Standard Gaussian measure has an everywhere positive
Lebesgue density, so the same zero set is Gaussian-null.  This generic
analytic theorem is the only null-locus fact used to prove that the pair,
triple, and higher projective orbit strata are conull. -/
axiom measure_zero_zeroSet_of_nontrivial_complex_analytic_piGaussian
    {ι : Type u} [Fintype ι] (d : ι → ℕ)
    (f : (∀ i, Fin (d i) → ℂ) → ℂ)
    (_hanalytic : AnalyticOnNhd ℂ f Set.univ)
    (_hnontrivial : ∃ x, f x ≠ 0) :
    (Measure.pi fun i ↦ standardComplexGaussianPi (d i))
      {x | f x = 0} = 0

/-- **External input (coarea formula).**  A smooth submersion between nonempty
open subsets of finite-dimensional complex coordinate spaces is nonsingular for
normalized measures having independent Gaussian coordinates.

This is the null-set corollary of the coarea formula: apply the formula to the
preimage of a target null set.  Surjectivity of the derivative makes the normal
Jacobian strictly positive, so that preimage has Lebesgue measure zero.  The
Gaussian coordinate densities are everywhere strictly positive, and restriction
and multiplication by a nonzero normalizing constant preserve null sets.

Source: Herbert Federer, *Geometric Measure Theory*, Grundlehren der
mathematischen Wissenschaften 153, Springer, 1969, Theorem 3.2.22 (general
area--coarea formula).  This exact null-set consequence is the only part used
below. -/
axiom quasiMeasurePreserving_normalizedOpenGaussian_of_submersion
    {E : Type u} {F : Type v}
    [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [BorelSpace F] [CompleteSpace F]
    (muE : Measure E) [IsFiniteMeasure muE] [muE.IsOpenPosMeasure]
    (muF : Measure F) [IsFiniteMeasure muF] [muF.IsOpenPosMeasure]
    (_hmuE : GaussianCoordinatePresentation muE)
    (_hmuF : GaussianCoordinatePresentation muF)
    (s : Set E) (hs : IsOpen s) (hsne : s.Nonempty)
    (t : Set F) (ht : IsOpen t) (htne : t.Nonempty)
    (f : E → F)
    (hfst : ∀ x, x ∈ s → f x ∈ t)
    (hsubmersion : ∀ x, x ∈ s → HasSurjectiveComplexFDerivAt f x) :
    Measure.QuasiMeasurePreserving
      (fun x : s => ⟨f x.1, hfst x.1 x.2⟩)
      (normalizedOpenMeasure muE s hs hsne)
      (normalizedOpenMeasure muF t ht htne)

/-- **External input (the reverse coarea implication for a surjective
submersion).**  Under the same finite-dimensional smooth-positive-density
hypotheses as above, surjectivity makes the target smooth measure absolutely
continuous with respect to the pushforward of the source measure.

Indeed, the submersion normal form identifies a neighborhood of every target
point with a product projection.  Fubini shows that a positive-measure target
set has positive-measure inverse image in any such chart; second countability
reduces to countably many charts.  Equivalently, this is the positivity half of
the coarea formula.

Source: Herbert Federer, *Geometric Measure Theory*, Grundlehren der
mathematischen Wissenschaften 153, Springer, 1969, Theorem 3.2.22
(area--coarea formula), together with the ordinary submersion normal-form
theorem. -/
axiom absolutelyContinuous_map_normalizedOpenGaussian_of_surjective_submersion
    {E : Type u} {F : Type v}
    [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [BorelSpace F] [CompleteSpace F]
    (muE : Measure E) [IsFiniteMeasure muE] [muE.IsOpenPosMeasure]
    (muF : Measure F) [IsFiniteMeasure muF] [muF.IsOpenPosMeasure]
    (_hmuE : GaussianCoordinatePresentation muE)
    (_hmuF : GaussianCoordinatePresentation muF)
    (s : Set E) (hs : IsOpen s) (hsne : s.Nonempty)
    (t : Set F) (ht : IsOpen t) (htne : t.Nonempty)
    (f : E → F)
    (hfst : ∀ x, x ∈ s → f x ∈ t)
    (_hsurjective : Function.Surjective
      (fun x : s => (⟨f x.1, hfst x.1 x.2⟩ : t)))
    (hsubmersion : ∀ x, x ∈ s → HasSurjectiveComplexFDerivAt f x) :
    normalizedOpenMeasure muF t ht htne ≪
      Measure.map (fun x : s => (⟨f x.1, hfst x.1 x.2⟩ : t))
        (normalizedOpenMeasure muE s hs hsne)

/-- **External input (projective change of variables).**  Every invertible
complex-linear transformation of `ℂ⁴` preserves the null sets of the smooth
measure class on complex projective three-space.  Here that class is
represented concretely by the pushforward of a nondegenerate Gaussian through
one affine chart; the omitted projective hyperplane is smooth-null.

This is the ordinary finite-dimensional change-of-variables theorem applied
in projective affine charts.  The transformation and its inverse are smooth,
so both directions of absolute continuity follow from the area formula.

Source: Herbert Federer, *Geometric Measure Theory*, Grundlehren der
mathematischen Wissenschaften 153, Springer, 1969, Theorem 3.2.22
(area--coarea formula; equal-dimensional change of variables). -/
axiom projectiveGaussian_linearEquiv_quasiMeasurePreserving
    (g : SymplecticVector ≃ₗ[ℂ] SymplecticVector) :
    Measure.QuasiMeasurePreserving
      (fun p : ProjectivePoint => g • p)
      ProjectiveGaussian.measureProjective
      ProjectiveGaussian.measureProjective

/-- **External input (Haar-class decomposition along a free product
coordinate).**  Let an lcsc group act on `G × Y` by left translation in the
first coordinate.  A sigma-finite measure class which is quasi-invariant for
that action and whose `Y`-marginal is equivalent to `ν` is exactly the product
of the Haar class with the class of `ν`.

One standard proof averages the given measure against a probability in the
Haar class and applies Tonelli.  On every fibre, the averaged null sets are
the Haar-null sets; the two marginal hypotheses then identify the product
null sets.  The underlying uniqueness of a quasi-invariant class on a
homogeneous space is Bourbaki's theorem below.

Source: N. Bourbaki, *Integration II*, Chapters 7--9, Springer, 2004,
Chapter VII, §2, no. 5, Theorem 1, p. VII.40 (uniqueness of the
quasi-invariant measure class on `G/H`), together with Tonelli's theorem. -/
axiom measure_equivalent_haar_prod_of_left_quasiInvariant
    {G : Type u} {Y : Type v}
    [Group G] [TopologicalSpace G] [T2Space G]
    [SecondCountableTopology G] [LocallyCompactSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace Y]
    (mu : Measure (G × Y)) [SigmaFinite mu]
    (nu : Measure Y) [SigmaFinite nu]
    (_hqi : ∀ a : G, Measure.QuasiMeasurePreserving
      (fun p : G × Y => (a * p.1, p.2)) mu mu)
    (_hmarginal : Measure.map Prod.snd mu ≪ nu)
    (_hmarginal_rev : nu ≪ Measure.map Prod.snd mu) :
    mu ≪ (Measure.haar : Measure G).prod nu ∧
      (Measure.haar : Measure G).prod nu ≪ mu

/-- **External input (properly supported smooth fibre integration).**  A
surjective submersion between open finite-dimensional coordinate manifolds,
together with finitely many maps whose products with the projection are
submersions, admits the concrete `SmoothFibreKernel` package.

The construction is the standard one used in the article: choose local product
charts and compactly supported fibre densities, splice them with a locally finite
partition of unity, and push each density forward by `(projection, nuisance i)`.
The external ingredients are:

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in
  Mathematics 218, Springer, 2013, Theorem 2.23 (existence of smooth partitions
  of unity);
* Alban Jago, *Traces, Fixed Points and Quantization of Symmetric Spaces*, PhD
  thesis, Université catholique de Louvain, 2017, Proposition 1.5.3 (a smooth
  density whose support is proper under a submersion has smooth pushforward).

The conclusion contains only the generic measure-kernel consequences of those
results; it contains no Pfaffian equation or bounded-defect conclusion. -/
axiom exists_smoothFibreKernel_normalizedOpenGaussian_of_submersions
    {E : Type u} {F : Type v} {ι : Type w} [Fintype ι]
    [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [BorelSpace F] [CompleteSpace F]
    (muE : Measure E) [IsFiniteMeasure muE] [muE.IsOpenPosMeasure]
    (muF : Measure F) [IsFiniteMeasure muF] [muF.IsOpenPosMeasure]
    (_hmuE : GaussianCoordinatePresentation muE)
    (_hmuF : GaussianCoordinatePresentation muF)
    (s : Set E) (hs : IsOpen s) (hsne : s.Nonempty)
    (t : Set F) (ht : IsOpen t) (htne : t.Nonempty)
    (projection : s → t) (nuisance : ι → s → t)
    (projectionAmbient : E → F) (nuisanceAmbient : ι → E → F)
    (_hprojection_restrict : ∀ x, (projection x).1 = projectionAmbient x.1)
    (_hnuisance_restrict : ∀ i x, (nuisance i x).1 = nuisanceAmbient i x.1)
    (_hprojection_surjective : Function.Surjective projection)
    (_hprojection_submersion :
      ∀ x, x ∈ s → HasSurjectiveComplexFDerivAt projectionAmbient x)
    (_hcombined_submersion :
      ∀ i x, x ∈ s → HasSurjectiveComplexFDerivAt
        (fun q => (projectionAmbient q, nuisanceAmbient i q)) x) :
    Nonempty (SmoothFibreKernel
      (normalizedOpenMeasure muF t ht htne)
      (normalizedOpenMeasure muE s hs hsne)
      projection nuisance)

end

end Sp4
