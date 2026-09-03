import Sp4.Cohomology.MeasurableDoubleComplex
import Sp4.Cohomology.Stabilizers
import Sp4.Cohomology.ParabolicWeights

/-!
# Individual first-page faces and the Shapiro restriction formula

The measurable horizontal differential is a signed sum of deletion faces.
This file first descends every individual face through vertical cohomology.
It then proves the first-page formula from a cochain-level Shapiro naturality
interface.  The latter is precisely the earlier Moore--Shapiro theorem; the
signed-sum calculation itself is internal.
-/

namespace Sp4
namespace MeasurableDoubleComplex

open MeasureTheory

noncomputable section

universe uX uG v

variable {X : Type uX} {G : Type uG}
  [MeasurableSpace X] [MeasurableSpace G]
  (muX : Measure X) (muG : Measure G)
  [IsProbabilityMeasure muX] [SigmaFinite muG]

variable (V : VerticalData muX muG)

theorem VerticalData.dh_eq_signed_sum_raw_faces (p q : ℕ) :
    VerticalData.dh muX muG p q =
      (-1 : ℝ) ^ q •
        ∑ i : Fin (p + 1), (-1 : ℝ) ^ i.val •
          MeasurableRows.face muX
            (MeasurableRows.tupleMeasure muG q) p i := by
  unfold VerticalData.dh
  rw [MeasurableRows.coboundary_eq_sum_faces]

/-- One projective deletion face restricted to vertical cocycles. -/
def VerticalData.verticalFaceCocycles (p q : ℕ) (i : Fin (p + 1)) :
    (V.toDoubleComplex).VerticalCocycles p (q + 1) →ₗ[ℝ]
      (V.toDoubleComplex).VerticalCocycles (p + 1) (q + 1) where
  toFun x := by
    let x0 : Cochain muX muG p (q + 1) := x.1
    have hx0 : V.dv p (q + 1) x0 = 0 := x.2
    refine ⟨MeasurableRows.face muX
      (MeasurableRows.tupleMeasure muG (q + 1)) p i x0, ?_⟩
    change V.dv (p + 1) (q + 1)
      (MeasurableRows.face muX
        (MeasurableRows.tupleMeasure muG (q + 1)) p i x0) = 0
    rw [V.commutesFace, hx0, map_zero]
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul _ _ _

/-- A deletion face sends vertical boundaries to vertical boundaries. -/
theorem VerticalData.verticalFaceCocycles_maps_boundaries
    (p q : ℕ) (i : Fin (p + 1)) :
    (V.toDoubleComplex).VerticalBoundariesSucc p q ≤
      ((V.toDoubleComplex).VerticalBoundariesSucc (p + 1) q).comap
        (V.verticalFaceCocycles muX muG p q i) := by
  intro x hx
  let x0 : Cochain muX muG p (q + 1) := x.1
  change x0 ∈ LinearMap.range (V.dv p q) at hx
  rcases hx with ⟨y, hy⟩
  change V.dv p q y = x0 at hy
  change (V.verticalFaceCocycles muX muG p q i x).1 ∈
    LinearMap.range (V.dv (p + 1) q)
  change MeasurableRows.face muX
      (MeasurableRows.tupleMeasure muG (q + 1)) p i x0 ∈
    LinearMap.range (V.dv (p + 1) q)
  refine ⟨MeasurableRows.face muX
    (MeasurableRows.tupleMeasure muG q) p i y, ?_⟩
  rw [V.commutesFace, hy]

/-- The map induced by one deletion face on positive vertical cohomology. -/
def VerticalData.verticalFace (p q : ℕ) (i : Fin (p + 1)) :
    (V.toDoubleComplex).VerticalHSucc p q →ₗ[ℝ]
      (V.toDoubleComplex).VerticalHSucc (p + 1) q :=
  ((V.toDoubleComplex).VerticalBoundariesSucc p q).mapQ
    ((V.toDoubleComplex).VerticalBoundariesSucc (p + 1) q)
    (V.verticalFaceCocycles muX muG p q i)
    (V.verticalFaceCocycles_maps_boundaries muX muG p q i)

@[simp]
theorem VerticalData.verticalFace_mk (p q : ℕ) (i : Fin (p + 1))
    (x : (V.toDoubleComplex).VerticalCocycles p (q + 1)) :
    V.verticalFace muX muG p q i (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (V.verticalFaceCocycles muX muG p q i x) :=
  rfl

/-- Before Shapiro, the first-page horizontal map is the signed sum of the
individual face maps.  Here `q + 1` is the actual vertical cohomological
degree, hence the global sign `(-1)^(q+1)`. -/
theorem VerticalData.verticalHorizontal_eq_signed_sum_faces (p q : ℕ) :
    (V.toDoubleComplex).verticalHorizontal p q =
      (-1 : ℝ) ^ (q + 1) •
        ∑ i : Fin (p + 1), (-1 : ℝ) ^ i.val •
          V.verticalFace muX muG p q i := by
  apply LinearMap.ext
  intro a
  obtain ⟨x, rfl⟩ :=
    ((V.toDoubleComplex).VerticalBoundariesSucc p q).mkQ_surjective a
  change (V.toDoubleComplex).verticalHorizontal p q
      (Submodule.Quotient.mk x) = _
  rw [(V.toDoubleComplex).verticalHorizontal_mk]
  change Submodule.Quotient.mk
      ((V.toDoubleComplex).verticalHorizontalCocycles p q x) = _
  rw [show (V.toDoubleComplex).verticalHorizontalCocycles p q x =
      (-1 : ℝ) ^ (q + 1) •
        ∑ i : Fin (p + 1), (-1 : ℝ) ^ i.val •
          V.verticalFaceCocycles muX muG p q i x by
    apply Subtype.ext
    let x0 : Cochain muX muG p (q + 1) := x.1
    change VerticalData.dh muX muG p (q + 1) x0 = _
    rw [VerticalData.dh_eq_signed_sum_raw_faces]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_smul, Submodule.coe_sum]
    rfl]
  change ((V.toDoubleComplex).VerticalBoundariesSucc (p + 1) q).mkQ
      ((-1 : ℝ) ^ (q + 1) •
        ∑ i : Fin (p + 1), (-1 : ℝ) ^ i.val •
          V.verticalFaceCocycles muX muG p q i x) = _
  rw [map_smul, map_sum]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul]
  congr 1

/-! ## Moore--Shapiro naturality boundary -/

/-- The exact data supplied by parameterized measurable Shapiro and its
naturality.  `stabilizerH p q` is the degree-`q+1` measurable cohomology of
the stabilizer of the chosen base `p`-tuple.  Naturality is stated separately
for every deletion face; no alternating-sum conclusion is assumed. -/
structure ShapiroNaturalityInterface where
  stabilizerH : ℕ → ℕ → ModuleCat.{v} ℝ
  shapiro : ∀ p q,
    (V.toDoubleComplex).VerticalHSucc p q ≃ₗ[ℝ] stabilizerH p q
  restriction : ∀ p q (i : Fin (p + 1)),
    stabilizerH p q →ₗ[ℝ] stabilizerH (p + 1) q
  naturality : ∀ p q (i : Fin (p + 1)) x,
    shapiro (p + 1) q (V.verticalFace muX muG p q i x) =
      restriction p q i (shapiro p q x)

namespace ShapiroNaturalityInterface

variable (S : ShapiroNaturalityInterface muX muG V)

/-- Under measurable Shapiro, the horizontal first-page differential is the
global bicomplex sign times the alternating sum of stabilizer restrictions. -/
theorem firstPage_face_formula (p q : ℕ)
    (x : (V.toDoubleComplex).VerticalHSucc p q) :
    S.shapiro (p + 1) q
        ((V.toDoubleComplex).verticalHorizontal p q x) =
      (-1 : ℝ) ^ (q + 1) •
        ∑ i : Fin (p + 1), (-1 : ℝ) ^ i.val •
          S.restriction p q i (S.shapiro p q x) := by
  rw [V.verticalHorizontal_eq_signed_sum_faces muX muG]
  simp only [LinearMap.smul_apply, LinearEquiv.map_smul,
    LinearMap.sum_apply, map_sum, S.naturality]

/-- In the first column there is one face, so the first-page map is the
corresponding stabilizer restriction with only the global bicomplex sign. -/
theorem firstPage_zero_formula (q : ℕ)
    (x : (V.toDoubleComplex).VerticalHSucc 0 q) :
    S.shapiro 1 q ((V.toDoubleComplex).verticalHorizontal 0 q x) =
      (-1 : ℝ) ^ (q + 1) •
        S.restriction 0 q (0 : Fin 1) (S.shapiro 0 q x) := by
  simpa [Fin.sum_univ_succ] using
    S.firstPage_face_formula muX muG V 0 q x

/-! ## The exact low-degree stabilizer inputs -/

/-- Earlier-literature cohomology facts after the Shapiro identifications.

The vanishing groups and degree-three restriction are the literature-level
continuous-cohomology inputs.  In degree one the interface supplies the
standard identifications `H¹(L) ≅ ℝ` and `H¹(H) ≅ Hom_cont(H,ℝ)`,
together with their ordinary restriction naturality.  The three pulled-back
characters themselves are *not* assumed to vanish: their exact split
coordinates and logarithmic-modulus calculation are proved in
`Stabilizers.lean`. -/
structure LowDegreeStabilizerInputs where
  /-- The restriction `H_c^3(Sp(4,ℂ)) → H_c^3(Q)` is an isomorphism.
  After the parabolic inflation isomorphism below, van Est naturality
  identifies it with pullback
  `H^3(Sp(2)) → H^3(U(1) × Sp(1))`.  This is an isomorphism by the
  fibration `Sp(1) → Sp(2) → S^7` and Künneth.

  Sources: Borel--Wallach, Chapter II (van Est and naturality), and
  M. Mimura--H. Toda, *Topology of Lie Groups, I and II*, Translations of
  Mathematical Monographs 91, AMS, 1991 (the compact symplectic fibration
  and cohomology). -/
  restrictionH3_bijective :
    Function.Bijective (S.restriction 0 2 (0 : Fin 1))
  /-- The degree-two inverse to parabolic inflation, supplied by the
  continuous Hochschild--Serre edge isomorphism for `Q = L ⋉ U`.
  Source: G. Hochschild and G. D. Mostow, *Cohomology of Lie groups*,
  Illinois J. Math. 6 (1962), 367--401, together with A. Borel and
  N. Wallach, *Continuous Cohomology, Discrete Subgroups, and
  Representations of Reductive Groups*, 2nd ed. (2000), Chapter II.  Its
  semidirect-product and positive-row hypotheses are discharged internally:
  `LineParabolicWeightCertificate` contains the concrete unique
  Heisenberg--Levi factorization, normality of the nilradical, and the contact
  weights used by
  `ParabolicWeights.continuousCohomology_eq_zero_of_contact_weights`.  Only
  the spectral-sequence and edge-map machinery is represented by this field. -/
  parabolicRestrictionH2_of_weightCertificate :
    ParabolicWeights.LineParabolicWeightCertificate →
      Function.Bijective (S.restriction 1 1 (0 : Fin 2))
  /-- `H_c^2(L;ℝ)=0` for
  `L ≅ ℂˣ × SL(2,ℂ)`.  This follows either from van Est and the compact-dual
  calculation or from the product formula together with the standard
  degree-one/degree-three generators.

  Sources: Borel--Wallach, Chapter II, and Mimura--Toda, loc. cit. -/
  H2L_zero : ∀ x : S.stabilizerH 2 1, x = 0
  /-- `H_c^4(Sp(4,ℂ);ℝ)=0`.  Van Est identifies this with degree four of
  the compact dual `Sp(2)`, whose real cohomology is exterior on generators
  in degrees three and seven.

  Sources: Borel--Wallach, Chapter II, and Mimura--Toda, loc. cit. -/
  H4G_zero : ∀ x : S.stabilizerH 0 3, x = 0
  /-- The standard natural identification
  `H_c^1(ℂˣ × SL(2,ℂ);ℝ) ≅ ℝ`, with coordinate represented by
  `a ↦ log ‖a‖`.  The concrete pair-stabilizer splitting is proved in
  `Stabilizers.lean`; only the general continuous-cohomology identification
  is external.  Source: Borel--Wallach, Chapters I--II. -/
  pairH1Coordinate : S.stabilizerH 2 0 ≃ₗ[ℝ] ℝ
  /-- The natural degree-one identification
  `H_c^1(H;ℝ) ≅ Hom_cont(H,ℝ)`.  The subsequent reduction of continuous
  characters of the explicit group `H ≅ {±1} × (ℂ,+)` to the real dual of
  `ℂ` is kernel checked in `Stabilizers.lean`.

  Source: the degree-one homogeneous continuous bar complex; see
  Borel--Wallach, Chapter I. -/
  tripleH1Characters : S.stabilizerH 3 0 ≃ₗ[ℝ]
    ProjectiveStabilizers.ContinuousRealCharacters
      ProjectiveStabilizers.TripleStabilizer
  /-- Naturality of the preceding `H_c^1 ≅ Hom_cont` identification for the
  three concrete face homomorphisms.  The homomorphisms, their split
  coordinates, and the functions `tripleFaceLog` are computed internally in
  `Stabilizers.lean`; this field supplies only ordinary functoriality of
  degree-one continuous cohomology.  Source: Borel--Wallach, Chapter I. -/
  faceRestrictionH1_character : ∀ (i : Fin 3)
      (x : S.stabilizerH 2 0)
      (h : ProjectiveStabilizers.TripleStabilizer),
    (tripleH1Characters (S.restriction 2 0 i x)).1 h =
      pairH1Coordinate x * ProjectiveStabilizers.tripleFaceLog i h

/-- The article's original three-face matrix calculation, combined only with
the standard degree-one character identifications, proves that each face
restriction is zero. -/
theorem LowDegreeStabilizerInputs.faceRestrictionH1_zero
    (P : S.LowDegreeStabilizerInputs) (i : Fin 3) :
    S.restriction 2 0 i = 0 := by
  apply LinearMap.ext
  intro x
  apply P.tripleH1Characters.injective
  rw [LinearMap.zero_apply, map_zero]
  apply Subtype.ext
  apply ContinuousMap.ext
  intro h
  rw [P.faceRestrictionH1_character]
  simp

/-- The quotient-level page hypotheses follow from the individual stabilizer
calculations and the internally proved signed face formula. -/
theorem transgressionCohomologyInputs
    (P : S.LowDegreeStabilizerInputs) :
    (V.toDoubleComplex).TransgressionCohomologyInputs where
  restrictionH3_bijective := by
    constructor
    · intro x y hxy
      apply (S.shapiro 0 2).injective
      apply P.restrictionH3_bijective.1
      have h := congrArg (S.shapiro 1 2) hxy
      rw [S.firstPage_zero_formula muX muG V 2 x,
        S.firstPage_zero_formula muX muG V 2 y] at h
      norm_num at h
      exact h
    · intro y
      obtain ⟨u, hu⟩ := P.restrictionH3_bijective.2
        (-S.shapiro 1 2 y)
      refine ⟨(S.shapiro 0 2).symm u, ?_⟩
      apply (S.shapiro 1 2).injective
      rw [S.firstPage_zero_formula muX muG V 2]
      simp only [LinearEquiv.apply_symm_apply]
      rw [hu]
      norm_num
  H2Q_zero := by
    intro x
    apply (S.shapiro 1 1).injective
    rw [map_zero]
    apply (P.parabolicRestrictionH2_of_weightCertificate
      ParabolicWeights.concreteLineParabolicWeightCertificate).1
    rw [map_zero]
    exact P.H2L_zero
      (S.restriction 1 1 (0 : Fin 2) (S.shapiro 1 1 x))
  H2L_zero := by
    intro x
    apply (S.shapiro 2 1).injective
    rw [map_zero]
    exact P.H2L_zero (S.shapiro 2 1 x)
  H4G_zero := by
    intro x
    apply (S.shapiro 0 3).injective
    rw [map_zero]
    exact P.H4G_zero (S.shapiro 0 3 x)
  incomingH1_zero := by
    apply LinearMap.ext
    intro x
    apply (S.shapiro 3 0).injective
    rw [LinearMap.zero_apply, map_zero]
    rw [S.firstPage_face_formula muX muG V 2 0 x]
    simp [P.faceRestrictionH1_zero]

end ShapiroNaturalityInterface

end
end MeasurableDoubleComplex
end Sp4
