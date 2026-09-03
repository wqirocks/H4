import Sp4.Chains.Measure
import Sp4.Chains.Normalized

/-!
# Orientation of four-point symplectic orbits

The symplectic orbit of a generic ordered four-tuple is classified by its
normalized coordinate in `U4`.  The remaining finite symmetry is the right
action of `S₄`.  This file develops the orientation character on a regular
finite orbit and records explicit symplectic transport witnesses.
-/

namespace Sp4

open Pfaffian MeasureChain
open scoped BigOperators

namespace OrbitChain

noncomputable section

/-! ## Returning from normalized coordinates to an arbitrary configuration -/

/-- Every generic ordered four-tuple is in the symplectic orbit of the chosen
realization of its normalized Gram coordinate. -/
theorem exists_smul_normalizedConfig4_orbitCoord4
    (x : GenericConfig 4) :
    ∃ g : SymplecticGroup,
      smulGeneric g (normalizedConfig4 (orbitCoord4 x)) = x := by
  let A := projectiveGram x.1
  have hA : IsAdmissibleGram A :=
    generic_projectiveGram_isAdmissible x.2 id Function.injective_id
  obtain ⟨d, hd⟩ := exists_matrix4_chi4_diagonalCongruence
    A hA.skew hA.offDiagonal_ne
  obtain ⟨g, hg⟩ :=
    exists_symplectic_smul_of_lift_gram_diagonalCongruent
      (normalizedRealization4 (orbitCoord4 x)).config x.1
      (normalizedRealization4 (orbitCoord4 x)).generic x.2
      (normalizedRealization4 (orbitCoord4 x)).lift
      (canonicalProjectiveLift x.1)
      id Function.injective_id d (by
        rw [(normalizedRealization4 (orbitCoord4 x)).gram_eq]
        exact hd)
  exact ⟨g, Subtype.ext hg⟩

/-- Equality of normalized four-point coordinates gives an actual
symplectic transport between the ordered configurations. -/
theorem exists_smul_of_orbitCoord4_eq
    (x y : GenericConfig 4) (hxy : orbitCoord4 x = orbitCoord4 y) :
    ∃ g : SymplecticGroup, smulGeneric g x = y := by
  obtain ⟨gx, hgx⟩ := exists_smul_normalizedConfig4_orbitCoord4 x
  obtain ⟨gy, hgy⟩ := exists_smul_normalizedConfig4_orbitCoord4 y
  refine ⟨gy * gx⁻¹, ?_⟩
  rw [← hgx, ← hgy]
  rw [hxy]
  apply Subtype.ext
  simp [smulGeneric, mul_smul]

/-- If the normalized coordinate of `y` is a permuted coordinate of `x`,
then `y` is a symplectic translate of the correspondingly permuted tuple. -/
theorem exists_smul_permute_of_orbitCoord4_eq
    (σ : Equiv.Perm (Fin 4)) (x y : GenericConfig 4)
    (hxy : orbitCoord4 y = permute4 σ (orbitCoord4 x)) :
    ∃ g : SymplecticGroup,
      smulGeneric g (permuteGeneric σ x) = y := by
  apply exists_smul_of_orbitCoord4_eq (permuteGeneric σ x) y
  rw [orbitCoord4_permuteGeneric, hxy]

/-! ## The finite unoriented orbit relation on `U4` -/

/-- Two normalized four-point coordinates are in the same unoriented
`S₄`-orbit. -/
def Coord4Related (q r : U4) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4), permute4 σ q = r

theorem coord4Related_refl (q : U4) : Coord4Related q q := by
  exact ⟨1, permute4_one q⟩

theorem coord4Related_symm {q r : U4} :
    Coord4Related q r → Coord4Related r q := by
  rintro ⟨σ, hσ⟩
  refine ⟨σ⁻¹, ?_⟩
  rw [← hσ, permute4_mul]
  simp

theorem coord4Related_trans {q r t : U4} :
    Coord4Related q r → Coord4Related r t → Coord4Related q t := by
  rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩
  refine ⟨σ * τ, ?_⟩
  rw [← permute4_mul, hσ, hτ]

/-- The setoid of unoriented normalized four-point orbits. -/
def coord4Setoid : Setoid U4 where
  r := Coord4Related
  iseqv := ⟨coord4Related_refl, coord4Related_symm,
    coord4Related_trans⟩

/-- An orbit is orientation-singular if an odd permutation stabilizes one
of its normalized coordinates. -/
def Coord4OrientationSingular (q : U4) : Prop :=
  ∃ σ : Equiv.Perm (Fin 4),
    permute4 σ q = q ∧ permSign ℝ σ = -1

/-- Orientation-regular means that there is no odd stabilizer. -/
def Coord4OrientationRegular (q : U4) : Prop :=
  ¬ Coord4OrientationSingular q

theorem permSign_eq_one_or_neg_one (σ : Equiv.Perm (Fin 4)) :
    permSign ℝ σ = 1 ∨ permSign ℝ σ = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · left
    simp [permSign, h]
  · right
    simp [permSign, h]

@[simp]
theorem permSign_inv_real (σ : Equiv.Perm (Fin 4)) :
    permSign ℝ σ⁻¹ = permSign ℝ σ := by
  simp [permSign, Equiv.Perm.sign_inv]

/-- On a regular orbit the sign of a permutation carrying `q` to `r` is
independent of the chosen permutation. -/
theorem permSign_eq_of_regular
    {q r : U4} (hq : Coord4OrientationRegular q)
    {σ τ : Equiv.Perm (Fin 4)}
    (hσ : permute4 σ q = r) (hτ : permute4 τ q = r) :
    permSign ℝ σ = permSign ℝ τ := by
  by_contra hne
  have hstab : permute4 (σ * τ⁻¹) q = q := by
    calc
      permute4 (σ * τ⁻¹) q = permute4 τ⁻¹ (permute4 σ q) :=
        (permute4_mul σ τ⁻¹ q).symm
      _ = permute4 τ⁻¹ r := by rw [hσ]
      _ = permute4 τ⁻¹ (permute4 τ q) := by rw [hτ]
      _ = permute4 (τ * τ⁻¹) q := permute4_mul τ τ⁻¹ q
      _ = q := by simp
  apply hq
  refine ⟨σ * τ⁻¹, hstab, ?_⟩
  rw [permSign_mul, permSign_inv_real]
  rcases permSign_eq_one_or_neg_one σ with hs | hs <;>
    rcases permSign_eq_one_or_neg_one τ with ht | ht <;>
    simp [hs, ht] at hne ⊢

/-- Regularity is constant along an unoriented coordinate orbit. -/
theorem regular_of_related {q r : U4}
    (hq : Coord4OrientationRegular q) (hqr : Coord4Related q r) :
    Coord4OrientationRegular r := by
  rintro ⟨τ, hτ, hτsign⟩
  rcases hqr with ⟨σ, hσ⟩
  apply hq
  refine ⟨σ * τ * σ⁻¹, ?_, ?_⟩
  · calc
      permute4 (σ * τ * σ⁻¹) q =
          permute4 σ⁻¹ (permute4 τ (permute4 σ q)) := by
            rw [← permute4_mul (σ * τ) σ⁻¹ q,
              ← permute4_mul σ τ q]
      _ = permute4 σ⁻¹ (permute4 τ r) := by rw [hσ]
      _ = permute4 σ⁻¹ r := by rw [hτ]
      _ = permute4 σ⁻¹ (permute4 σ q) := by rw [hσ]
      _ = q := by rw [permute4_mul]; simp
  · rw [permSign_mul, permSign_mul, permSign_inv_real, hτsign]
    have hs := permSign_sq ℝ σ
    linarith

/-- Orientation singularity, like regularity, is constant along an
unoriented coordinate orbit. -/
theorem singular_of_related {q r : U4}
    (hq : Coord4OrientationSingular q) (hqr : Coord4Related q r) :
    Coord4OrientationSingular r := by
  classical
  by_contra hr
  have hrreg : Coord4OrientationRegular r := hr
  have hqreg : Coord4OrientationRegular q :=
    regular_of_related hrreg (coord4Related_symm hqr)
  exact hqreg hq

/-! ## The orientation character of one regular orbit -/

/-- Sign of a coordinate relative to an oriented regular base orbit, and
zero off that orbit.  Sign independence is proved below. -/
def coord4Orientation (q₀ q : U4) : ℝ := by
  classical
  exact if h : Coord4Related q₀ q then
    permSign ℝ (Classical.choose h)
  else 0

theorem coord4Orientation_eq_permSign
    {q₀ q : U4} (hreg : Coord4OrientationRegular q₀)
    {σ : Equiv.Perm (Fin 4)} (hσ : permute4 σ q₀ = q) :
    coord4Orientation q₀ q = permSign ℝ σ := by
  classical
  unfold coord4Orientation
  split
  · rename_i hrel
    exact permSign_eq_of_regular hreg (Classical.choose_spec hrel) hσ
  · rename_i hnot
    exact False.elim (hnot ⟨σ, hσ⟩)

theorem coord4Orientation_eq_zero_of_not_related
    {q₀ q : U4} (h : ¬ Coord4Related q₀ q) :
    coord4Orientation q₀ q = 0 := by
  simp [coord4Orientation, h]

/-- The orientation character transforms by the permutation sign. -/
theorem coord4Orientation_permute
    {q₀ : U4} (hreg : Coord4OrientationRegular q₀)
    (τ : Equiv.Perm (Fin 4)) (q : U4) :
    coord4Orientation q₀ (permute4 τ q) =
      permSign ℝ τ * coord4Orientation q₀ q := by
  classical
  by_cases hq : Coord4Related q₀ q
  · rcases hq with ⟨σ, hσ⟩
    have hστ : permute4 (σ * τ) q₀ = permute4 τ q := by
      rw [← permute4_mul, hσ]
    rw [coord4Orientation_eq_permSign hreg hστ,
      coord4Orientation_eq_permSign hreg hσ, permSign_mul]
    ring
  · have hnot : ¬ Coord4Related q₀ (permute4 τ q) := by
      intro hrel
      apply hq
      exact coord4Related_trans hrel
        ⟨τ⁻¹, by rw [permute4_mul]; simp⟩
    rw [coord4Orientation_eq_zero_of_not_related hq,
      coord4Orientation_eq_zero_of_not_related hnot, mul_zero]

/-- The orientation character is an alternating real function on `U4`. -/
theorem coord4Orientation_isAlternating
    {q₀ : U4} (hreg : Coord4OrientationRegular q₀) :
    IsAlternatingFunction4 (coord4Orientation q₀) := by
  intro σ q
  rw [coord4Orientation_permute hreg]
  rfl

/-- On its own regular orbit the orientation character is always `±1`. -/
theorem coord4Orientation_eq_one_or_neg_one
    {q₀ q : U4} (hreg : Coord4OrientationRegular q₀)
    (hrel : Coord4Related q₀ q) :
    coord4Orientation q₀ q = 1 ∨ coord4Orientation q₀ q = -1 := by
  rcases hrel with ⟨σ, hσ⟩
  rw [coord4Orientation_eq_permSign hreg hσ]
  exact permSign_eq_one_or_neg_one σ

/-- Evaluation on a displayed raw four-chain is the corresponding finite
oriented-coordinate sum. -/
theorem evaluation4_mkQ_sum
    {K : Type*} [Fintype K]
    (f : U4 → ℝ) (hf : IsAlternatingFunction4 f)
    (c : K → ℝ) (x : K → GenericConfig 4) :
    evaluation4 f hf
        ((relations ℝ 4).mkQ
          (∑ k : K, c k • generator (x k))) =
      ∑ k : K, c k * f (orbitCoord4 (x k)) := by
  simp [evaluation4, rawEvaluation4, generator, smul_eq_mul]

/-- Vanishing of a finite orbit chain forces zero signed mass in every
chosen regular unoriented orbit. -/
theorem regular_orbit_balance
    {K : Type*} [Fintype K]
    (q₀ : U4) (hreg : Coord4OrientationRegular q₀)
    (c : K → ℝ) (x : K → GenericConfig 4)
    (hzero :
      (relations ℝ 4).mkQ
        (∑ k : K, c k • generator (x k)) = 0) :
    (∑ k : K,
      c k * coord4Orientation q₀ (orbitCoord4 (x k))) = 0 := by
  have h := congrArg
    (evaluation4 (coord4Orientation q₀)
      (coord4Orientation_isAlternating hreg)) hzero
  rw [evaluation4_mkQ_sum, map_zero] at h
  exact h

/-! ## Finite weighted presentations and their face occurrences -/

/-- A finite displayed five-chain whose coefficients are all nonzero and
whose image in the orbit quotient is a cycle.  Positivity is represented by
the absolute value of `coeff`; its sign is retained separately by the real
coefficient itself. -/
structure WeightedFacetPresentation (I : Type*) [Fintype I] where
  facet : I → GenericConfig 5
  coeff : I → ℝ
  coeff_ne : ∀ s, coeff s ≠ 0
  isCycle : boundary ℝ 4
    (∑ s : I, coeff s • ofConfig (R := ℝ) (facet s)) = 0

namespace WeightedFacetPresentation

variable {I : Type*} [Fintype I]

/-- The finite type of all five face occurrences. -/
abbrev FaceOccurrence (_p : WeightedFacetPresentation I) := I × Fin 5

def faceBase (p : WeightedFacetPresentation I) (o : p.FaceOccurrence) :
    GenericConfig 4 :=
  face o.2 (p.facet o.1)

def faceCoeff (p : WeightedFacetPresentation I) (o : p.FaceOccurrence) : ℝ :=
  p.coeff o.1 * (-1 : ℝ) ^ o.2.val

theorem faceCoeff_ne (p : WeightedFacetPresentation I)
    (o : p.FaceOccurrence) : p.faceCoeff o ≠ 0 := by
  exact mul_ne_zero (p.coeff_ne o.1) (pow_ne_zero _ (by norm_num))

@[simp]
theorem abs_faceCoeff (p : WeightedFacetPresentation I)
    (o : p.FaceOccurrence) : |p.faceCoeff o| = |p.coeff o.1| := by
  rw [faceCoeff, abs_mul, abs_pow, abs_neg, abs_one, one_pow, mul_one]

/-- The raw four-chain consisting of all signed face occurrences. -/
def rawFaces (p : WeightedFacetPresentation I) : Raw ℝ 4 :=
  ∑ o : p.FaceOccurrence, p.faceCoeff o • generator (p.faceBase o)

/-- The cycle hypothesis is exactly the assertion that the signed face
occurrence chain vanishes after projection to orbit coinvariants. -/
theorem mkQ_rawFaces_eq_zero (p : WeightedFacetPresentation I) :
    (relations ℝ 4).mkQ p.rawFaces = 0 := by
  rw [rawFaces]
  simp only [map_sum, map_smul]
  change (∑ o : I × Fin 5,
      p.faceCoeff o • ofConfig (R := ℝ) (p.faceBase o)) = 0
  rw [Fintype.sum_prod_type]
  change (∑ s : I, ∑ i : Fin 5,
      (p.coeff s * (-1 : ℝ) ^ i.val) •
        ofConfig (R := ℝ) (face i (p.facet s))) = 0
  simp_rw [mul_smul, ← Finset.smul_sum]
  simpa [boundary_ofConfig] using p.isCycle

/-- Balance in a regular unoriented face orbit, specialized to the complete
list of face occurrences of a weighted cycle. -/
theorem regular_face_orbit_balance
    (p : WeightedFacetPresentation I)
    (q₀ : U4) (hreg : Coord4OrientationRegular q₀) :
    (∑ o : p.FaceOccurrence,
      p.faceCoeff o *
        coord4Orientation q₀ (orbitCoord4 (p.faceBase o))) = 0 := by
  apply regular_orbit_balance q₀ hreg p.faceCoeff p.faceBase
  exact p.mkQ_rawFaces_eq_zero

end WeightedFacetPresentation

namespace WeightedFacetPresentation

variable {I : Type*} [Fintype I]
variable (p : WeightedFacetPresentation I)

/-- Two face occurrences lie in the same unoriented orbit. -/
def FaceRelated (o o' : p.FaceOccurrence) : Prop :=
  Coord4Related (orbitCoord4 (p.faceBase o))
    (orbitCoord4 (p.faceBase o'))

theorem faceRelated_refl (o : p.FaceOccurrence) : p.FaceRelated o o :=
  coord4Related_refl _

theorem faceRelated_symm {o o' : p.FaceOccurrence} :
    p.FaceRelated o o' → p.FaceRelated o' o :=
  coord4Related_symm

theorem faceRelated_trans {o₁ o₂ o₃ : p.FaceOccurrence} :
    p.FaceRelated o₁ o₂ → p.FaceRelated o₂ o₃ →
      p.FaceRelated o₁ o₃ :=
  coord4Related_trans

def faceSetoid : Setoid p.FaceOccurrence where
  r := p.FaceRelated
  iseqv := ⟨p.faceRelated_refl, p.faceRelated_symm,
    p.faceRelated_trans⟩

/-- The finite set of unoriented face orbits occurring in the presentation. -/
abbrev FaceOrbit := Quotient p.faceSetoid

noncomputable instance faceOrbitFintype : Fintype p.FaceOrbit :=
  Fintype.ofFinite p.FaceOrbit

def orbitClass (o : p.FaceOccurrence) : p.FaceOrbit :=
  Quotient.mk p.faceSetoid o

noncomputable def orbitRepresentative (c : p.FaceOrbit) : p.FaceOccurrence :=
  Quotient.out c

@[simp]
theorem orbitClass_representative (c : p.FaceOrbit) :
    p.orbitClass (p.orbitRepresentative c) = c :=
  Quotient.out_eq c

theorem related_representative_of_class_eq
    {c : p.FaceOrbit} {o : p.FaceOccurrence}
    (ho : p.orbitClass o = c) :
    p.FaceRelated (p.orbitRepresentative c) o := by
  change (p.faceSetoid).r (p.orbitRepresentative c) o
  exact Quotient.exact (show
    p.orbitClass (p.orbitRepresentative c) = p.orbitClass o by
      rw [p.orbitClass_representative, ho])

/-- Regularity of a finite occurrence orbit, measured at its chosen
representative. -/
def FaceOrbitRegular (c : p.FaceOrbit) : Prop :=
  Coord4OrientationRegular
    (orbitCoord4 (p.faceBase (p.orbitRepresentative c)))

def FaceOrbitSingular (c : p.FaceOrbit) : Prop :=
  ¬p.FaceOrbitRegular c

/-- Occurrences belonging to a specified finite face orbit. -/
abbrev OccurrencesIn (c : p.FaceOrbit) :=
  {o : p.FaceOccurrence // p.orbitClass o = c}

noncomputable instance occurrencesInNonempty (c : p.FaceOrbit) :
    Nonempty (p.OccurrencesIn c) :=
  ⟨⟨p.orbitRepresentative c, p.orbitClass_representative c⟩⟩

noncomputable instance occurrencesInFintype (c : p.FaceOrbit) :
    Fintype (p.OccurrencesIn c) := Fintype.ofFinite _

theorem occurrence_related_representative
    {c : p.FaceOrbit} (o : p.OccurrencesIn c) :
    Coord4Related
      (orbitCoord4 (p.faceBase (p.orbitRepresentative c)))
      (orbitCoord4 (p.faceBase o.1)) :=
  p.related_representative_of_class_eq o.2

theorem occurrence_regular {c : p.FaceOrbit}
    (hc : p.FaceOrbitRegular c) (o : p.OccurrencesIn c) :
    Coord4OrientationRegular (orbitCoord4 (p.faceBase o.1)) :=
  regular_of_related hc (p.occurrence_related_representative o)

/-- Every occurrence in a singular finite orbit has an odd stabilizer. -/
theorem occurrence_singular {c : p.FaceOrbit}
    (hc : p.FaceOrbitSingular c) (o : p.OccurrencesIn c) :
    Coord4OrientationSingular (orbitCoord4 (p.faceBase o.1)) := by
  classical
  apply singular_of_related
  · exact Classical.byContradiction (fun hreg ↦ hc hreg)
  · exact p.occurrence_related_representative o

/-- At a singular occurrence an odd coordinate stabilizer is realized by
an actual symplectic self-transport of the ordered face. -/
theorem exists_odd_self_transport {c : p.FaceOrbit}
    (hc : p.FaceOrbitSingular c) (o : p.OccurrencesIn c) :
    ∃ (σ : Equiv.Perm (Fin 4)) (g : SymplecticGroup),
      permSign ℝ σ = -1 ∧
        p.faceBase o.1 =
          smulGeneric g (permuteGeneric σ (p.faceBase o.1)) := by
  obtain ⟨σ, hfix, hsign⟩ := p.occurrence_singular hc o
  obtain ⟨g, hg⟩ := exists_smul_permute_of_orbitCoord4_eq
    σ (p.faceBase o.1) (p.faceBase o.1) hfix.symm
  exact ⟨σ, g, hsign, hg.symm⟩

/-- A coordinate-orbit relation between two actual faces supplies both a
permutation and a concrete symplectic transport. -/
theorem exists_face_transport_of_same_orbit
    {o o' : p.FaceOccurrence} (h : p.FaceRelated o o') :
    ∃ (σ : Equiv.Perm (Fin 4)) (g : SymplecticGroup),
      permute4 σ (orbitCoord4 (p.faceBase o)) =
          orbitCoord4 (p.faceBase o') ∧
        smulGeneric g (permuteGeneric σ (p.faceBase o)) =
          p.faceBase o' := by
  rcases h with ⟨σ, hσ⟩
  obtain ⟨g, hg⟩ := exists_smul_permute_of_orbitCoord4_eq
    σ (p.faceBase o) (p.faceBase o') hσ.symm
  exact ⟨σ, g, hσ, hg⟩

/-! ### Oriented coefficients inside one regular finite orbit -/

def orbitBaseCoord (c : p.FaceOrbit) : U4 :=
  orbitCoord4 (p.faceBase (p.orbitRepresentative c))

def orientedFaceCoeff (c : p.FaceOrbit) (o : p.OccurrencesIn c) : ℝ :=
  p.faceCoeff o.1 *
    coord4Orientation (p.orbitBaseCoord c)
      (orbitCoord4 (p.faceBase o.1))

theorem orientation_occurrence_eq_one_or_neg_one
    {c : p.FaceOrbit} (hc : p.FaceOrbitRegular c)
    (o : p.OccurrencesIn c) :
    coord4Orientation (p.orbitBaseCoord c)
        (orbitCoord4 (p.faceBase o.1)) = 1 ∨
      coord4Orientation (p.orbitBaseCoord c)
        (orbitCoord4 (p.faceBase o.1)) = -1 :=
  coord4Orientation_eq_one_or_neg_one hc
    (p.occurrence_related_representative o)

theorem orientedFaceCoeff_ne
    {c : p.FaceOrbit} (hc : p.FaceOrbitRegular c)
    (o : p.OccurrencesIn c) : p.orientedFaceCoeff c o ≠ 0 := by
  apply mul_ne_zero (p.faceCoeff_ne o.1)
  rcases p.orientation_occurrence_eq_one_or_neg_one hc o with h | h <;>
    simp [h]

@[simp]
theorem abs_orientedFaceCoeff
    {c : p.FaceOrbit} (hc : p.FaceOrbitRegular c)
    (o : p.OccurrencesIn c) :
    |p.orientedFaceCoeff c o| = |p.faceCoeff o.1| := by
  rw [orientedFaceCoeff, abs_mul]
  rcases p.orientation_occurrence_eq_one_or_neg_one hc o with h | h <;>
    simp [h]

theorem not_related_of_orbitClass_ne
    {c : p.FaceOrbit} {o : p.FaceOccurrence}
    (ho : p.orbitClass o ≠ c) :
    ¬Coord4Related (p.orbitBaseCoord c)
      (orbitCoord4 (p.faceBase o)) := by
  intro hrel
  apply ho
  calc
    p.orbitClass o = p.orbitClass (p.orbitRepresentative c) :=
      (Quotient.sound hrel).symm
    _ = c := p.orbitClass_representative c

/-- The global regular-orbit balance reduces to the sum over the occurrences
in that one finite orbit. -/
theorem sum_orientedFaceCoeff_eq_zero
    {c : p.FaceOrbit} (hc : p.FaceOrbitRegular c) :
    (∑ o : p.OccurrencesIn c, p.orientedFaceCoeff c o) = 0 := by
  classical
  let f : p.FaceOccurrence → ℝ := fun o ↦
    p.faceCoeff o * coord4Orientation (p.orbitBaseCoord c)
      (orbitCoord4 (p.faceBase o))
  have hfull : (∑ o : p.FaceOccurrence, f o) = 0 := by
    exact p.regular_face_orbit_balance (p.orbitBaseCoord c) hc
  let s : Finset p.FaceOccurrence :=
    Finset.univ.filter (fun o ↦ p.orbitClass o = c)
  have hsfull : (∑ o ∈ s, f o) = ∑ o : p.FaceOccurrence, f o := by
    apply Finset.sum_subset (by simp [s])
    intro o _ ho
    have hne : p.orbitClass o ≠ c := by simpa [s] using ho
    simp [f, coord4Orientation_eq_zero_of_not_related
      (p.not_related_of_orbitClass_ne hne)]
  have hsubtype : (∑ o ∈ s, f o) =
      ∑ o : p.OccurrencesIn c, f o.1 := by
    apply Finset.sum_subtype s
    intro o
    simp [s]
  change (∑ o : p.OccurrencesIn c, f o.1) = 0
  rw [← hsubtype, hsfull, hfull]

/-- Positive and negative parts of the oriented coefficient list. -/
abbrev PositiveOccurrences (c : p.FaceOrbit) :=
  {o : p.OccurrencesIn c // 0 < p.orientedFaceCoeff c o}

abbrev NegativeOccurrences (c : p.FaceOrbit) :=
  {o : p.OccurrencesIn c // p.orientedFaceCoeff c o < 0}

noncomputable instance positiveOccurrencesFintype (c : p.FaceOrbit) :
    Fintype (p.PositiveOccurrences c) := Fintype.ofFinite _

noncomputable instance negativeOccurrencesFintype (c : p.FaceOrbit) :
    Fintype (p.NegativeOccurrences c) := Fintype.ofFinite _

def positiveWeight {c : p.FaceOrbit} (o : p.PositiveOccurrences c) : ℝ :=
  p.orientedFaceCoeff c o.1

def negativeWeight {c : p.FaceOrbit} (o : p.NegativeOccurrences c) : ℝ :=
  -p.orientedFaceCoeff c o.1

theorem positiveWeight_pos {c : p.FaceOrbit}
    (o : p.PositiveOccurrences c) : 0 < p.positiveWeight o := o.2

theorem negativeWeight_pos {c : p.FaceOrbit}
    (o : p.NegativeOccurrences c) : 0 < p.negativeWeight o := by
  exact neg_pos.mpr o.2

theorem exists_positiveOccurrence
    {c : p.FaceOrbit} (hc : p.FaceOrbitRegular c) :
    Nonempty (p.PositiveOccurrences c) := by
  obtain ⟨o, _, ho⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero
    (fun o : p.OccurrencesIn c ↦ p.orientedFaceCoeff c o)
    (p.sum_orientedFaceCoeff_eq_zero hc)
    ⟨Classical.choice (p.occurrencesInNonempty c), Finset.mem_univ _,
      p.orientedFaceCoeff_ne hc _⟩
  exact ⟨⟨o, ho⟩⟩

theorem exists_negativeOccurrence
    {c : p.FaceOrbit} (hc : p.FaceOrbitRegular c) :
    Nonempty (p.NegativeOccurrences c) := by
  obtain ⟨o, _, ho⟩ := Finset.exists_pos_of_sum_zero_of_exists_nonzero
    (fun o : p.OccurrencesIn c ↦ -p.orientedFaceCoeff c o)
    (by
      have hz := congrArg (fun z : ℝ ↦ -z)
        (p.sum_orientedFaceCoeff_eq_zero hc)
      simpa using hz)
    ⟨Classical.choice (p.occurrencesInNonempty c), Finset.mem_univ _,
      neg_ne_zero.mpr (p.orientedFaceCoeff_ne hc _)⟩
  exact ⟨⟨o, neg_pos.mp ho⟩⟩

/-- Positive and negative oriented masses in a regular orbit agree. -/
theorem regular_positive_negative_mass_eq
    {c : p.FaceOrbit} (hc : p.FaceOrbitRegular c) :
    (∑ o : p.PositiveOccurrences c, p.positiveWeight o) =
      ∑ o : p.NegativeOccurrences c, p.negativeWeight o := by
  classical
  let v : p.OccurrencesIn c → ℝ := p.orientedFaceCoeff c
  let sp : Finset (p.OccurrencesIn c) :=
    Finset.univ.filter (fun o ↦ 0 < v o)
  let sn : Finset (p.OccurrencesIn c) :=
    Finset.univ.filter (fun o ↦ v o < 0)
  have hsp : (∑ o ∈ sp, v o) =
      ∑ o : p.PositiveOccurrences c, v o.1 := by
    apply Finset.sum_subtype sp
    intro o
    simp [sp, v]
  have hsn : (∑ o ∈ sn, v o) =
      ∑ o : p.NegativeOccurrences c, v o.1 := by
    apply Finset.sum_subtype sn
    intro o
    simp [sn, v]
  have hdisj : Disjoint sp sn := by
    apply Finset.disjoint_left.mpr
    intro o hop hon
    have hp : 0 < v o := (Finset.mem_filter.mp hop).2
    have hn : v o < 0 := (Finset.mem_filter.mp hon).2
    linarith
  have hunion : sp ∪ sn = Finset.univ := by
    ext o
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro _
      trivial
    · intro _
      by_cases hpos : 0 < v o
      · left
        simp [sp, hpos]
      · right
        simp only [sn, Finset.mem_filter, Finset.mem_univ, true_and]
        exact lt_of_le_of_ne (not_lt.mp hpos)
          (p.orientedFaceCoeff_ne hc o)
  have hparts :
      (∑ o : p.PositiveOccurrences c, v o.1) +
        ∑ o : p.NegativeOccurrences c, v o.1 =
      ∑ o : p.OccurrencesIn c, v o := by
    rw [← hsp, ← hsn, ← Finset.sum_union hdisj, hunion]
  have hzero :
      (∑ o : p.PositiveOccurrences c, v o.1) +
        ∑ o : p.NegativeOccurrences c, v o.1 = 0 := by
    rw [hparts]
    exact p.sum_orientedFaceCoeff_eq_zero hc
  change (∑ o : p.PositiveOccurrences c, v o.1) =
    ∑ o : p.NegativeOccurrences c, -v o.1
  rw [show (∑ o : p.NegativeOccurrences c, -v o.1) =
      -(∑ o : p.NegativeOccurrences c, v o.1) by simp]
  linarith

end WeightedFacetPresentation

/-! ## The output type of weighted face pairing -/

/-- A finite subdivision of all face occurrences into paired oriented atoms.
The two refinement equations say respectively that coefficients are preserved
and that no absolute mass is lost.  The final three fields are the concrete
orbit transport and its orientation sign. -/
structure WeightedFacePairing {I : Type*} [Fintype I] [DecidableEq I]
    (p : WeightedFacetPresentation I) (A : Type*) [Fintype A] where
  occurrence : A → p.FaceOccurrence
  atomCoeff : A → ℝ
  coeff_refinement : ∀ o,
    (∑ a ∈ Finset.univ.filter (fun a : A ↦ occurrence a = o),
      atomCoeff a) = p.faceCoeff o
  mass_refinement : ∀ o,
    (∑ a ∈ Finset.univ.filter (fun a : A ↦ occurrence a = o),
      |atomCoeff a|) = |p.faceCoeff o|
  mate : Equiv.Perm A
  mate_involutive : ∀ a, mate (mate a) = a
  mate_ne : ∀ a, mate a ≠ a
  group : A → SymplecticGroup
  permutation : A → Equiv.Perm (Fin 4)
  base_transport : ∀ a,
    p.faceBase (occurrence (mate a)) =
      smulGeneric (group a)
        (permuteGeneric (permutation a) (p.faceBase (occurrence a)))
  coeff_transport : ∀ a,
    atomCoeff (mate a) * permSign ℝ (permutation a) = -atomCoeff a

namespace WeightedFacePairing

variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
variable {p : WeightedFacetPresentation I}

def parent (d : WeightedFacePairing p A) (a : A) : I :=
  (d.occurrence a).1

def faceIndex (d : WeightedFacePairing p A) (a : A) : Fin 5 :=
  (d.occurrence a).2

theorem base_transport_symm (d : WeightedFacePairing p A) (a : A) :
    p.faceBase (d.occurrence a) =
      smulGeneric (d.group a)⁻¹
        (permuteGeneric (d.permutation a)⁻¹
          (p.faceBase (d.occurrence (d.mate a)))) := by
  rw [d.base_transport a]
  apply Subtype.ext
  funext i
  simp [smulGeneric, permuteGeneric, FinTuple.permute]

/-! A weighted pairing initially records a valid directed transport at each
endpoint.  For choosing cone apices we need the two transports on a matched
pair to be literal inverses.  We obtain that coherence without imposing any
cycle/holonomy condition: order the two endpoints, use the stored transport
only in the forward direction, and use its inverse in the reverse direction. -/

/-- Canonical orientation of a two-element mate orbit, obtained from the
standard finite enumeration of the atom type. -/
noncomputable def pairForward (d : WeightedFacePairing p A) (a : A) : Prop :=
  (Fintype.equivFin A a).val < (Fintype.equivFin A (d.mate a)).val

theorem pairForward_mate_iff (d : WeightedFacePairing p A) (a : A) :
    d.pairForward (d.mate a) ↔ ¬d.pairForward a := by
  classical
  unfold pairForward
  rw [d.mate_involutive]
  have hne : (Fintype.equivFin A a).val ≠
      (Fintype.equivFin A (d.mate a)).val := by
    intro h
    apply d.mate_ne a
    apply (Fintype.equivFin A).injective
    apply Fin.ext
    exact h.symm
  omega

theorem pairForward_ne_mate (d : WeightedFacePairing p A) (a : A) :
    d.pairForward a ↔ ¬d.pairForward (d.mate a) := by
  rw [d.pairForward_mate_iff]
  tauto

/-- The group component of the coherently oriented pair transport. -/
noncomputable def coherentGroup (d : WeightedFacePairing p A) (a : A) :
    SymplecticGroup := by
  classical
  exact if d.pairForward a then d.group a else (d.group (d.mate a))⁻¹

/-- The permutation component of the coherently oriented pair transport. -/
noncomputable def coherentPermutation (d : WeightedFacePairing p A) (a : A) :
    Equiv.Perm (Fin 4) := by
  classical
  exact if d.pairForward a then d.permutation a
    else (d.permutation (d.mate a))⁻¹

theorem coherentGroup_mate (d : WeightedFacePairing p A) (a : A) :
    d.coherentGroup (d.mate a) = (d.coherentGroup a)⁻¹ := by
  classical
  by_cases h : d.pairForward a
  · have hm : ¬d.pairForward (d.mate a) :=
      (d.pairForward_ne_mate a).mp h
    simp [coherentGroup, h, hm, d.mate_involutive]
  · have hm : d.pairForward (d.mate a) :=
      (d.pairForward_mate_iff a).mpr h
    simp [coherentGroup, h, hm, d.mate_involutive]

theorem coherentPermutation_mate (d : WeightedFacePairing p A) (a : A) :
    d.coherentPermutation (d.mate a) =
      (d.coherentPermutation a)⁻¹ := by
  classical
  by_cases h : d.pairForward a
  · have hm : ¬d.pairForward (d.mate a) :=
      (d.pairForward_ne_mate a).mp h
    simp [coherentPermutation, h, hm, d.mate_involutive]
  · have hm : d.pairForward (d.mate a) :=
      (d.pairForward_mate_iff a).mpr h
    simp [coherentPermutation, h, hm, d.mate_involutive]

theorem coherent_base_transport (d : WeightedFacePairing p A) (a : A) :
    p.faceBase (d.occurrence (d.mate a)) =
      smulGeneric (d.coherentGroup a)
        (permuteGeneric (d.coherentPermutation a)
          (p.faceBase (d.occurrence a))) := by
  classical
  by_cases h : d.pairForward a
  · simpa [coherentGroup, coherentPermutation, h] using d.base_transport a
  · have hs := d.base_transport_symm (d.mate a)
    rw [d.mate_involutive] at hs
    simpa [coherentGroup, coherentPermutation, h] using hs

theorem coherent_coeff_transport (d : WeightedFacePairing p A) (a : A) :
    d.atomCoeff (d.mate a) * permSign ℝ (d.coherentPermutation a) =
      -d.atomCoeff a := by
  classical
  by_cases h : d.pairForward a
  · simpa [coherentPermutation, h] using d.coeff_transport a
  · have ht := d.coeff_transport (d.mate a)
    rw [d.mate_involutive] at ht
    have hs := permSign_sq ℝ (d.permutation (d.mate a))
    rw [coherentPermutation, if_neg h, permSign_inv_real]
    have hcoeff : d.atomCoeff (d.mate a) =
        -(d.atomCoeff a * permSign ℝ (d.permutation (d.mate a))) := by
      linarith
    rw [hcoeff]
    calc
      -(d.atomCoeff a * permSign ℝ (d.permutation (d.mate a))) *
          permSign ℝ (d.permutation (d.mate a)) =
          -d.atomCoeff a *
            (permSign ℝ (d.permutation (d.mate a)) *
              permSign ℝ (d.permutation (d.mate a))) := by ring
      _ = -d.atomCoeff a := by rw [hs]; ring

end WeightedFacePairing

/-! ## A product transportation matrix

For two positive finite lists of equal total mass, the product coupling is a
particularly convenient fully explicit transportation decomposition. -/

def productCoupling {P N : Type*} [Fintype P]
    (wp : P → ℝ) (wn : N → ℝ) (p : P) (n : N) : ℝ :=
  wp p * wn n / ∑ p : P, wp p

theorem sum_productCoupling_row {P N : Type*} [Fintype P] [Fintype N]
    (wp : P → ℝ) (wn : N → ℝ)
    (heq : (∑ p : P, wp p) = ∑ n : N, wn n)
    (hne : (∑ p : P, wp p) ≠ 0) (p : P) :
    (∑ n : N, productCoupling wp wn p n) = wp p := by
  simp_rw [productCoupling]
  rw [← Finset.sum_div, ← Finset.mul_sum, ← heq]
  field_simp

theorem sum_productCoupling_col {P N : Type*} [Fintype P] [Fintype N]
    (wp : P → ℝ) (wn : N → ℝ)
    (hne : (∑ p : P, wp p) ≠ 0) (n : N) :
    (∑ p : P, productCoupling wp wn p n) = wn n := by
  simp_rw [productCoupling]
  rw [← Finset.sum_div, ← Finset.sum_mul]
  field_simp

theorem productCoupling_pos {P N : Type*} [Fintype P] [Nonempty P]
    (wp : P → ℝ) (wn : N → ℝ)
    (hwp : ∀ p, 0 < wp p) (hwn : ∀ n, 0 < wn n)
    (p : P) (n : N) : 0 < productCoupling wp wn p n := by
  unfold productCoupling
  apply div_pos (mul_pos (hwp p) (hwn n))
  exact Finset.sum_pos (fun p _ ↦ hwp p) Finset.univ_nonempty

end

end OrbitChain

end Sp4
