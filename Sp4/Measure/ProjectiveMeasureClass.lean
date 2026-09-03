import Sp4.Measure.GaussianLebesgue
import Sp4.Measure.ProjectiveProbability
import Sp4.Measure.ProjectiveOrbit
import Sp4.Measure.ReferenceSix
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Natural projective and Haar-orbit measure classes

This file proves the measure-class part of the normalized Gram quotient for
four, five, and six generic points.  It compares the product smooth measure
on projective space with the Haar-product measures used by the explicit
Pfaffian action complex.

The project-specific geometry is proved here: simultaneous affine charts,
surjectivity and full-rank differentials of the normalized Gram maps, the
coarea comparison on the parameter spaces, quasi-invariance of the natural
projective measure, and the final orbit-product comparison.  Only the generic
finite-dimensional change-of-variables, coarea, and lcsc Haar-class theorems
declared in `ExternalInputs` are used as literature interfaces.
-/

namespace Sp4
namespace ProjectiveMeasureClass

open MeasureTheory ProbabilityTheory

open scoped LinearAlgebra.Projectivization

theorem inAffineChart_iff_transverse_standardPair_one
    (p : ProjectivePoint) :
    Sp4.ProjectiveProbability.InAffineChart p ↔
      Transverse p (Sp4.ProjectiveStabilizers.standardPair 1) := by
  induction p using Projectivization.ind with
  | h v hv =>
      rw [Sp4.ProjectiveProbability.inAffineChart_mk]
      change v 0 ≠ 0 ↔
        Transverse (Projectivization.mk ℂ v hv)
          (Projectivization.mk ℂ TwoFree.f1 TwoFree.f1_ne_zero)
      rw [transverse_mk_iff]
      simp [omega_apply, TwoFree.f1]

theorem exists_smul_all_inAffineChart {n : ℕ} [Nonempty (Fin n)]
    (x : ProjectiveConfig n) :
    ∃ g : SymplecticGroup, ∀ i,
      Sp4.ProjectiveProbability.InAffineChart ((g • x) i) := by
  let family : Unit → ProjectiveConfig n := fun _ => x
  obtain ⟨y, hy⟩ := Sp4.exists_commonApex family
  let i₀ : Fin n := Classical.choice inferInstance
  let p : ProjectiveConfig 2 := ![x i₀, y]
  have hp : Transverse (p 0) (p 1) := by
    exact (hy.transverse () i₀).symm
  let xy : Sp4.ProjectiveStabilizers.TransversePair := ⟨p, hp⟩
  obtain ⟨g, hg⟩ := Sp4.ProjectiveStabilizers.transversePair_transitive xy
  refine ⟨g, fun i => (inAffineChart_iff_transverse_standardPair_one _).2 ?_⟩
  have hgy : g • y = Sp4.ProjectiveStabilizers.standardPair 1 := by
    have h := congrFun hg 1
    simpa [xy, p] using h
  rw [← hgy]
  change Transverse (g • x i) (g • y)
  rw [transverse_smul_iff]
  exact (hy.transverse () i).symm

open OrbitChain Pfaffian ProjectiveAction

abbrev AffineGeneric (n : ℕ) (h4 : 4 ≤ n) :=
  {z : Fin n → ProjectiveProbability.AffineCoordinates //
    (ProjectiveProbability.affineConfigFamily n h4).Good z}

noncomputable def affineGenericConfig {n : ℕ} {h4 : 4 ≤ n}
    (z : AffineGeneric n h4) : GenericConfig n :=
  ⟨ProjectiveProbability.affineTuple n z.1,
    (ProjectiveProbability.affineConfigFamily n h4).config_generic z.2⟩

theorem exists_affineGenericConfig_eq_smul {n : ℕ} (h4 : 4 ≤ n)
    (x : GenericConfig n) :
    ∃ (z : AffineGeneric n h4) (g : SymplecticGroup),
      affineGenericConfig z = smulGeneric g x := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨g, hg⟩ := exists_smul_all_inAffineChart x.1
  let z := ProjectiveProbability.affineTupleCoord n (g • x.1)
  have hzconfig : ProjectiveProbability.affineTuple n z = g • x.1 := by
    funext i
    exact ProjectiveProbability.affinePoint_affineCoord_of_chart _ (hg i)
  have hzGeneric : IsGeneric (ProjectiveProbability.affineTuple n z) := by
    rw [hzconfig]
    exact x.2.smul g
  have hzGood : (ProjectiveProbability.affineConfigFamily n h4).Good z :=
    (ProjectiveProbability.affineConfigFamily n h4).good_of_projectivized_generic
      (fun i => ProjectiveProbability.affineVector_ne_zero (z i)) hzGeneric
  let z' : AffineGeneric n h4 := ⟨z, hzGood⟩
  refine ⟨z', g, ?_⟩
  apply Subtype.ext
  exact hzconfig

noncomputable def affineGramCoord4
    (z : Fin 4 → ProjectiveProbability.AffineCoordinates) : Coord4 :=
  chi4 (gram (fun i => ProjectiveProbability.affineVector (z i)))


noncomputable def affineGramCoord5
    (z : Fin 5 → ProjectiveProbability.AffineCoordinates) : Coord5 :=
  chi5 (gram (fun i => ProjectiveProbability.affineVector (z i)))

noncomputable def affineGramCoord6
    (z : Fin 6 → ProjectiveProbability.AffineCoordinates) : Coord6 :=
  chi6 (gram (fun i => ProjectiveProbability.affineVector (z i)))

theorem orbitCoord4_affineGenericConfig_val
    (z : AffineGeneric 4 (by norm_num)) :
    (orbitCoord4 (affineGenericConfig z)).1 = affineGramCoord4 z.1 := by
  obtain ⟨d, hd⟩ :=
    (canonicalProjectiveLift (affineGenericConfig z).1).gram_diagonalCongruent
      ((ProjectiveProbability.affineConfigFamily 4 (by norm_num)).lift z.1 z.2)
  change projectiveGram (affineGenericConfig z).1 =
    diagonalCongruence (fun i => (d i : ℂ))
      (gram (fun i => ProjectiveProbability.affineVector (z.1 i))) at hd
  change chi4 (projectiveGram (affineGenericConfig z).1) = _
  rw [hd, OrbitChain.chi4_diagonalCongruence]
  · rfl
  · exact z.2 (Sum.inl ⟨(1, 2), by decide⟩)
  · exact z.2 (Sum.inl ⟨(0, 3), by decide⟩)

theorem orbitCoord5_affineGenericConfig_val
    (z : AffineGeneric 5 (by norm_num)) :
    (orbitCoord5 (affineGenericConfig z)).1 = affineGramCoord5 z.1 := by
  obtain ⟨d, hd⟩ :=
    (canonicalProjectiveLift (affineGenericConfig z).1).gram_diagonalCongruent
      ((ProjectiveProbability.affineConfigFamily 5 (by norm_num)).lift z.1 z.2)
  change projectiveGram (affineGenericConfig z).1 =
    diagonalCongruence (fun i => (d i : ℂ))
      (gram (fun i => ProjectiveProbability.affineVector (z.1 i))) at hd
  change chi5 (projectiveGram (affineGenericConfig z).1) = _
  rw [hd, chi5_diagonalCongruence]
  · rfl
  · exact fun i j hij => z.2 (Sum.inl ⟨(i, j), hij⟩)

theorem orbitCoord6_affineGenericConfig_val
    (z : AffineGeneric 6 (by norm_num)) :
    (orbitCoord6 (affineGenericConfig z)).1 = affineGramCoord6 z.1 := by
  obtain ⟨d, hd⟩ :=
    (canonicalProjectiveLift (affineGenericConfig z).1).gram_diagonalCongruent
      ((ProjectiveProbability.affineConfigFamily 6 (by norm_num)).lift z.1 z.2)
  change projectiveGram (affineGenericConfig z).1 =
    diagonalCongruence (fun i => (d i : ℂ))
      (gram (fun i => ProjectiveProbability.affineVector (z.1 i))) at hd
  change chi6 (projectiveGram (affineGenericConfig z).1) = _
  rw [hd, chi6_diagonalCongruence]
  · rfl
  · exact fun i j hij => z.2 (Sum.inl ⟨(i, j), hij⟩)

noncomputable def affineOrbitCoord4
    (z : AffineGeneric 4 (by norm_num)) : U4 :=
  orbitCoord4 (affineGenericConfig z)

noncomputable def affineOrbitCoord5
    (z : AffineGeneric 5 (by norm_num)) : U5 :=
  orbitCoord5 (affineGenericConfig z)

noncomputable def affineOrbitCoord6
    (z : AffineGeneric 6 (by norm_num)) : U6 :=
  orbitCoord6 (affineGenericConfig z)

theorem affineOrbitCoord4_surjective : Function.Surjective affineOrbitCoord4 := by
  intro q
  obtain ⟨z, g, hz⟩ := exists_affineGenericConfig_eq_smul (by norm_num)
    (normalizedConfig4 q)
  refine ⟨z, ?_⟩
  rw [affineOrbitCoord4, hz, orbitCoord4_smulGeneric,
    orbitCoord4_normalizedConfig4]

theorem affineOrbitCoord5_surjective : Function.Surjective affineOrbitCoord5 := by
  intro q
  obtain ⟨z, g, hz⟩ := exists_affineGenericConfig_eq_smul (by norm_num)
    (normalizedConfig5 q)
  refine ⟨z, ?_⟩
  rw [affineOrbitCoord5, hz, orbitCoord5_smulGeneric,
    orbitCoord5_normalizedConfig5]

theorem affineOrbitCoord6_surjective : Function.Surjective affineOrbitCoord6 := by
  intro q
  obtain ⟨z, g, hz⟩ := exists_affineGenericConfig_eq_smul (by norm_num)
    (normalizedConfig6 q)
  refine ⟨z, ?_⟩
  rw [affineOrbitCoord6, hz, orbitCoord6_smulGeneric,
    orbitCoord6_normalizedConfig6]

theorem differentiableAt_affinePairing {n : ℕ} (i j : Fin n)
    (z : Fin n → ProjectiveProbability.AffineCoordinates) :
    DifferentiableAt ℂ (ProjectiveProbability.affinePairing i j) z :=
  (ProjectiveProbability.affinePairing_analytic i j z (Set.mem_univ z)).differentiableAt

theorem affinePairing_ne_of_good {n : ℕ} {h4 : 4 ≤ n}
    (z : AffineGeneric n h4) (i j : Fin n) (hij : i ≠ j) :
    ProjectiveProbability.affinePairing i j z.1 ≠ 0 :=
  z.2 (Sum.inl ⟨(i, j), hij⟩)

theorem differentiableAt_affineNormalizedEntry {m : ℕ}
    (z : Fin (m + 3) → ProjectiveProbability.AffineCoordinates)
    (i j : Fin (m + 3))
    (h12 : ProjectiveProbability.affinePairing 1 2 z ≠ 0)
    (h0i : ProjectiveProbability.affinePairing 0 i z ≠ 0)
    (h0j : ProjectiveProbability.affinePairing 0 j z ≠ 0) :
    DifferentiableAt ℂ
      (fun x => normalizedEntry
        (gram (fun k => ProjectiveProbability.affineVector (x k))) i j) z := by
  change DifferentiableAt ℂ
    ((ProjectiveProbability.affinePairing i j *
          ProjectiveProbability.affinePairing 0 1) *
          ProjectiveProbability.affinePairing 0 2 *
        ((ProjectiveProbability.affinePairing 1 2 *
          ProjectiveProbability.affinePairing 0 i) *
          ProjectiveProbability.affinePairing 0 j)⁻¹) z
  have hnum := ((differentiableAt_affinePairing i j z).mul
      (differentiableAt_affinePairing 0 1 z)).mul
        (differentiableAt_affinePairing 0 2 z)
  have hden := ((differentiableAt_affinePairing 1 2 z).mul
      (differentiableAt_affinePairing 0 i z)).mul
        (differentiableAt_affinePairing 0 j z)
  exact hnum.mul (hden.inv (mul_ne_zero (mul_ne_zero h12 h0i) h0j))

theorem differentiableAt_affineGramCoord4
    (z : AffineGeneric 4 (by norm_num)) :
    DifferentiableAt ℂ affineGramCoord4 z.1 := by
  have hpair (i j : Fin 4) (hij : i ≠ j) :=
    affinePairing_ne_of_good z i j hij
  apply differentiableAt_coord4_mk
  · change DifferentiableAt ℂ
      (ProjectiveProbability.affinePairing 1 3 *
        ProjectiveProbability.affinePairing 0 2 *
          (ProjectiveProbability.affinePairing 1 2 *
            ProjectiveProbability.affinePairing 0 3)⁻¹) z.1
    have hnum := (differentiableAt_affinePairing 1 3 z.1).mul
      (differentiableAt_affinePairing 0 2 z.1)
    have hden := (differentiableAt_affinePairing 1 2 z.1).mul
      (differentiableAt_affinePairing 0 3 z.1)
    exact hnum.mul (hden.inv
      (mul_ne_zero (hpair 1 2 (by decide)) (hpair 0 3 (by decide))))
  · change DifferentiableAt ℂ
      (ProjectiveProbability.affinePairing 2 3 *
        ProjectiveProbability.affinePairing 0 1 *
          (ProjectiveProbability.affinePairing 1 2 *
            ProjectiveProbability.affinePairing 0 3)⁻¹) z.1
    have hnum := (differentiableAt_affinePairing 2 3 z.1).mul
      (differentiableAt_affinePairing 0 1 z.1)
    have hden := (differentiableAt_affinePairing 1 2 z.1).mul
      (differentiableAt_affinePairing 0 3 z.1)
    exact hnum.mul (hden.inv
      (mul_ne_zero (hpair 1 2 (by decide)) (hpair 0 3 (by decide))))

set_option maxHeartbeats 800000 in
theorem differentiableAt_affineGramCoord5
    (z : AffineGeneric 5 (by norm_num)) :
    DifferentiableAt ℂ affineGramCoord5 z.1 := by
  have hpair (i j : Fin 5) (hij : i ≠ j) :=
    affinePairing_ne_of_good z i j hij
  apply differentiableAt_coord5_mk
  all_goals apply differentiableAt_affineNormalizedEntry
  all_goals first | exact hpair 1 2 (by decide) |
    exact hpair 0 1 (by decide) | exact hpair 0 2 (by decide) |
    exact hpair 0 3 (by decide) | exact hpair 0 4 (by decide)

noncomputable def affineGramChartCoord6
    (z : Fin 6 → ProjectiveProbability.AffineCoordinates) : Coord8 :=
  Pfaffian.dropR (affineGramCoord6 z)

set_option maxHeartbeats 800000 in
theorem differentiableAt_affineGramChartCoord6
    (z : AffineGeneric 6 (by norm_num)) :
    DifferentiableAt ℂ affineGramChartCoord6 z.1 := by
  have hpair (i j : Fin 6) (hij : i ≠ j) :=
    affinePairing_ne_of_good z i j hij
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;> apply differentiableAt_affineNormalizedEntry
  all_goals first | exact hpair 1 2 (by decide) |
    exact hpair 0 1 (by decide) | exact hpair 0 2 (by decide) |
    exact hpair 0 3 (by decide) | exact hpair 0 4 (by decide) |
    exact hpair 0 5 (by decide)

noncomputable def affineCoordinatesOfVector (v : SymplecticVector) :
    ProjectiveProbability.AffineCoordinates :=
  fun j => v j.succ / v 0

theorem affinePoint_affineCoordinatesOfVector (v : SymplecticVector)
    (hv : v ≠ 0) (hv0 : v 0 ≠ 0) :
    ProjectiveProbability.affinePoint (affineCoordinatesOfVector v) =
      Projectivization.mk ℂ v hv := by
  exact ProjectiveProbability.affinePoint_affineCoord_of_chart _
    ((ProjectiveProbability.inAffineChart_mk v hv).2 hv0)

noncomputable def rawNormalizedVectors4 (q : Coord4) :
    Fin 4 → SymplecticVector :=
  ![![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![-1, 1, 1, 0],
    ![-q.x, 1, 0, delta4 q]]

@[simp] theorem rawNormalizedVectors4_u4 (q : U4) :
    rawNormalizedVectors4 q.1 = normalizedVectors4 q := rfl

noncomputable def affineSection4 (g : SymplecticGroup) (q : Coord4) :
    Fin 4 → ProjectiveProbability.AffineCoordinates :=
  fun i => affineCoordinatesOfVector (g.1 (rawNormalizedVectors4 q i))

theorem affineTuple_affineSection4 (g : SymplecticGroup) (q : U4)
    (hden : ∀ i, g.1 (rawNormalizedVectors4 q.1 i) 0 ≠ 0) :
    ProjectiveProbability.affineTuple 4 (affineSection4 g q.1) =
      (smulGeneric g (normalizedConfig4 q)).1 := by
  funext i
  change ProjectiveProbability.affinePoint
      (affineCoordinatesOfVector (g.1 (rawNormalizedVectors4 q.1 i))) =
    g.1 • Projectivization.mk ℂ (normalizedVectors4 q i)
      (normalizedVectors4_ne q i)
  rw [Projectivization.smul_mk]
  exact affinePoint_affineCoordinatesOfVector _
    (by
      simpa using g.1.injective.ne (normalizedVectors4_ne q i))
    (hden i)

theorem affineGramCoord4_affineSection4 (g : SymplecticGroup) (q : U4)
    (hden : ∀ i, g.1 (rawNormalizedVectors4 q.1 i) 0 ≠ 0) :
    affineGramCoord4 (affineSection4 g q.1) = q.1 := by
  have hconfig := affineTuple_affineSection4 g q hden
  have hgeneric : IsGeneric
      (ProjectiveProbability.affineTuple 4 (affineSection4 g q.1)) := by
    rw [hconfig]
    exact (normalizedConfig4 q).2.smul g
  have hgood : (ProjectiveProbability.affineConfigFamily 4 (by norm_num)).Good
      (affineSection4 g q.1) :=
    (ProjectiveProbability.affineConfigFamily 4 (by norm_num)).good_of_projectivized_generic
      (fun i => ProjectiveProbability.affineVector_ne_zero _) hgeneric
  let z : AffineGeneric 4 (by norm_num) :=
    ⟨affineSection4 g q.1, hgood⟩
  rw [← orbitCoord4_affineGenericConfig_val z]
  have hz : affineGenericConfig z = smulGeneric g (normalizedConfig4 q) := by
    apply Subtype.ext
    exact hconfig
  rw [hz, orbitCoord4_smulGeneric, orbitCoord4_normalizedConfig4]

theorem affineSection4_denom_ne (z : AffineGeneric 4 (by norm_num)) :
    ∃ g : SymplecticGroup,
      smulGeneric g (normalizedConfig4 (orbitCoord4 (affineGenericConfig z))) =
          affineGenericConfig z ∧
        ∀ i, g.1 (rawNormalizedVectors4
          (orbitCoord4 (affineGenericConfig z)).1 i) 0 ≠ 0 := by
  obtain ⟨g, hg⟩ := exists_smul_normalizedConfig4_orbitCoord4
    (affineGenericConfig z)
  refine ⟨g, hg, fun i => ?_⟩
  have hpoint := congrFun (congrArg Subtype.val hg) i
  have hchart : ProjectiveProbability.InAffineChart
      ((smulGeneric g
        (normalizedConfig4 (orbitCoord4 (affineGenericConfig z)))).1 i) := by
    rw [hpoint]
    exact (ProjectiveProbability.inAffineChart_mk _ _).2 (by
      simp [ProjectiveProbability.affineVector])
  rw [show (smulGeneric g
      (normalizedConfig4 (orbitCoord4 (affineGenericConfig z)))).1 i =
      Projectivization.mk ℂ
        (g.1 (rawNormalizedVectors4
          (orbitCoord4 (affineGenericConfig z)).1 i))
        (by
          simpa using g.1.injective.ne
            (normalizedVectors4_ne
              (orbitCoord4 (affineGenericConfig z)) i)) by
    change g.1 • Projectivization.mk ℂ
      (normalizedVectors4 (orbitCoord4 (affineGenericConfig z)) i)
      (normalizedVectors4_ne _ i) = _
    rw [Projectivization.smul_mk]
    rfl] at hchart
  exact (ProjectiveProbability.inAffineChart_mk _ _).1 hchart

theorem differentiable_rawNormalizedVectors4 :
    Differentiable ℂ rawNormalizedVectors4 := by
  intro q
  rw [differentiableAt_pi]
  intro i
  rw [differentiableAt_pi]
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [rawNormalizedVectors4] <;> fun_prop [delta4]

theorem continuous_rawNormalizedVectors4 :
    Continuous rawNormalizedVectors4 :=
  differentiable_rawNormalizedVectors4.continuous

theorem differentiableAt_affineSection4 (g : SymplecticGroup) (q : Coord4)
    (hden : ∀ i, g.1 (rawNormalizedVectors4 q i) 0 ≠ 0) :
    DifferentiableAt ℂ (affineSection4 g) q := by
  rw [differentiableAt_pi]
  intro i
  rw [differentiableAt_pi]
  intro j
  have hv : DifferentiableAt ℂ
      (fun x => g.1 (rawNormalizedVectors4 x i)) q :=
    (symplecticContinuousEquiv g).differentiableAt.comp q
      (differentiableAt_pi.mp (differentiable_rawNormalizedVectors4 q) i)
  change DifferentiableAt ℂ
    ((fun x => g.1 (rawNormalizedVectors4 x i) j.succ) *
      (fun x => g.1 (rawNormalizedVectors4 x i) 0)⁻¹) q
  exact (differentiableAt_pi.mp hv j.succ).mul
    ((differentiableAt_pi.mp hv 0).inv (hden i))

theorem affineGramCoord4_hasSurjectiveComplexFDerivAt
    (z : AffineGeneric 4 (by norm_num)) :
    HasSurjectiveComplexFDerivAt affineGramCoord4 z.1 := by
  obtain ⟨g, hg, hden⟩ := affineSection4_denom_ne z
  let q := orbitCoord4 (affineGenericConfig z)
  have hq : q.1 = affineGramCoord4 z.1 :=
    orbitCoord4_affineGenericConfig_val z
  apply Pfaffian.hasSurjectiveComplexFDerivAt_of_eventual_section
    affineGramCoord4 z.1 (affineSection4 g)
      (differentiableAt_affineGramCoord4 z)
      (by
        rw [← hq]
        exact differentiableAt_affineSection4 g q.1 hden)
  · rw [← hq]
    apply (ProjectiveProbability.measurableEmbedding_affineTuple 4).injective
    rw [affineTuple_affineSection4 g q hden]
    exact congrArg Subtype.val hg
  · rw [← hq]
    have hdenEventually : ∀ᶠ q' in nhds q.1,
        ∀ i, g.1 (rawNormalizedVectors4 q' i) 0 ≠ 0 := by
      exact Filter.eventually_all.2 fun i =>
        (isOpen_ne_fun (by
          exact (continuous_apply 0).comp
            ((symplecticContinuousEquiv g).continuous.comp
              ((continuous_apply i).comp continuous_rawNormalizedVectors4)))
          continuous_const).mem_nhds (hden i)
    filter_upwards [isOpen_u4Set.mem_nhds q.2, hdenEventually] with q' hq' hqden
    change affineGramCoord4 (affineSection4 g q') = q'
    exact affineGramCoord4_affineSection4 g ⟨q', hq'⟩ hqden

noncomputable def rawNormalizedVectors5 (q : Coord5) :
    Fin 5 → SymplecticVector :=
  ![![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![-1, 1, 1, 0],
    ![-q.u, 1, 0, p4 q],
    ![-q.v, 1, (q.v - q.u - q.y) / p4 q, p3 q]]

@[simp] theorem rawNormalizedVectors5_u5 (q : U5) :
    rawNormalizedVectors5 q.1 = normalizedVectors5 q := rfl

noncomputable def affineSection5 (g : SymplecticGroup) (q : Coord5) :
    Fin 5 → ProjectiveProbability.AffineCoordinates :=
  fun i => affineCoordinatesOfVector (g.1 (rawNormalizedVectors5 q i))

theorem affineTuple_affineSection5 (g : SymplecticGroup) (q : U5)
    (hden : ∀ i, g.1 (rawNormalizedVectors5 q.1 i) 0 ≠ 0) :
    ProjectiveProbability.affineTuple 5 (affineSection5 g q.1) =
      (smulGeneric g (normalizedConfig5 q)).1 := by
  funext i
  change ProjectiveProbability.affinePoint
      (affineCoordinatesOfVector (g.1 (rawNormalizedVectors5 q.1 i))) =
    g.1 • Projectivization.mk ℂ (normalizedVectors5 q i)
      (normalizedVectors5_ne q i)
  rw [Projectivization.smul_mk]
  exact affinePoint_affineCoordinatesOfVector _
    (by simpa using g.1.injective.ne (normalizedVectors5_ne q i)) (hden i)

theorem affineGramCoord5_affineSection5 (g : SymplecticGroup) (q : U5)
    (hden : ∀ i, g.1 (rawNormalizedVectors5 q.1 i) 0 ≠ 0) :
    affineGramCoord5 (affineSection5 g q.1) = q.1 := by
  have hconfig := affineTuple_affineSection5 g q hden
  have hgeneric : IsGeneric
      (ProjectiveProbability.affineTuple 5 (affineSection5 g q.1)) := by
    rw [hconfig]
    exact (normalizedConfig5 q).2.smul g
  have hgood : (ProjectiveProbability.affineConfigFamily 5 (by norm_num)).Good
      (affineSection5 g q.1) :=
    (ProjectiveProbability.affineConfigFamily 5 (by norm_num)).good_of_projectivized_generic
      (fun i => ProjectiveProbability.affineVector_ne_zero _) hgeneric
  let z : AffineGeneric 5 (by norm_num) :=
    ⟨affineSection5 g q.1, hgood⟩
  rw [← orbitCoord5_affineGenericConfig_val z]
  have hz : affineGenericConfig z = smulGeneric g (normalizedConfig5 q) := by
    apply Subtype.ext
    exact hconfig
  rw [hz, orbitCoord5_smulGeneric, orbitCoord5_normalizedConfig5]

theorem affineSection5_denom_ne (z : AffineGeneric 5 (by norm_num)) :
    ∃ g : SymplecticGroup,
      smulGeneric g (normalizedConfig5 (orbitCoord5 (affineGenericConfig z))) =
          affineGenericConfig z ∧
        ∀ i, g.1 (rawNormalizedVectors5
          (orbitCoord5 (affineGenericConfig z)).1 i) 0 ≠ 0 := by
  obtain ⟨g, hg⟩ := exists_smul_normalizedConfig5_orbitCoord5
    (affineGenericConfig z)
  refine ⟨g, hg, fun i => ?_⟩
  have hpoint := congrFun (congrArg Subtype.val hg) i
  have hchart : ProjectiveProbability.InAffineChart
      ((smulGeneric g
        (normalizedConfig5 (orbitCoord5 (affineGenericConfig z)))).1 i) := by
    rw [hpoint]
    exact (ProjectiveProbability.inAffineChart_mk _ _).2 (by
      simp [ProjectiveProbability.affineVector])
  rw [show (smulGeneric g
      (normalizedConfig5 (orbitCoord5 (affineGenericConfig z)))).1 i =
      Projectivization.mk ℂ
        (g.1 (rawNormalizedVectors5
          (orbitCoord5 (affineGenericConfig z)).1 i))
        (by
          simpa using g.1.injective.ne
            (normalizedVectors5_ne
              (orbitCoord5 (affineGenericConfig z)) i)) by
    change g.1 • Projectivization.mk ℂ
      (normalizedVectors5 (orbitCoord5 (affineGenericConfig z)) i)
      (normalizedVectors5_ne _ i) = _
    rw [Projectivization.smul_mk]
    rfl] at hchart
  exact (ProjectiveProbability.inAffineChart_mk _ _).1 hchart

theorem differentiableAt_rawNormalizedVectors5 (q : U5) :
    DifferentiableAt ℂ rawNormalizedVectors5 q.1 := by
  rw [differentiableAt_pi]
  intro i
  rw [differentiableAt_pi]
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [rawNormalizedVectors5] <;>
    fun_prop (disch := first | exact q.2.p4_ne | assumption) [p4, p3]

theorem differentiableAt_affineSection5 (g : SymplecticGroup) (q : U5)
    (hden : ∀ i, g.1 (rawNormalizedVectors5 q.1 i) 0 ≠ 0) :
    DifferentiableAt ℂ (affineSection5 g) q.1 := by
  rw [differentiableAt_pi]
  intro i
  rw [differentiableAt_pi]
  intro j
  have hv : DifferentiableAt ℂ
      (fun x => g.1 (rawNormalizedVectors5 x i)) q.1 :=
    (symplecticContinuousEquiv g).differentiableAt.comp q.1
      (differentiableAt_pi.mp (differentiableAt_rawNormalizedVectors5 q) i)
  change DifferentiableAt ℂ
    ((fun x => g.1 (rawNormalizedVectors5 x i) j.succ) *
      (fun x => g.1 (rawNormalizedVectors5 x i) 0)⁻¹) q.1
  exact (differentiableAt_pi.mp hv j.succ).mul
    ((differentiableAt_pi.mp hv 0).inv (hden i))

theorem affineGramCoord5_hasSurjectiveComplexFDerivAt
    (z : AffineGeneric 5 (by norm_num)) :
    HasSurjectiveComplexFDerivAt affineGramCoord5 z.1 := by
  obtain ⟨g, hg, hden⟩ := affineSection5_denom_ne z
  let q := orbitCoord5 (affineGenericConfig z)
  have hq : q.1 = affineGramCoord5 z.1 :=
    orbitCoord5_affineGenericConfig_val z
  apply Pfaffian.hasSurjectiveComplexFDerivAt_of_eventual_section
    affineGramCoord5 z.1 (affineSection5 g)
      (differentiableAt_affineGramCoord5 z)
      (by
        rw [← hq]
        exact differentiableAt_affineSection5 g q hden)
  · rw [← hq]
    apply (ProjectiveProbability.measurableEmbedding_affineTuple 5).injective
    rw [affineTuple_affineSection5 g q hden]
    exact congrArg Subtype.val hg
  · rw [← hq]
    have hdenEventually : ∀ᶠ q' in nhds q.1,
        ∀ i, g.1 (rawNormalizedVectors5 q' i) 0 ≠ 0 := by
      exact Filter.eventually_all.2 fun i =>
        ((continuous_apply 0).continuousAt.comp
          ((symplecticContinuousEquiv g).continuous.continuousAt.comp
            ((continuous_apply i).continuousAt.comp
              (differentiableAt_rawNormalizedVectors5 q).continuousAt))).eventually_ne
          (hden i)
    filter_upwards [isOpen_u5Set.mem_nhds q.2, hdenEventually] with q' hq' hqden
    change affineGramCoord5 (affineSection5 g q') = q'
    exact affineGramCoord5_affineSection5 g ⟨q', hq'⟩ hqden

noncomputable def rawNormalizedVectors6 (q : Coord6) :
    Fin 6 → SymplecticVector :=
  ![![1, 0, 0, 0],
    ![0, 1, 0, 0],
    ![-1, 1, 1, 0],
    ![-q.u, 1, 0, pf0123 q],
    ![-q.v, 1, (q.v - q.u - q.y) / pf0123 q, pf0124 q],
    ![-q.s, 1, (q.s - q.u - q.z) / pf0123 q, pf0125 q]]

@[simp] theorem rawNormalizedVectors6_u6 (q : U6) :
    rawNormalizedVectors6 q.1 = normalizedVectors6 q := rfl

noncomputable def rawNormalizedVectors6Chart (p : Coord8) :
    Fin 6 → SymplecticVector :=
  rawNormalizedVectors6 (chartCoord6 p)

@[simp] theorem rawNormalizedVectors6Chart_u6Chart (p : U6Chart) :
    rawNormalizedVectors6Chart p.1 = normalizedVectors6 (chartToU6 p) := rfl

noncomputable def affineSection6 (g : SymplecticGroup) (p : Coord8) :
    Fin 6 → ProjectiveProbability.AffineCoordinates :=
  fun i => affineCoordinatesOfVector (g.1 (rawNormalizedVectors6Chart p i))

theorem affineTuple_affineSection6 (g : SymplecticGroup) (p : U6Chart)
    (hden : ∀ i, g.1 (rawNormalizedVectors6Chart p.1 i) 0 ≠ 0) :
    ProjectiveProbability.affineTuple 6 (affineSection6 g p.1) =
      (smulGeneric g (normalizedConfig6 (chartToU6 p))).1 := by
  funext i
  change ProjectiveProbability.affinePoint
      (affineCoordinatesOfVector (g.1 (rawNormalizedVectors6Chart p.1 i))) =
    g.1 • Projectivization.mk ℂ (normalizedVectors6 (chartToU6 p) i)
      (normalizedVectors6_ne (chartToU6 p) i)
  rw [Projectivization.smul_mk]
  exact affinePoint_affineCoordinatesOfVector _
    (by simpa only [rawNormalizedVectors6Chart_u6Chart, map_zero] using
      g.1.injective.ne (normalizedVectors6_ne (chartToU6 p) i))
    (hden i)

theorem affineGramChartCoord6_affineSection6
    (g : SymplecticGroup) (p : U6Chart)
    (hden : ∀ i, g.1 (rawNormalizedVectors6Chart p.1 i) 0 ≠ 0) :
    affineGramChartCoord6 (affineSection6 g p.1) = p.1 := by
  have hconfig := affineTuple_affineSection6 g p hden
  have hgeneric : IsGeneric
      (ProjectiveProbability.affineTuple 6 (affineSection6 g p.1)) := by
    rw [hconfig]
    exact (normalizedConfig6 (chartToU6 p)).2.smul g
  have hgood : (ProjectiveProbability.affineConfigFamily 6 (by norm_num)).Good
      (affineSection6 g p.1) :=
    (ProjectiveProbability.affineConfigFamily 6 (by norm_num)).good_of_projectivized_generic
      (fun i => ProjectiveProbability.affineVector_ne_zero _) hgeneric
  let z : AffineGeneric 6 (by norm_num) :=
    ⟨affineSection6 g p.1, hgood⟩
  have hz : affineGenericConfig z =
      smulGeneric g (normalizedConfig6 (chartToU6 p)) := by
    apply Subtype.ext
    exact hconfig
  have horbit : orbitCoord6 (affineGenericConfig z) = chartToU6 p := by
    rw [hz, orbitCoord6_smulGeneric, orbitCoord6_normalizedConfig6]
  have horbit' := congrArg (fun q : U6 => dropR q.1) horbit
  rw [orbitCoord6_affineGenericConfig_val z] at horbit'
  change dropR (affineGramCoord6 z.1) = dropR (chartCoord6 p.1) at horbit'
  rw [dropR_chartCoord6] at horbit'
  exact horbit'

theorem affineSection6_denom_ne (z : AffineGeneric 6 (by norm_num)) :
    ∃ g : SymplecticGroup,
      smulGeneric g (normalizedConfig6 (orbitCoord6 (affineGenericConfig z))) =
          affineGenericConfig z ∧
        ∀ i, g.1 (rawNormalizedVectors6
          (orbitCoord6 (affineGenericConfig z)).1 i) 0 ≠ 0 := by
  obtain ⟨g, hg⟩ := exists_smul_normalizedConfig6_orbitCoord6
    (affineGenericConfig z)
  refine ⟨g, hg, fun i => ?_⟩
  have hpoint := congrFun (congrArg Subtype.val hg) i
  have hchart : ProjectiveProbability.InAffineChart
      ((smulGeneric g
        (normalizedConfig6 (orbitCoord6 (affineGenericConfig z)))).1 i) := by
    rw [hpoint]
    exact (ProjectiveProbability.inAffineChart_mk _ _).2 (by
      simp [ProjectiveProbability.affineVector])
  rw [show (smulGeneric g
      (normalizedConfig6 (orbitCoord6 (affineGenericConfig z)))).1 i =
      Projectivization.mk ℂ
        (g.1 (rawNormalizedVectors6
          (orbitCoord6 (affineGenericConfig z)).1 i))
        (by
          simpa using g.1.injective.ne
            (normalizedVectors6_ne
              (orbitCoord6 (affineGenericConfig z)) i)) by
    change g.1 • Projectivization.mk ℂ
      (normalizedVectors6 (orbitCoord6 (affineGenericConfig z)) i)
      (normalizedVectors6_ne _ i) = _
    rw [Projectivization.smul_mk]
    rfl] at hchart
  exact (ProjectiveProbability.inAffineChart_mk _ _).1 hchart

@[fun_prop] theorem differentiable_coord6_u' :
    Differentiable ℂ (fun q : Coord6 => q.u) := by
  change Differentiable ℂ (fun q : Coord6 => coord6LinearIsometryEquivFun q 0)
  fun_prop

@[fun_prop] theorem differentiable_coord6_v' :
    Differentiable ℂ (fun q : Coord6 => q.v) := by
  change Differentiable ℂ (fun q : Coord6 => coord6LinearIsometryEquivFun q 1)
  fun_prop

@[fun_prop] theorem differentiable_coord6_s' :
    Differentiable ℂ (fun q : Coord6 => q.s) := by
  change Differentiable ℂ (fun q : Coord6 => coord6LinearIsometryEquivFun q 2)
  fun_prop

@[fun_prop] theorem differentiable_coord6_w' :
    Differentiable ℂ (fun q : Coord6 => q.w) := by
  change Differentiable ℂ (fun q : Coord6 => coord6LinearIsometryEquivFun q 3)
  fun_prop

@[fun_prop] theorem differentiable_coord6_x' :
    Differentiable ℂ (fun q : Coord6 => q.x) := by
  change Differentiable ℂ (fun q : Coord6 => coord6LinearIsometryEquivFun q 4)
  fun_prop

@[fun_prop] theorem differentiable_coord6_t' :
    Differentiable ℂ (fun q : Coord6 => q.t) := by
  change Differentiable ℂ (fun q : Coord6 => coord6LinearIsometryEquivFun q 5)
  fun_prop

@[fun_prop] theorem differentiable_coord6_y' :
    Differentiable ℂ (fun q : Coord6 => q.y) := by
  change Differentiable ℂ (fun q : Coord6 => coord6LinearIsometryEquivFun q 6)
  fun_prop

@[fun_prop] theorem differentiable_coord6_z' :
    Differentiable ℂ (fun q : Coord6 => q.z) := by
  change Differentiable ℂ (fun q : Coord6 => coord6LinearIsometryEquivFun q 7)
  fun_prop

theorem differentiableAt_rawNormalizedVectors6 (q : U6) :
    DifferentiableAt ℂ rawNormalizedVectors6 q.1 := by
  rw [differentiableAt_pi]
  intro i
  rw [differentiableAt_pi]
  intro j
  fin_cases i <;> fin_cases j <;>
    simp [rawNormalizedVectors6] <;>
    fun_prop (disch := first | exact q.2.pf0123_ne | assumption)
      [pf0123, pf0124, pf0125]

theorem differentiableAt_rawNormalizedVectors6Chart (p : U6Chart) :
    DifferentiableAt ℂ rawNormalizedVectors6Chart p.1 := by
  exact (differentiableAt_rawNormalizedVectors6 (chartToU6 p)).comp p.1
    (differentiableAt_chartCoord6 p.2.1)

theorem differentiableAt_affineSection6 (g : SymplecticGroup) (p : U6Chart)
    (hden : ∀ i, g.1 (rawNormalizedVectors6Chart p.1 i) 0 ≠ 0) :
    DifferentiableAt ℂ (affineSection6 g) p.1 := by
  rw [differentiableAt_pi]
  intro i
  rw [differentiableAt_pi]
  intro j
  have hv : DifferentiableAt ℂ
      (fun x => g.1 (rawNormalizedVectors6Chart x i)) p.1 :=
    (symplecticContinuousEquiv g).differentiableAt.comp p.1
      (differentiableAt_pi.mp (differentiableAt_rawNormalizedVectors6Chart p) i)
  change DifferentiableAt ℂ
    ((fun x => g.1 (rawNormalizedVectors6Chart x i) j.succ) *
      (fun x => g.1 (rawNormalizedVectors6Chart x i) 0)⁻¹) p.1
  exact (differentiableAt_pi.mp hv j.succ).mul
    ((differentiableAt_pi.mp hv 0).inv (hden i))

theorem affineGramChartCoord6_hasSurjectiveComplexFDerivAt
    (z : AffineGeneric 6 (by norm_num)) :
    HasSurjectiveComplexFDerivAt affineGramChartCoord6 z.1 := by
  obtain ⟨g, hg, hden⟩ := affineSection6_denom_ne z
  let q := orbitCoord6 (affineGenericConfig z)
  let p := u6ToChart q
  have hpval : p.1 = affineGramChartCoord6 z.1 := by
    exact congrArg dropR (orbitCoord6_affineGenericConfig_val z)
  have hden' : ∀ i, g.1 (rawNormalizedVectors6Chart p.1 i) 0 ≠ 0 := by
    intro i
    change g.1 (rawNormalizedVectors6 (chartCoord6 (dropR q.1)) i) 0 ≠ 0
    rw [chartCoord6_dropR q]
    exact hden i
  apply Pfaffian.hasSurjectiveComplexFDerivAt_of_eventual_section
    affineGramChartCoord6 z.1 (affineSection6 g)
      (differentiableAt_affineGramChartCoord6 z)
      (by
        rw [← hpval]
        exact differentiableAt_affineSection6 g p hden')
  · rw [← hpval]
    apply (ProjectiveProbability.measurableEmbedding_affineTuple 6).injective
    rw [affineTuple_affineSection6 g p hden']
    rw [show chartToU6 p = q by exact u6ChartEquiv.right_inv q]
    exact congrArg Subtype.val hg
  · rw [← hpval]
    have hdenEventually : ∀ᶠ p' in nhds p.1,
        ∀ i, g.1 (rawNormalizedVectors6Chart p' i) 0 ≠ 0 := by
      exact Filter.eventually_all.2 fun i =>
        ((continuous_apply 0).continuousAt.comp
          ((symplecticContinuousEquiv g).continuous.continuousAt.comp
            ((continuous_apply i).continuousAt.comp
              (differentiableAt_rawNormalizedVectors6Chart p).continuousAt))).eventually_ne
          (hden' i)
    filter_upwards [isOpen_u6ChartSet.mem_nhds p.2, hdenEventually]
      with p' hp' hpden
    change affineGramChartCoord6 (affineSection6 g p') = p'
    exact affineGramChartCoord6_affineSection6 g ⟨p', hp'⟩ hpden

noncomputable def affineConfigCoordinates (n : ℕ) :
    (Fin n → ProjectiveProbability.AffineCoordinates) ≃L[ℂ]
      (Fin (3 * n) → ℂ) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    rw [Module.finrank_pi_fintype]
    simp [ProjectiveProbability.AffineCoordinates, Nat.mul_comm])

noncomputable def affineCoordinateGaussian (n : ℕ) :
    Measure (Fin n → ProjectiveProbability.AffineCoordinates) :=
  coordinateGaussian (3 * n) (affineConfigCoordinates n)

instance (n : ℕ) : IsProbabilityMeasure (affineCoordinateGaussian n) := by
  apply Measure.isProbabilityMeasure_map
  exact (affineConfigCoordinates n).symm.continuous.measurable.aemeasurable

instance (n : ℕ) : (affineCoordinateGaussian n).IsOpenPosMeasure := by
  exact (affineConfigCoordinates n).symm.continuous.isOpenPosMeasure_map
    (affineConfigCoordinates n).symm.surjective

noncomputable def affineCoordinateGaussianPresentation (n : ℕ) :
    GaussianCoordinatePresentation (affineCoordinateGaussian n) :=
  coordinateGaussianPresentation (3 * n) (affineConfigCoordinates n)

theorem sourceMeasure_absolutelyContinuous_affineCoordinateGaussian (n : ℕ) :
    ProjectiveProbability.sourceMeasure n ≪ affineCoordinateGaussian n := by
  let productVolume : Measure
      (Fin n → ProjectiveProbability.AffineCoordinates) :=
    Measure.pi fun _ : Fin n => (volume : Measure (Fin 3 → ℂ))
  let coordinateVolume : Measure
      (Fin n → ProjectiveProbability.AffineCoordinates) :=
    Measure.map (affineConfigCoordinates n).symm
      (volume : Measure (Fin (3 * n) → ℂ))
  have hsource : ProjectiveProbability.sourceMeasure n ≪ productVolume := by
    exact Measure.piFin_absolutelyContinuous _ _
      (standardComplexGaussianPi_absolutelyContinuous_volume 3) n
  let _ : Measure.IsAddHaarMeasure productVolume := by
    dsimp [productVolume]
    exact Measure.pi.isAddHaarMeasure
      (fun _ : Fin n => (volume : Measure (Fin 3 → ℂ)))
  let _ : Measure.IsAddHaarMeasure coordinateVolume := by
    exact (affineConfigCoordinates n).symm.isAddHaarMeasure_map
      (volume : Measure (Fin (3 * n) → ℂ))
  have hhaar : productVolume ≪ coordinateVolume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have hgaussian : coordinateVolume ≪ affineCoordinateGaussian n := by
    exact (volume_absolutelyContinuous_standardComplexGaussianPi (3 * n)).map
      (affineConfigCoordinates n).symm.continuous.measurable
  exact hsource.trans (hhaar.trans hgaussian)

theorem affineCoordinateGaussian_absolutelyContinuous_sourceMeasure (n : ℕ) :
    affineCoordinateGaussian n ≪ ProjectiveProbability.sourceMeasure n := by
  let productVolume : Measure
      (Fin n → ProjectiveProbability.AffineCoordinates) :=
    Measure.pi fun _ : Fin n => (volume : Measure (Fin 3 → ℂ))
  let coordinateVolume : Measure
      (Fin n → ProjectiveProbability.AffineCoordinates) :=
    Measure.map (affineConfigCoordinates n).symm
      (volume : Measure (Fin (3 * n) → ℂ))
  have hgaussian : affineCoordinateGaussian n ≪ coordinateVolume := by
    exact (standardComplexGaussianPi_absolutelyContinuous_volume (3 * n)).map
      (affineConfigCoordinates n).symm.continuous.measurable
  let _ : Measure.IsAddHaarMeasure productVolume := by
    dsimp [productVolume]
    exact Measure.pi.isAddHaarMeasure
      (fun _ : Fin n => (volume : Measure (Fin 3 → ℂ)))
  let _ : Measure.IsAddHaarMeasure coordinateVolume := by
    exact (affineConfigCoordinates n).symm.isAddHaarMeasure_map
      (volume : Measure (Fin (3 * n) → ℂ))
  have hhaar : coordinateVolume ≪ productVolume :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have hsource : productVolume ≪ ProjectiveProbability.sourceMeasure n := by
    exact Measure.piFin_absolutelyContinuous _ _
      (volume_absolutelyContinuous_standardComplexGaussianPi 3) n
  exact hgaussian.trans (hhaar.trans hsource)

theorem affineGoodSet_isOpen {n : ℕ} (h4 : 4 ≤ n) :
    IsOpen (ProjectiveProbability.affineConfigFamily n h4).goodSet :=
  ((ProjectiveProbability.affineConfigFamily n h4).goodSet_isOpen_dense
    ⟨ProjectiveProbability.momentTuple n,
      ProjectiveProbability.affineConfigFamily_good_moment h4⟩).1

theorem affineGoodSet_nonempty {n : ℕ} (h4 : 4 ≤ n) :
    (ProjectiveProbability.affineConfigFamily n h4).goodSet.Nonempty :=
  (ProjectiveProbability.affineConfigFamily n h4).goodSet_nonempty
    ⟨ProjectiveProbability.momentTuple n,
      ProjectiveProbability.affineConfigFamily_good_moment h4⟩

noncomputable def coordinateAffineGenericMeasure (n : ℕ) (h4 : 4 ≤ n) :
    Measure (AffineGeneric n h4) :=
  normalizedOpenMeasure (affineCoordinateGaussian n)
    (ProjectiveProbability.affineConfigFamily n h4).goodSet
    (affineGoodSet_isOpen h4) (affineGoodSet_nonempty h4)

noncomputable def naturalAffineGenericMeasure (n : ℕ) (h4 : 4 ≤ n) :
    Measure (AffineGeneric n h4) :=
  normalizedOpenMeasure (ProjectiveProbability.sourceMeasure n)
    (ProjectiveProbability.affineConfigFamily n h4).goodSet
    (affineGoodSet_isOpen h4) (affineGoodSet_nonempty h4)

instance naturalAffineGenericMeasure_isProbability
    (n : ℕ) (h4 : 4 ≤ n) :
    IsProbabilityMeasure (naturalAffineGenericMeasure n h4) :=
  normalizedOpenMeasure_isProbability
    (ProjectiveProbability.sourceMeasure n)
    (ProjectiveProbability.affineConfigFamily n h4).goodSet
    (affineGoodSet_isOpen h4) (affineGoodSet_nonempty h4)

instance (n : ℕ) : (ProjectiveProbability.sourceMeasure n).IsOpenPosMeasure := by
  dsimp [ProjectiveProbability.sourceMeasure]
  exact Measure.pi.isOpenPosMeasure
    (μ := fun _ : Fin n => standardComplexGaussianPi 3)

theorem naturalAffineGenericMeasure_absolutelyContinuous_coordinate
    (n : ℕ) (h4 : 4 ≤ n) :
  naturalAffineGenericMeasure n h4 ≪ coordinateAffineGenericMeasure n h4 :=
  normalizedOpenMeasure_absolutelyContinuous
    (s := (ProjectiveProbability.affineConfigFamily n h4).goodSet)
    (sourceMeasure_absolutelyContinuous_affineCoordinateGaussian n)
    (affineGoodSet_isOpen h4) (affineGoodSet_nonempty h4)

theorem coordinateAffineGenericMeasure_absolutelyContinuous_natural
    (n : ℕ) (h4 : 4 ≤ n) :
  coordinateAffineGenericMeasure n h4 ≪ naturalAffineGenericMeasure n h4 :=
  normalizedOpenMeasure_absolutelyContinuous
    (s := (ProjectiveProbability.affineConfigFamily n h4).goodSet)
    (affineCoordinateGaussian_absolutelyContinuous_sourceMeasure n)
    (affineGoodSet_isOpen h4) (affineGoodSet_nonempty h4)

theorem map_val_naturalAffineGenericMeasure_absolutelyContinuous_source
    (n : ℕ) (h4 : 4 ≤ n) :
    Measure.map (Subtype.val : AffineGeneric n h4 →
        Fin n → ProjectiveProbability.AffineCoordinates)
        (naturalAffineGenericMeasure n h4) ≪
      ProjectiveProbability.sourceMeasure n := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hnull
  rw [Measure.map_apply measurable_subtype_coe hs]
  apply (normalizedOpenMeasure_eq_zero_iff_image
    (ProjectiveProbability.sourceMeasure n)
    (ProjectiveProbability.affineConfigFamily n h4).goodSet
    (affineGoodSet_isOpen h4) (affineGoodSet_nonempty h4)
    (hs.preimage measurable_subtype_coe)).mpr
  apply measure_mono_null _ hnull
  rintro _ ⟨z, hz, rfl⟩
  exact hz

theorem source_absolutelyContinuous_map_val_naturalAffineGenericMeasure
    (n : ℕ) (h4 : 4 ≤ n) :
    ProjectiveProbability.sourceMeasure n ≪
      Measure.map (Subtype.val : AffineGeneric n h4 →
        Fin n → ProjectiveProbability.AffineCoordinates)
        (naturalAffineGenericMeasure n h4) := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hnull
  rw [Measure.map_apply measurable_subtype_coe hs] at hnull
  have himageNull : ProjectiveProbability.sourceMeasure n
      (Subtype.val '' (Subtype.val ⁻¹' s : Set (AffineGeneric n h4))) = 0 :=
    (normalizedOpenMeasure_eq_zero_iff_image
      (ProjectiveProbability.sourceMeasure n)
      (ProjectiveProbability.affineConfigFamily n h4).goodSet
      (affineGoodSet_isOpen h4) (affineGoodSet_nonempty h4)
      (hs.preimage measurable_subtype_coe)).mp hnull
  have hbad : ProjectiveProbability.sourceMeasure n
      (ProjectiveProbability.affineConfigFamily n h4).goodSetᶜ = 0 := by
    change ProjectiveProbability.sourceMeasure n
      {z | ¬(ProjectiveProbability.affineConfigFamily n h4).Good z} = 0
    rw [← ae_iff]
    exact ProjectiveProbability.ae_affineConfigFamily_good h4
  apply measure_mono_null _ (measure_union_null himageNull hbad)
  intro x hx
  by_cases hgood : x ∈
      (ProjectiveProbability.affineConfigFamily n h4).goodSet
  · left
    exact ⟨⟨x, hgood⟩, hx, rfl⟩
  · exact Or.inr hgood

noncomputable def affineGramMap4
    (z : AffineGeneric 4 (by norm_num)) : U4 :=
  ⟨affineGramCoord4 z.1, by
    rw [← orbitCoord4_affineGenericConfig_val z]
    exact (orbitCoord4 (affineGenericConfig z)).2⟩

@[simp] theorem affineGramMap4_val (z : AffineGeneric 4 (by norm_num)) :
    (affineGramMap4 z).1 = affineGramCoord4 z.1 := rfl

theorem affineGramMap4_surjective : Function.Surjective affineGramMap4 := by
  intro q
  obtain ⟨z, hz⟩ := affineOrbitCoord4_surjective q
  refine ⟨z, ?_⟩
  apply Subtype.ext
  rw [affineGramMap4_val, ← orbitCoord4_affineGenericConfig_val]
  exact congrArg Subtype.val hz

theorem affineGramMap4_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving affineGramMap4
      (coordinateAffineGenericMeasure 4 (by norm_num)) measureU4 := by
  have h := quasiMeasurePreserving_normalizedOpenGaussian_of_submersion
    (affineCoordinateGaussian 4) coord4Gaussian
    (affineCoordinateGaussianPresentation 4) coord4GaussianPresentation
    (ProjectiveProbability.affineConfigFamily 4 (by norm_num)).goodSet
      (affineGoodSet_isOpen (by norm_num))
      (affineGoodSet_nonempty (by norm_num))
    u4Set isOpen_u4Set u4Set_nonempty
    affineGramCoord4
    (by
      intro x hx
      exact (affineGramMap4 ⟨x, hx⟩).2)
    (by
      intro x hx
      exact affineGramCoord4_hasSurjectiveComplexFDerivAt ⟨x, hx⟩)
  change Measure.QuasiMeasurePreserving affineGramMap4
    (coordinateAffineGenericMeasure 4 (by norm_num)) measureU4
  exact h

theorem measureU4_absolutelyContinuous_map_affineGramMap4 :
    measureU4 ≪ Measure.map affineGramMap4
      (coordinateAffineGenericMeasure 4 (by norm_num)) := by
  have h := absolutelyContinuous_map_normalizedOpenGaussian_of_surjective_submersion
    (affineCoordinateGaussian 4) coord4Gaussian
    (affineCoordinateGaussianPresentation 4) coord4GaussianPresentation
    (ProjectiveProbability.affineConfigFamily 4 (by norm_num)).goodSet
      (affineGoodSet_isOpen (by norm_num))
      (affineGoodSet_nonempty (by norm_num))
    u4Set isOpen_u4Set u4Set_nonempty
    affineGramCoord4
    (by
      intro x hx
      exact (affineGramMap4 ⟨x, hx⟩).2)
    (by
      intro q
      obtain ⟨z, hz⟩ := affineGramMap4_surjective q
      exact ⟨z, hz⟩)
    (by
      intro x hx
      exact affineGramCoord4_hasSurjectiveComplexFDerivAt ⟨x, hx⟩)
  exact h

noncomputable def affineGramMap5
    (z : AffineGeneric 5 (by norm_num)) : U5 :=
  ⟨affineGramCoord5 z.1, by
    rw [← orbitCoord5_affineGenericConfig_val z]
    exact (orbitCoord5 (affineGenericConfig z)).2⟩

@[simp] theorem affineGramMap5_val (z : AffineGeneric 5 (by norm_num)) :
    (affineGramMap5 z).1 = affineGramCoord5 z.1 := rfl

theorem affineGramMap5_surjective : Function.Surjective affineGramMap5 := by
  intro q
  obtain ⟨z, hz⟩ := affineOrbitCoord5_surjective q
  refine ⟨z, ?_⟩
  apply Subtype.ext
  rw [affineGramMap5_val, ← orbitCoord5_affineGenericConfig_val]
  exact congrArg Subtype.val hz

theorem affineGramMap5_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving affineGramMap5
      (coordinateAffineGenericMeasure 5 (by norm_num)) measureU5 := by
  have h := quasiMeasurePreserving_normalizedOpenGaussian_of_submersion
    (affineCoordinateGaussian 5) coord5Gaussian
    (affineCoordinateGaussianPresentation 5) coord5GaussianPresentation
    (ProjectiveProbability.affineConfigFamily 5 (by norm_num)).goodSet
      (affineGoodSet_isOpen (by norm_num))
      (affineGoodSet_nonempty (by norm_num))
    u5Set isOpen_u5Set u5Set_nonempty
    affineGramCoord5
    (by
      intro x hx
      exact (affineGramMap5 ⟨x, hx⟩).2)
    (by
      intro x hx
      exact affineGramCoord5_hasSurjectiveComplexFDerivAt ⟨x, hx⟩)
  change Measure.QuasiMeasurePreserving affineGramMap5
    (coordinateAffineGenericMeasure 5 (by norm_num)) measureU5
  exact h

theorem measureU5_absolutelyContinuous_map_affineGramMap5 :
    measureU5 ≪ Measure.map affineGramMap5
      (coordinateAffineGenericMeasure 5 (by norm_num)) := by
  have h := absolutelyContinuous_map_normalizedOpenGaussian_of_surjective_submersion
    (affineCoordinateGaussian 5) coord5Gaussian
    (affineCoordinateGaussianPresentation 5) coord5GaussianPresentation
    (ProjectiveProbability.affineConfigFamily 5 (by norm_num)).goodSet
      (affineGoodSet_isOpen (by norm_num))
      (affineGoodSet_nonempty (by norm_num))
    u5Set isOpen_u5Set u5Set_nonempty
    affineGramCoord5
    (by
      intro x hx
      exact (affineGramMap5 ⟨x, hx⟩).2)
    (by
      intro q
      obtain ⟨z, hz⟩ := affineGramMap5_surjective q
      exact ⟨z, hz⟩)
    (by
      intro x hx
      exact affineGramCoord5_hasSurjectiveComplexFDerivAt ⟨x, hx⟩)
  exact h

noncomputable def affineGramChartMap6
    (z : AffineGeneric 6 (by norm_num)) : U6Chart :=
  ⟨affineGramChartCoord6 z.1, by
    have h := dropR_mem_u6ChartSet (orbitCoord6 (affineGenericConfig z))
    simpa [affineGramChartCoord6, orbitCoord6_affineGenericConfig_val z] using h⟩

@[simp] theorem affineGramChartMap6_val
    (z : AffineGeneric 6 (by norm_num)) :
    (affineGramChartMap6 z).1 = affineGramChartCoord6 z.1 := rfl

theorem affineGramChartMap6_surjective :
    Function.Surjective affineGramChartMap6 := by
  intro p
  obtain ⟨z, hz⟩ := affineOrbitCoord6_surjective (chartToU6 p)
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change dropR (affineGramCoord6 z.1) = p.1
  rw [← orbitCoord6_affineGenericConfig_val z]
  change orbitCoord6 (affineGenericConfig z) = chartToU6 p at hz
  rw [hz]
  exact dropR_chartCoord6 p.1

theorem affineGramChartMap6_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving affineGramChartMap6
      (coordinateAffineGenericMeasure 6 (by norm_num)) measureU6Chart := by
  have h := quasiMeasurePreserving_normalizedOpenGaussian_of_submersion
    (affineCoordinateGaussian 6) coord8Gaussian
    (affineCoordinateGaussianPresentation 6) coord8GaussianPresentation
    (ProjectiveProbability.affineConfigFamily 6 (by norm_num)).goodSet
      (affineGoodSet_isOpen (by norm_num))
      (affineGoodSet_nonempty (by norm_num))
    u6ChartSet isOpen_u6ChartSet u6ChartSet_nonempty
    affineGramChartCoord6
    (by
      intro x hx
      exact (affineGramChartMap6 ⟨x, hx⟩).2)
    (by
      intro x hx
      exact affineGramChartCoord6_hasSurjectiveComplexFDerivAt ⟨x, hx⟩)
  change Measure.QuasiMeasurePreserving affineGramChartMap6
    (coordinateAffineGenericMeasure 6 (by norm_num)) measureU6Chart
  exact h

theorem measureU6Chart_absolutelyContinuous_map_affineGramChartMap6 :
    measureU6Chart ≪ Measure.map affineGramChartMap6
      (coordinateAffineGenericMeasure 6 (by norm_num)) := by
  have h := absolutelyContinuous_map_normalizedOpenGaussian_of_surjective_submersion
    (affineCoordinateGaussian 6) coord8Gaussian
    (affineCoordinateGaussianPresentation 6) coord8GaussianPresentation
    (ProjectiveProbability.affineConfigFamily 6 (by norm_num)).goodSet
      (affineGoodSet_isOpen (by norm_num))
      (affineGoodSet_nonempty (by norm_num))
    u6ChartSet isOpen_u6ChartSet u6ChartSet_nonempty
    affineGramChartCoord6
    (by
      intro x hx
      exact (affineGramChartMap6 ⟨x, hx⟩).2)
    (by
      intro p
      obtain ⟨z, hz⟩ := affineGramChartMap6_surjective p
      exact ⟨z, hz⟩)
    (by
      intro x hx
      exact affineGramChartCoord6_hasSurjectiveComplexFDerivAt ⟨x, hx⟩)
  exact h

/-! ## The natural projective measure on the generic subtype -/

theorem measurable_affineGenericConfig {n : ℕ} {h4 : 4 ≤ n} :
    Measurable (@affineGenericConfig n h4) := by
  apply Measurable.subtype_mk
  exact (ProjectiveProbability.measurable_affineTuple n).comp measurable_subtype_coe

/-- The restriction of the affine-chart representative of the natural
projective product measure to the generic locus. -/
noncomputable def naturalGenericMeasure (n : ℕ) (h4 : 4 ≤ n) :
    Measure (GenericConfig n) :=
  Measure.map affineGenericConfig (naturalAffineGenericMeasure n h4)

instance naturalGenericMeasure_isProbability (n : ℕ) (h4 : 4 ≤ n) :
    IsProbabilityMeasure (naturalGenericMeasure n h4) := by
  apply Measure.isProbabilityMeasure_map
  exact measurable_affineGenericConfig.aemeasurable

/-- A Euclidean Gaussian representative of the same measure class. -/
noncomputable def coordinateGenericMeasure (n : ℕ) (h4 : 4 ≤ n) :
    Measure (GenericConfig n) :=
  Measure.map affineGenericConfig (coordinateAffineGenericMeasure n h4)

theorem naturalGenericMeasure_absolutelyContinuous_coordinate
    (n : ℕ) (h4 : 4 ≤ n) :
    naturalGenericMeasure n h4 ≪ coordinateGenericMeasure n h4 := by
  exact (naturalAffineGenericMeasure_absolutelyContinuous_coordinate n h4).map
    measurable_affineGenericConfig

theorem coordinateGenericMeasure_absolutelyContinuous_natural
    (n : ℕ) (h4 : 4 ≤ n) :
    coordinateGenericMeasure n h4 ≪ naturalGenericMeasure n h4 := by
  exact (coordinateAffineGenericMeasure_absolutelyContinuous_natural n h4).map
    measurable_affineGenericConfig

theorem map_genericVal_naturalGenericMeasure_absolutelyContinuous_tuple
    (n : ℕ) (h4 : 4 ≤ n) :
    Measure.map (Subtype.val : GenericConfig n → ProjectiveConfig n)
        (naturalGenericMeasure n h4) ≪
      MeasurableRows.tupleMeasure ProjectiveProbability.measureProjective n := by
  rw [naturalGenericMeasure,
    Measure.map_map measurable_subtype_coe measurable_affineGenericConfig,
    ProjectiveProbability.tupleMeasure_measureProjective]
  have h := (map_val_naturalAffineGenericMeasure_absolutelyContinuous_source
    n h4).map (ProjectiveProbability.measurable_affineTuple n)
  rw [Measure.map_map (ProjectiveProbability.measurable_affineTuple n)
    measurable_subtype_coe] at h
  convert h using 1 <;> congr 1 <;> funext z <;> rfl

theorem tuple_absolutelyContinuous_map_genericVal_naturalGenericMeasure
    (n : ℕ) (h4 : 4 ≤ n) :
    MeasurableRows.tupleMeasure ProjectiveProbability.measureProjective n ≪
      Measure.map (Subtype.val : GenericConfig n → ProjectiveConfig n)
        (naturalGenericMeasure n h4) := by
  rw [naturalGenericMeasure,
    Measure.map_map measurable_subtype_coe measurable_affineGenericConfig,
    ProjectiveProbability.tupleMeasure_measureProjective]
  have h := (source_absolutelyContinuous_map_val_naturalAffineGenericMeasure
    n h4).map (ProjectiveProbability.measurable_affineTuple n)
  rw [Measure.map_map (ProjectiveProbability.measurable_affineTuple n)
    measurable_subtype_coe] at h
  convert h using 1 <;> congr 1 <;> funext z <;> rfl

theorem measurable_orbitCoord4 : Measurable orbitCoord4 := by
  rw [show orbitCoord4 = Prod.snd ∘ orbitProductMeasurableEquiv4.symm by
    funext x
    exact (orbitProductMeasurableEquiv4_symm_snd x).symm]
  exact measurable_snd.comp orbitProductMeasurableEquiv4.symm.measurable

theorem measurable_orbitCoord5 : Measurable orbitCoord5 := by
  rw [show orbitCoord5 = Prod.snd ∘ orbitProductMeasurableEquiv5.symm by
    funext x
    exact (orbitProductMeasurableEquiv5_symm_snd x).symm]
  exact measurable_snd.comp orbitProductMeasurableEquiv5.symm.measurable

theorem measurable_orbitCoord6 : Measurable orbitCoord6 := by
  rw [show orbitCoord6 = Prod.snd ∘ orbitProductMeasurableEquiv6.symm by
    funext x
    exact (orbitProductMeasurableEquiv6_symm_snd x).symm]
  exact measurable_snd.comp orbitProductMeasurableEquiv6.symm.measurable

theorem map_orbitCoord4_coordinateGenericMeasure :
    Measure.map orbitCoord4 (coordinateGenericMeasure 4 (by norm_num)) =
      Measure.map affineGramMap4
        (coordinateAffineGenericMeasure 4 (by norm_num)) := by
  rw [coordinateGenericMeasure, Measure.map_map measurable_orbitCoord4
    measurable_affineGenericConfig]
  congr 1
  funext z
  apply Subtype.ext
  exact orbitCoord4_affineGenericConfig_val z

theorem map_orbitCoord5_coordinateGenericMeasure :
    Measure.map orbitCoord5 (coordinateGenericMeasure 5 (by norm_num)) =
      Measure.map affineGramMap5
        (coordinateAffineGenericMeasure 5 (by norm_num)) := by
  rw [coordinateGenericMeasure, Measure.map_map measurable_orbitCoord5
    measurable_affineGenericConfig]
  congr 1
  funext z
  apply Subtype.ext
  exact orbitCoord5_affineGenericConfig_val z

theorem orbitCoord6_affineGenericConfig_eq_chartToU6
    (z : AffineGeneric 6 (by norm_num)) :
    orbitCoord6 (affineGenericConfig z) = chartToU6 (affineGramChartMap6 z) := by
  apply Subtype.ext
  rw [orbitCoord6_affineGenericConfig_val]
  change affineGramCoord6 z.1 = chartCoord6 (affineGramChartMap6 z).1
  rw [affineGramChartMap6_val]
  change affineGramCoord6 z.1 = chartCoord6 (dropR (affineGramCoord6 z.1))
  rw [← orbitCoord6_affineGenericConfig_val z]
  exact (chartCoord6_dropR (orbitCoord6 (affineGenericConfig z))).symm

theorem map_orbitCoord6_coordinateGenericMeasure :
    Measure.map orbitCoord6 (coordinateGenericMeasure 6 (by norm_num)) =
      Measure.map chartToU6 (Measure.map affineGramChartMap6
        (coordinateAffineGenericMeasure 6 (by norm_num))) := by
  rw [coordinateGenericMeasure, Measure.map_map measurable_orbitCoord6
    measurable_affineGenericConfig]
  rw [Measure.map_map continuous_chartToU6.measurable
    affineGramChartMap6_quasiMeasurePreserving.measurable]
  congr 1
  funext z
  exact orbitCoord6_affineGenericConfig_eq_chartToU6 z

theorem map_orbitCoord4_naturalGenericMeasure_absolutelyContinuous_measureU4 :
    Measure.map orbitCoord4 (naturalGenericMeasure 4 (by norm_num)) ≪ measureU4 := by
  exact ((naturalGenericMeasure_absolutelyContinuous_coordinate 4 (by norm_num)).map
    measurable_orbitCoord4).trans (by
      rw [map_orbitCoord4_coordinateGenericMeasure]
      exact affineGramMap4_quasiMeasurePreserving.absolutelyContinuous)

theorem measureU4_absolutelyContinuous_map_orbitCoord4_naturalGenericMeasure :
    measureU4 ≪ Measure.map orbitCoord4
      (naturalGenericMeasure 4 (by norm_num)) := by
  rw [naturalGenericMeasure, Measure.map_map measurable_orbitCoord4
    measurable_affineGenericConfig]
  have hcoord := measureU4_absolutelyContinuous_map_affineGramMap4
  have hnat := (coordinateAffineGenericMeasure_absolutelyContinuous_natural
    4 (by norm_num)).map (by
      exact affineGramMap4_quasiMeasurePreserving.measurable)
  apply hcoord.trans
  convert hnat using 1 <;> congr 1 <;> funext z <;> apply Subtype.ext
  exact orbitCoord4_affineGenericConfig_val z

theorem map_orbitCoord5_naturalGenericMeasure_absolutelyContinuous_measureU5 :
    Measure.map orbitCoord5 (naturalGenericMeasure 5 (by norm_num)) ≪ measureU5 := by
  exact ((naturalGenericMeasure_absolutelyContinuous_coordinate 5 (by norm_num)).map
    measurable_orbitCoord5).trans (by
      rw [map_orbitCoord5_coordinateGenericMeasure]
      exact affineGramMap5_quasiMeasurePreserving.absolutelyContinuous)

theorem measureU5_absolutelyContinuous_map_orbitCoord5_naturalGenericMeasure :
    measureU5 ≪ Measure.map orbitCoord5
      (naturalGenericMeasure 5 (by norm_num)) := by
  rw [naturalGenericMeasure, Measure.map_map measurable_orbitCoord5
    measurable_affineGenericConfig]
  have hcoord := measureU5_absolutelyContinuous_map_affineGramMap5
  have hnat := (coordinateAffineGenericMeasure_absolutelyContinuous_natural
    5 (by norm_num)).map (by
      exact affineGramMap5_quasiMeasurePreserving.measurable)
  apply hcoord.trans
  convert hnat using 1 <;> congr 1 <;> funext z <;> apply Subtype.ext
  exact orbitCoord5_affineGenericConfig_val z

theorem map_orbitCoord6_naturalGenericMeasure_absolutelyContinuous_measureU6 :
    Measure.map orbitCoord6 (naturalGenericMeasure 6 (by norm_num)) ≪ measureU6 := by
  apply ((naturalGenericMeasure_absolutelyContinuous_coordinate 6
    (by norm_num)).map measurable_orbitCoord6).trans
  rw [map_orbitCoord6_coordinateGenericMeasure, measureU6]
  exact affineGramChartMap6_quasiMeasurePreserving.absolutelyContinuous.map
    continuous_chartToU6.measurable

theorem measureU6_absolutelyContinuous_map_orbitCoord6_naturalGenericMeasure :
    measureU6 ≪ Measure.map orbitCoord6
      (naturalGenericMeasure 6 (by norm_num)) := by
  rw [measureU6, naturalGenericMeasure,
    Measure.map_map measurable_orbitCoord6 measurable_affineGenericConfig]
  have hchart := measureU6Chart_absolutelyContinuous_map_affineGramChartMap6
  have hnat := (coordinateAffineGenericMeasure_absolutelyContinuous_natural
    6 (by norm_num)).map affineGramChartMap6_quasiMeasurePreserving.measurable
  have hmap := hchart.trans hnat
  have hmap' := hmap.map continuous_chartToU6.measurable
  rw [Measure.map_map continuous_chartToU6.measurable
    affineGramChartMap6_quasiMeasurePreserving.measurable] at hmap'
  convert hmap' using 1 <;> congr 1 <;> funext z
  exact orbitCoord6_affineGenericConfig_eq_chartToU6 z

theorem measureProjective_eq_projectiveGaussian :
    ProjectiveProbability.measureProjective =
      ProjectiveGaussian.measureProjective := by
  rfl

theorem symplectic_smul_measureProjective_quasiMeasurePreserving
    (g : SymplecticGroup) :
    Measure.QuasiMeasurePreserving (fun p : ProjectivePoint => g • p)
      ProjectiveProbability.measureProjective
      ProjectiveProbability.measureProjective := by
  rw [measureProjective_eq_projectiveGaussian]
  convert projectiveGaussian_linearEquiv_quasiMeasurePreserving g.1 using 1
  funext p
  induction p using Projectivization.ind with
  | h v hv => rfl

theorem symplectic_smul_projectiveConfig_quasiMeasurePreserving
    (n : ℕ) (g : SymplecticGroup) :
    Measure.QuasiMeasurePreserving
      (fun x : ProjectiveConfig n => g • x)
      (MeasurableRows.tupleMeasure ProjectiveProbability.measureProjective n)
      (MeasurableRows.tupleMeasure ProjectiveProbability.measureProjective n) := by
  let hpoint := symplectic_smul_measureProjective_quasiMeasurePreserving g
  refine ⟨?_, ?_⟩
  · apply measurable_pi_lambda
    intro i
    exact hpoint.measurable.comp (measurable_pi_apply i)
  · rw [MeasurableRows.tupleMeasure]
    rw [show (fun x : ProjectiveConfig n => g • x) =
        (fun x i => g • x i) by
      funext x i
      rfl]
    rw [Measure.pi_map_pi (fun _ => hpoint.measurable.aemeasurable)]
    exact Measure.piFin_absolutelyContinuous _ _
      hpoint.absolutelyContinuous n

theorem absolutelyContinuous_of_map_measurableEmbedding
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {f : A → B} (hf : MeasurableEmbedding f) {mu nu : Measure A}
    (h : Measure.map f mu ≪ Measure.map f nu) : mu ≪ nu := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hnull
  have himage : MeasurableSet (f '' s) := hf.measurableSet_image' hs
  have hmapNull : Measure.map f nu (f '' s) = 0 := by
    rw [Measure.map_apply hf.measurable himage]
    simpa only [hf.injective.preimage_image] using hnull
  have := h hmapNull
  rw [Measure.map_apply hf.measurable himage] at this
  simpa only [hf.injective.preimage_image] using this

theorem symplectic_smul_naturalGenericMeasure_quasiMeasurePreserving
    {n : ℕ} (h4 : 4 ≤ n)
    (hemb : MeasurableEmbedding
      (Subtype.val : GenericConfig n → ProjectiveConfig n))
    (g : SymplecticGroup) :
    Measure.QuasiMeasurePreserving (smulGeneric g)
      (naturalGenericMeasure n h4) (naturalGenericMeasure n h4) := by
  let ambient := MeasurableRows.tupleMeasure
    ProjectiveProbability.measureProjective n
  let mu := naturalGenericMeasure n h4
  let i : GenericConfig n → ProjectiveConfig n := Subtype.val
  let F : ProjectiveConfig n → ProjectiveConfig n := fun x => g • x
  let f : GenericConfig n → GenericConfig n := smulGeneric g
  have hF := symplectic_smul_projectiveConfig_quasiMeasurePreserving n g
  have hf : Measurable f := by
    apply Measurable.subtype_mk
    exact hF.measurable.comp measurable_subtype_coe
  refine ⟨hf, ?_⟩
  have h₁ : Measure.map F (Measure.map i mu) ≪ Measure.map F ambient :=
    (map_genericVal_naturalGenericMeasure_absolutelyContinuous_tuple
      n h4).map hF.measurable
  have h₂ : Measure.map F ambient ≪ ambient := hF.absolutelyContinuous
  have h₃ : ambient ≪ Measure.map i mu :=
    tuple_absolutelyContinuous_map_genericVal_naturalGenericMeasure n h4
  have hImage : Measure.map i (Measure.map f mu) ≪ Measure.map i mu := by
    rw [Measure.map_map hemb.measurable hf]
    rw [Measure.map_map hF.measurable hemb.measurable] at h₁
    have hchain := h₁.trans (h₂.trans h₃)
    convert hchain using 1
    congr 1
  exact absolutelyContinuous_of_map_measurableEmbedding hemb hImage

theorem effective_smul_naturalGenericMeasure4_quasiMeasurePreserving
    (a : EffectiveSymplecticGroup) :
    Measure.QuasiMeasurePreserving (fun x : GenericConfig 4 => a • x)
      (naturalGenericMeasure 4 (by norm_num))
      (naturalGenericMeasure 4 (by norm_num)) := by
  induction a using Quotient.inductionOn' with
  | _ g =>
      exact symplectic_smul_naturalGenericMeasure_quasiMeasurePreserving
        (by norm_num)
        (measurable_subtype_coe.measurableEmbedding Subtype.val_injective) g

theorem effective_smul_naturalGenericMeasure5_quasiMeasurePreserving
    (a : EffectiveSymplecticGroup) :
    Measure.QuasiMeasurePreserving (fun x : GenericConfig 5 => a • x)
      (naturalGenericMeasure 5 (by norm_num))
      (naturalGenericMeasure 5 (by norm_num)) := by
  induction a using Quotient.inductionOn' with
  | _ g =>
      exact symplectic_smul_naturalGenericMeasure_quasiMeasurePreserving
        (by norm_num)
        (measurable_subtype_coe.measurableEmbedding Subtype.val_injective) g

theorem effective_smul_naturalGenericMeasure6_quasiMeasurePreserving
    (a : EffectiveSymplecticGroup) :
    Measure.QuasiMeasurePreserving (fun x : GenericConfig 6 => a • x)
      (naturalGenericMeasure 6 (by norm_num))
      (naturalGenericMeasure 6 (by norm_num)) := by
  induction a using Quotient.inductionOn' with
  | _ g =>
      exact symplectic_smul_naturalGenericMeasure_quasiMeasurePreserving
        (by norm_num)
        (measurable_subtype_coe.measurableEmbedding Subtype.val_injective) g

noncomputable def naturalOrbitPull4 :
    Measure (EffectiveSymplecticGroup × U4) :=
  Measure.map orbitProductMeasurableEquiv4.symm
    (naturalGenericMeasure 4 (by norm_num))

instance naturalOrbitPull4_isProbability :
    IsProbabilityMeasure naturalOrbitPull4 := by
  apply Measure.isProbabilityMeasure_map
  exact orbitProductMeasurableEquiv4.symm.measurable.aemeasurable

theorem orbitProductNaturalMeasurePreserving4 :
    MeasurePreserving orbitProductMeasurableEquiv4 naturalOrbitPull4
      (naturalGenericMeasure 4 (by norm_num)) := by
  refine ⟨orbitProductMeasurableEquiv4.measurable, ?_⟩
  simp [naturalOrbitPull4]

theorem orbitProductNaturalMeasurePreserving4_symm :
    MeasurePreserving orbitProductMeasurableEquiv4.symm
      (naturalGenericMeasure 4 (by norm_num)) naturalOrbitPull4 :=
  ⟨orbitProductMeasurableEquiv4.symm.measurable, rfl⟩

theorem leftProduct_naturalOrbitPull4_quasiMeasurePreserving
    (a : EffectiveSymplecticGroup) :
    Measure.QuasiMeasurePreserving
      (fun p : EffectiveSymplecticGroup × U4 => (a * p.1, p.2))
      naturalOrbitPull4 naturalOrbitPull4 := by
  have h := orbitProductNaturalMeasurePreserving4_symm.quasiMeasurePreserving.comp
    ((effective_smul_naturalGenericMeasure4_quasiMeasurePreserving a).comp
      orbitProductNaturalMeasurePreserving4.quasiMeasurePreserving)
  convert h using 1
  funext p
  apply orbitProductMeasurableEquiv4.injective
  change orbitProductMeasurableEquiv4 (a * p.1, p.2) =
    orbitProductMeasurableEquiv4
      (orbitProductMeasurableEquiv4.symm (a • orbitProductMeasurableEquiv4 p))
  rw [orbitProductMeasurableEquiv4.apply_symm_apply]
  exact (effective_smul_orbitProductEquiv4 a p.1 p.2).symm

theorem map_snd_naturalOrbitPull4 :
    Measure.map Prod.snd naturalOrbitPull4 =
      Measure.map orbitCoord4 (naturalGenericMeasure 4 (by norm_num)) := by
  rw [naturalOrbitPull4, Measure.map_map measurable_snd
    orbitProductMeasurableEquiv4.symm.measurable]
  congr 1
  funext x
  exact orbitProductMeasurableEquiv4_symm_snd x

theorem naturalGenericMeasure4_absolutelyContinuous_measureGeneric4 :
    naturalGenericMeasure 4 (by norm_num) ≪ measureGeneric4 := by
  have h := measure_equivalent_haar_prod_of_left_quasiInvariant
    naturalOrbitPull4 measureU4
    leftProduct_naturalOrbitPull4_quasiMeasurePreserving
    (by
      rw [map_snd_naturalOrbitPull4]
      exact map_orbitCoord4_naturalGenericMeasure_absolutelyContinuous_measureU4)
    (by
      rw [map_snd_naturalOrbitPull4]
      exact measureU4_absolutelyContinuous_map_orbitCoord4_naturalGenericMeasure)
  have hmap := h.1.map orbitProductMeasurableEquiv4.measurable
  simpa [measureGeneric4, naturalOrbitPull4] using hmap

theorem measureGeneric4_absolutelyContinuous_naturalGenericMeasure4 :
    measureGeneric4 ≪ naturalGenericMeasure 4 (by norm_num) := by
  have h := measure_equivalent_haar_prod_of_left_quasiInvariant
    naturalOrbitPull4 measureU4
    leftProduct_naturalOrbitPull4_quasiMeasurePreserving
    (by
      rw [map_snd_naturalOrbitPull4]
      exact map_orbitCoord4_naturalGenericMeasure_absolutelyContinuous_measureU4)
    (by
      rw [map_snd_naturalOrbitPull4]
      exact measureU4_absolutelyContinuous_map_orbitCoord4_naturalGenericMeasure)
  have hmap := h.2.map orbitProductMeasurableEquiv4.measurable
  simpa [measureGeneric4, naturalOrbitPull4] using hmap

noncomputable def naturalOrbitPull5 :
    Measure (EffectiveSymplecticGroup × U5) :=
  Measure.map orbitProductMeasurableEquiv5.symm
    (naturalGenericMeasure 5 (by norm_num))

instance naturalOrbitPull5_isProbability :
    IsProbabilityMeasure naturalOrbitPull5 := by
  apply Measure.isProbabilityMeasure_map
  exact orbitProductMeasurableEquiv5.symm.measurable.aemeasurable

theorem orbitProductNaturalMeasurePreserving5 :
    MeasurePreserving orbitProductMeasurableEquiv5 naturalOrbitPull5
      (naturalGenericMeasure 5 (by norm_num)) := by
  refine ⟨orbitProductMeasurableEquiv5.measurable, ?_⟩
  simp [naturalOrbitPull5]

theorem orbitProductNaturalMeasurePreserving5_symm :
    MeasurePreserving orbitProductMeasurableEquiv5.symm
      (naturalGenericMeasure 5 (by norm_num)) naturalOrbitPull5 :=
  ⟨orbitProductMeasurableEquiv5.symm.measurable, rfl⟩

theorem leftProduct_naturalOrbitPull5_quasiMeasurePreserving
    (a : EffectiveSymplecticGroup) :
    Measure.QuasiMeasurePreserving
      (fun p : EffectiveSymplecticGroup × U5 => (a * p.1, p.2))
      naturalOrbitPull5 naturalOrbitPull5 := by
  have h := orbitProductNaturalMeasurePreserving5_symm.quasiMeasurePreserving.comp
    ((effective_smul_naturalGenericMeasure5_quasiMeasurePreserving a).comp
      orbitProductNaturalMeasurePreserving5.quasiMeasurePreserving)
  convert h using 1
  funext p
  apply orbitProductMeasurableEquiv5.injective
  change orbitProductMeasurableEquiv5 (a * p.1, p.2) =
    orbitProductMeasurableEquiv5
      (orbitProductMeasurableEquiv5.symm (a • orbitProductMeasurableEquiv5 p))
  rw [orbitProductMeasurableEquiv5.apply_symm_apply]
  exact (effective_smul_orbitProductEquiv5 a p.1 p.2).symm

theorem map_snd_naturalOrbitPull5 :
    Measure.map Prod.snd naturalOrbitPull5 =
      Measure.map orbitCoord5 (naturalGenericMeasure 5 (by norm_num)) := by
  rw [naturalOrbitPull5, Measure.map_map measurable_snd
    orbitProductMeasurableEquiv5.symm.measurable]
  congr 1
  funext x
  exact orbitProductMeasurableEquiv5_symm_snd x

theorem naturalGenericMeasure5_absolutelyContinuous_measureGeneric5 :
    naturalGenericMeasure 5 (by norm_num) ≪ measureGeneric5 := by
  have h := measure_equivalent_haar_prod_of_left_quasiInvariant
    naturalOrbitPull5 measureU5
    leftProduct_naturalOrbitPull5_quasiMeasurePreserving
    (by
      rw [map_snd_naturalOrbitPull5]
      exact map_orbitCoord5_naturalGenericMeasure_absolutelyContinuous_measureU5)
    (by
      rw [map_snd_naturalOrbitPull5]
      exact measureU5_absolutelyContinuous_map_orbitCoord5_naturalGenericMeasure)
  have hmap := h.1.map orbitProductMeasurableEquiv5.measurable
  simpa [measureGeneric5, naturalOrbitPull5] using hmap

theorem measureGeneric5_absolutelyContinuous_naturalGenericMeasure5 :
    measureGeneric5 ≪ naturalGenericMeasure 5 (by norm_num) := by
  have h := measure_equivalent_haar_prod_of_left_quasiInvariant
    naturalOrbitPull5 measureU5
    leftProduct_naturalOrbitPull5_quasiMeasurePreserving
    (by
      rw [map_snd_naturalOrbitPull5]
      exact map_orbitCoord5_naturalGenericMeasure_absolutelyContinuous_measureU5)
    (by
      rw [map_snd_naturalOrbitPull5]
      exact measureU5_absolutelyContinuous_map_orbitCoord5_naturalGenericMeasure)
  have hmap := h.2.map orbitProductMeasurableEquiv5.measurable
  simpa [measureGeneric5, naturalOrbitPull5] using hmap

noncomputable def naturalOrbitPull6 :
    Measure (EffectiveSymplecticGroup × U6) :=
  Measure.map orbitProductMeasurableEquiv6.symm
    (naturalGenericMeasure 6 (by norm_num))

instance naturalOrbitPull6_isProbability :
    IsProbabilityMeasure naturalOrbitPull6 := by
  apply Measure.isProbabilityMeasure_map
  exact orbitProductMeasurableEquiv6.symm.measurable.aemeasurable

theorem orbitProductNaturalMeasurePreserving6 :
    MeasurePreserving orbitProductMeasurableEquiv6 naturalOrbitPull6
      (naturalGenericMeasure 6 (by norm_num)) := by
  refine ⟨orbitProductMeasurableEquiv6.measurable, ?_⟩
  simp [naturalOrbitPull6]

theorem orbitProductNaturalMeasurePreserving6_symm :
    MeasurePreserving orbitProductMeasurableEquiv6.symm
      (naturalGenericMeasure 6 (by norm_num)) naturalOrbitPull6 :=
  ⟨orbitProductMeasurableEquiv6.symm.measurable, rfl⟩

theorem leftProduct_naturalOrbitPull6_quasiMeasurePreserving
    (a : EffectiveSymplecticGroup) :
    Measure.QuasiMeasurePreserving
      (fun p : EffectiveSymplecticGroup × U6 => (a * p.1, p.2))
      naturalOrbitPull6 naturalOrbitPull6 := by
  have h := orbitProductNaturalMeasurePreserving6_symm.quasiMeasurePreserving.comp
    ((effective_smul_naturalGenericMeasure6_quasiMeasurePreserving a).comp
      orbitProductNaturalMeasurePreserving6.quasiMeasurePreserving)
  convert h using 1
  funext p
  apply orbitProductMeasurableEquiv6.injective
  change orbitProductMeasurableEquiv6 (a * p.1, p.2) =
    orbitProductMeasurableEquiv6
      (orbitProductMeasurableEquiv6.symm (a • orbitProductMeasurableEquiv6 p))
  rw [orbitProductMeasurableEquiv6.apply_symm_apply]
  exact (effective_smul_orbitProductEquiv6 a p.1 p.2).symm

theorem map_snd_naturalOrbitPull6 :
    Measure.map Prod.snd naturalOrbitPull6 =
      Measure.map orbitCoord6 (naturalGenericMeasure 6 (by norm_num)) := by
  rw [naturalOrbitPull6, Measure.map_map measurable_snd
    orbitProductMeasurableEquiv6.symm.measurable]
  congr 1
  funext x
  exact orbitProductMeasurableEquiv6_symm_snd x

theorem naturalGenericMeasure6_absolutelyContinuous_measureGeneric6 :
    naturalGenericMeasure 6 (by norm_num) ≪ measureGeneric6 := by
  have h := measure_equivalent_haar_prod_of_left_quasiInvariant
    naturalOrbitPull6 measureU6
    leftProduct_naturalOrbitPull6_quasiMeasurePreserving
    (by
      rw [map_snd_naturalOrbitPull6]
      exact map_orbitCoord6_naturalGenericMeasure_absolutelyContinuous_measureU6)
    (by
      rw [map_snd_naturalOrbitPull6]
      exact measureU6_absolutelyContinuous_map_orbitCoord6_naturalGenericMeasure)
  have hmap := h.1.map orbitProductMeasurableEquiv6.measurable
  simpa [measureGeneric6, naturalOrbitPull6] using hmap

theorem measureGeneric6_absolutelyContinuous_naturalGenericMeasure6 :
    measureGeneric6 ≪ naturalGenericMeasure 6 (by norm_num) := by
  have h := measure_equivalent_haar_prod_of_left_quasiInvariant
    naturalOrbitPull6 measureU6
    leftProduct_naturalOrbitPull6_quasiMeasurePreserving
    (by
      rw [map_snd_naturalOrbitPull6]
      exact map_orbitCoord6_naturalGenericMeasure_absolutelyContinuous_measureU6)
    (by
      rw [map_snd_naturalOrbitPull6]
      exact measureU6_absolutelyContinuous_map_orbitCoord6_naturalGenericMeasure)
  have hmap := h.2.map orbitProductMeasurableEquiv6.measurable
  simpa [measureGeneric6, naturalOrbitPull6] using hmap

end ProjectiveMeasureClass
end Sp4
