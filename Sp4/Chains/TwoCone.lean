import Sp4.Chains.Presentation
import Sp4.Measure.FibreKernel
import Sp4.Symplectic.GenericApex

/-! Weighted face transport, two-cone diffusion, and the period inequality. -/

namespace Sp4

namespace MeasureChain

noncomputable section

open MeasureTheory Pfaffian AffineCocycle OrbitChain
open scoped BigOperators

/-! ## The simplicial cone, with all genericity evidence explicit -/

/-- Prepend a projective point to an ordered configuration. -/
def coneTuple {n : ℕ} (y : ProjectivePoint) (x : ProjectiveConfig n) :
    ProjectiveConfig (n + 1) :=
  Fin.cons y x

/-- Once the full cone is generic, each cone over a face of its base is
generic by deletion. -/
theorem coneTuple_delete_generic {n : ℕ} (y : ProjectivePoint)
    (x : ProjectiveConfig (n + 1))
    (h : IsGeneric (coneTuple y x)) (i : Fin (n + 1)) :
    IsGeneric (coneTuple y (FinTuple.delete i x)) := by
  have hd := h.delete i.succ
  have heq : FinTuple.delete i.succ (coneTuple y x) =
      coneTuple y (FinTuple.delete i x) := by
    exact Fin.cons_comp_succ_succAbove y x i
  rw [heq] at hd
  exact hd

/-- A cone is a generic configuration only after its apex has been chosen
away from the relevant bad algebraic locus.  The proof is therefore an
explicit argument rather than hidden partiality. -/
def coneConfig {n : ℕ} (y : ProjectivePoint)
    (x : GenericConfig n) (h : IsGeneric (coneTuple y x.1)) :
    GenericConfig (n + 1) :=
  ⟨coneTuple y x.1, h⟩

/-- Simultaneously transporting the apex and a permuted base preserves
genericity of the cone. -/
theorem coneTuple_smul_permute_generic {n : ℕ}
    (g : SymplecticGroup) (σ : Equiv.Perm (Fin n))
    (y : ProjectivePoint) (x : GenericConfig n)
    (h : IsGeneric (coneTuple y x.1)) :
    IsGeneric
      (coneTuple (g • y) (smulGeneric g (permuteGeneric σ x)).1) := by
  have hz :=
    (permuteGeneric (extendPermAt 0 σ) (coneConfig y x h)).2.smul g
  convert hz using 1
  funext i
  cases i using Fin.cases with
  | zero =>
      simp [coneTuple, coneConfig, smulGeneric, permuteGeneric,
        FinTuple.permute]
  | succ i =>
      have hext : extendPermAt (0 : Fin (n + 1)) σ i.succ =
          (σ i).succ := by
        simpa using extendPermAt_succAbove (0 : Fin (n + 1)) σ i
      simp [coneTuple, coneConfig, smulGeneric, permuteGeneric,
        FinTuple.permute, hext]

@[simp]
theorem face_zero_coneConfig {n : ℕ} (y : ProjectivePoint)
    (x : GenericConfig n) (h : IsGeneric (coneTuple y x.1)) :
    face 0 (coneConfig y x h) = x := by
  apply Subtype.ext
  funext i
  simp [face, coneConfig, coneTuple, FinTuple.delete]

@[simp]
theorem face_succ_coneConfig {n : ℕ} (y : ProjectivePoint)
    (x : GenericConfig (n + 1)) (h : IsGeneric (coneTuple y x.1))
    (i : Fin (n + 1))
    (hi : IsGeneric (coneTuple y (face i x).1)) :
    face i.succ (coneConfig y x h) = coneConfig y (face i x) hi := by
  apply Subtype.ext
  exact Fin.cons_comp_succ_succAbove y x.1 i

/-- Totalized cone on a raw generator: it is the geometric cone on the
generic locus and zero elsewhere.  Totalization makes a genuine linear map;
all uses below prove that the relevant branch is the generic one. -/
def rawConeGenerator (R : Type*) [CommRing R] {n : ℕ}
    (y : ProjectivePoint) (x : GenericConfig n) : OrbitChain.Raw R (n + 1) := by
  classical
  exact if h : IsGeneric (coneTuple y x.1) then
      OrbitChain.generator (coneConfig y x h)
    else 0

def rawConeMap (R : Type*) [CommRing R] (n : ℕ)
    (y : ProjectivePoint) :
    OrbitChain.Raw R n →ₗ[R] OrbitChain.Raw R (n + 1) :=
  Finsupp.linearCombination R (rawConeGenerator R y)

@[simp]
theorem rawConeMap_generator (R : Type*) [CommRing R] {n : ℕ}
    (y : ProjectivePoint) (x : GenericConfig n) :
    rawConeMap R n y (OrbitChain.generator x) =
      rawConeGenerator R y x := by
  simp [rawConeMap, OrbitChain.generator]

theorem rawConeMap_generator_of_generic
    (R : Type*) [CommRing R] {n : ℕ}
    (y : ProjectivePoint) (x : GenericConfig n)
    (h : IsGeneric (coneTuple y x.1)) :
    rawConeMap R n y (OrbitChain.generator x) =
      OrbitChain.generator (coneConfig y x h) := by
  rw [rawConeMap_generator]
  simp only [rawConeGenerator, dif_pos h]

/-- Raw generator form of the cone identity.  This is the version used by
the second cone, where cancellation must occur before taking orbit
coinvariants. -/
theorem rawCone_homotopy_generator
    (R : Type*) [CommRing R] {n : ℕ}
    (y : ProjectivePoint) (x : GenericConfig (n + 1))
    (h : IsGeneric (coneTuple y x.1))
    (hface : ∀ i : Fin (n + 1),
      IsGeneric (coneTuple y (face i x).1)) :
    OrbitChain.rawBoundary R (n + 1)
        (rawConeMap R (n + 1) y (OrbitChain.generator x)) +
      rawConeMap R n y
        (OrbitChain.rawBoundary R n (OrbitChain.generator x)) =
      OrbitChain.generator x := by
  rw [rawConeMap_generator_of_generic R y x h,
    OrbitChain.rawBoundary_generator, OrbitChain.rawBoundary_generator]
  simp only [OrbitChain.boundaryGenerator, map_sum, LinearMap.map_smul]
  simp_rw [rawConeMap_generator_of_generic R y (face _ x) (hface _)]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul]
  rw [show face 0 (coneConfig y x h) = x from
    face_zero_coneConfig y x h]
  calc
    OrbitChain.generator x +
        ∑ i : Fin (n + 1), (-1 : R) ^ i.succ.val •
          OrbitChain.generator (face i.succ (coneConfig y x h)) +
        ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
          OrbitChain.generator (coneConfig y (face i x) (hface i)) =
      OrbitChain.generator x +
        ∑ i : Fin (n + 1),
          ((-1 : R) ^ i.succ.val + (-1 : R) ^ i.val) •
            OrbitChain.generator
              (coneConfig y (face i x) (hface i)) := by
      rw [add_assoc]
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [show face i.succ (coneConfig y x h) =
        coneConfig y (face i x) (hface i) from
          face_succ_coneConfig y x h i (hface i)]
      rw [add_smul]
    _ = OrbitChain.generator x := by
      simp [Fin.val_succ, pow_succ]

/-- The raw cone homotopy identity for an explicitly indexed finite chain. -/
theorem rawCone_homotopy_finset
    (R : Type*) [CommRing R] {n : ℕ} {I : Type*}
    (s : Finset I) (c : I → R) (x : I → GenericConfig (n + 1))
    (y : ProjectivePoint)
    (h : ∀ a ∈ s, IsGeneric (coneTuple y (x a).1))
    (hface : ∀ a ∈ s, ∀ i : Fin (n + 1),
      IsGeneric (coneTuple y (face i (x a)).1)) :
    OrbitChain.rawBoundary R (n + 1)
        (rawConeMap R (n + 1) y
          (∑ a ∈ s, c a • OrbitChain.generator (x a))) +
      rawConeMap R n y
        (OrbitChain.rawBoundary R n
          (∑ a ∈ s, c a • OrbitChain.generator (x a))) =
      ∑ a ∈ s, c a • OrbitChain.generator (x a) := by
  simp only [map_sum, LinearMap.map_smul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← smul_add]
  rw [rawCone_homotopy_generator R y (x a) (h a ha) (hface a ha)]

/-- The pointwise simplicial cone identity, stated only when the cone over
the base and the cones over all faces are generic. -/
theorem boundary_coneConfig (R : Type*) [CommRing R] {n : ℕ}
    (y : ProjectivePoint) (x : GenericConfig (n + 1))
    (h : IsGeneric (coneTuple y x.1))
    (hface : ∀ i : Fin (n + 1),
      IsGeneric (coneTuple y (face i x).1)) :
    boundary R (n + 1) (ofConfig (R := R) (coneConfig y x h)) =
      ofConfig (R := R) x -
        ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
          ofConfig (R := R) (coneConfig y (face i x) (hface i)) := by
  rw [boundary_ofConfig, Fin.sum_univ_succ]
  rw [face_zero_coneConfig]
  simp only [Fin.val_zero, pow_zero, one_smul]
  calc
    ofConfig (R := R) x +
        ∑ i : Fin (n + 1), (-1 : R) ^ i.succ.val •
          ofConfig (R := R) (face i.succ (coneConfig y x h)) =
      ofConfig (R := R) x +
        ∑ i : Fin (n + 1), (-1 : R) ^ i.succ.val •
          ofConfig (R := R) (coneConfig y (face i x) (hface i)) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [face_succ_coneConfig]
    _ = _ := by
      simp_rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
      rw [Finset.sum_neg_distrib]
      rw [sub_eq_add_neg]

/-- All genericity data needed for coning an `(n+1)`-tuple and every one of
its faces. -/
structure ConeDatum (n : ℕ) where
  apex : ProjectivePoint
  base : GenericConfig (n + 1)
  cone_generic : IsGeneric (coneTuple apex base.1)
  face_generic : ∀ i : Fin (n + 1),
    IsGeneric (coneTuple apex (face i base).1)

namespace ConeDatum

def cone {n : ℕ} (d : ConeDatum n) : GenericConfig (n + 2) :=
  coneConfig d.apex d.base d.cone_generic

def sideFace {n : ℕ} (d : ConeDatum n) (i : Fin (n + 1)) :
    GenericConfig (n + 1) :=
  coneConfig d.apex (face i d.base) (d.face_generic i)

@[simp]
theorem face_succ_cone {n : ℕ} (d : ConeDatum n)
    (i : Fin (n + 1)) : face i.succ d.cone = d.sideFace i := by
  exact face_succ_coneConfig d.apex d.base d.cone_generic i
    (d.face_generic i)

def sideChain (R : Type*) [CommRing R] {n : ℕ} (d : ConeDatum n) :
    OrbitChain.Module R (n + 1) :=
  ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
    ofConfig (R := R) (d.sideFace i)

def rawSideChain (R : Type*) [CommRing R] {n : ℕ} (d : ConeDatum n) :
    OrbitChain.Raw R (n + 1) :=
  ∑ i : Fin (n + 1), (-1 : R) ^ i.val •
    OrbitChain.generator (d.sideFace i)

theorem boundary_cone (R : Type*) [CommRing R] {n : ℕ}
    (d : ConeDatum n) :
    boundary R (n + 1) (ofConfig (R := R) d.cone) =
      ofConfig (R := R) d.base - d.sideChain R := by
  exact boundary_coneConfig R d.apex d.base d.cone_generic d.face_generic

theorem rawBoundary_cone (R : Type*) [CommRing R] {n : ℕ}
    (d : ConeDatum n) :
    OrbitChain.rawBoundary R (n + 1) (OrbitChain.generator d.cone) =
      OrbitChain.generator d.base - d.rawSideChain R := by
  rw [OrbitChain.rawBoundary_generator, OrbitChain.boundaryGenerator,
    Fin.sum_univ_succ]
  rw [show face 0 d.cone = d.base from
    face_zero_coneConfig d.apex d.base d.cone_generic]
  simp only [Fin.val_zero, pow_zero, one_smul]
  calc
    OrbitChain.generator d.base +
        ∑ i : Fin (n + 1), (-1 : R) ^ i.succ.val •
          OrbitChain.generator (face i.succ d.cone) =
      OrbitChain.generator d.base +
        ∑ i : Fin (n + 1), (-1 : R) ^ i.succ.val •
          OrbitChain.generator (d.sideFace i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [show face i.succ d.cone = d.sideFace i from
        face_succ_coneConfig d.apex d.base d.cone_generic i
          (d.face_generic i)]
    _ = _ := by
      simp_rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
      rw [Finset.sum_neg_distrib, sub_eq_add_neg]
      rfl

/-- Transport data across one paired oriented face. -/
structure Transport {n : ℕ} (d e : ConeDatum n) where
  group : SymplecticGroup
  permutation : Equiv.Perm (Fin (n + 1))
  base_eq : e.base =
    smulGeneric group (permuteGeneric permutation d.base)
  apex_eq : e.apex = group • d.apex

/-- Reverse a face transport.  This is important for representing a paired
atom by two directed endpoints while choosing geometric data only once. -/
def Transport.symm {n : ℕ} {d e : ConeDatum n}
    (h : Transport d e) : Transport e d where
  group := h.group⁻¹
  permutation := h.permutation⁻¹
  base_eq := by
    rw [h.base_eq]
    apply Subtype.ext
    funext i
    simp [smulGeneric, permuteGeneric, FinTuple.permute, mul_smul]
  apex_eq := by
    rw [h.apex_eq]
    simp

theorem cone_eq_smul_permute {n : ℕ} {d e : ConeDatum n}
    (h : Transport d e) :
    e.cone = smulGeneric h.group
      (permuteGeneric (extendPermAt 0 h.permutation) d.cone) := by
  apply Subtype.ext
  funext i
  cases i using Fin.cases with
  | zero =>
      simp [cone, coneConfig, coneTuple, h.apex_eq, smulGeneric,
        permuteGeneric, FinTuple.permute]
  | succ i =>
      have hb := congrArg (fun z : GenericConfig (n + 1) ↦ z.1 i) h.base_eq
      have hext : extendPermAt (0 : Fin (n + 2)) h.permutation i.succ =
          (h.permutation i).succ := by
        simpa using extendPermAt_succAbove
          (0 : Fin (n + 2)) h.permutation i
      simp [cone, coneConfig, coneTuple, smulGeneric, permuteGeneric,
        FinTuple.permute, hext]
      exact hb

theorem ofConfig_cone_transport (R : Type*) [CommRing R]
    {n : ℕ} {d e : ConeDatum n} (h : Transport d e) :
    ofConfig (R := R) e.cone =
      permSign R h.permutation • ofConfig (R := R) d.cone := by
  rw [cone_eq_smul_permute h, ofConfig_smulGeneric,
    ofConfig_permuteGeneric, permSign_extendPermAt]

theorem ofConfig_base_transport (R : Type*) [CommRing R]
    {n : ℕ} {d e : ConeDatum n} (h : Transport d e) :
    ofConfig (R := R) e.base =
      permSign R h.permutation • ofConfig (R := R) d.base := by
  rw [h.base_eq, ofConfig_smulGeneric, ofConfig_permuteGeneric]

/-- Applying the cone identity to a transported cone proves compatibility of
the entire side boundary; no coherence around cycles of face pairings is
used. -/
theorem sideChain_transport (R : Type*) [CommRing R]
    {n : ℕ} {d e : ConeDatum n} (h : Transport d e) :
    e.sideChain R = permSign R h.permutation • d.sideChain R := by
  have hcone := congrArg (boundary R (n + 1))
    (ofConfig_cone_transport R h)
  rw [map_smul, boundary_cone R e, boundary_cone R d,
    ofConfig_base_transport R h, smul_sub] at hcone
  exact sub_right_injective hcone

end ConeDatum

/-! ## The first cone, indexed by weighted face atoms

The indexing below deliberately records a *raw* finite presentation.  A cone
with a fixed apex is not defined on orbit coinvariants, so it would be
incorrect to formulate the second cone directly on `OrbitChain.Module`.
Instead, orbit transport is used only to cancel paired first-cone terms after
projection to the quotient. -/

/-- Algebraic data produced by an orientation-correct weighted pairing of all
face occurrences in a finite five-point chain.

`I` indexes the parent facets and `A` indexes the refined face atoms.  The
coefficient of an atom already contains the incidence sign of its face. -/
structure FirstConeSystem (I A : Type*) [Fintype I] [Fintype A]
    [DecidableEq I] where
  facet : I → GenericConfig 5
  facetCoeff : I → ℝ
  parent : A → I
  faceIndex : A → Fin 5
  atomCoeff : A → ℝ
  first : A → ConeDatum 3
  base_eq : ∀ a,
    (first a).base = face (faceIndex a) (facet (parent a))
  boundary_refinement : ∀ s,
    (∑ a ∈ Finset.univ.filter (fun a : A ↦ parent a = s),
        atomCoeff a • OrbitChain.generator ((first a).base)) =
      OrbitChain.rawBoundary ℝ 4
        (facetCoeff s • OrbitChain.generator (facet s))
  mate : Equiv.Perm A
  mate_involutive : ∀ a, mate (mate a) = a
  mate_ne : ∀ a, mate a ≠ a
  transport : ∀ a, ConeDatum.Transport (first a) (first (mate a))
  coeff_transport : ∀ a,
    atomCoeff (mate a) * permSign ℝ (transport a).permutation =
      -atomCoeff a
  faceAtomMass : ∀ s i,
    (∑ a ∈ Finset.univ.filter
        (fun a : A ↦ parent a = s ∧ faceIndex a = i),
        |atomCoeff a|) = |facetCoeff s|

/-! ## Supplying first apices to an orientation-correct pairing -/

/-- A compatible apex choice for a weighted face pairing.  Genericity is
listed both for the first cone and for each of its four side faces, exactly
as required by the simplicial cone identity. -/
structure PairedApexChoice {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] (p : OrbitChain.WeightedFacetPresentation I)
    (d : OrbitChain.WeightedFacePairing p A) where
  apex : A → ProjectivePoint
  apex_transport : ∀ a,
    apex (d.mate a) = d.coherentGroup a • apex a
  cone_generic : ∀ a,
    IsGeneric (coneTuple (apex a) (p.faceBase (d.occurrence a)).1)
  face_generic : ∀ a (i : Fin 4),
    IsGeneric (coneTuple (apex a)
      (face i (p.faceBase (d.occurrence a))).1)

namespace PairedApexChoiceConstruction

variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
variable (p : OrbitChain.WeightedFacetPresentation I)
variable (d : OrbitChain.WeightedFacePairing p A)

/-- An independently chosen generic apex at each directed atom.  Only the
forward member of each mate pair will be used. -/
noncomputable def seedApex (a : A) : ProjectivePoint :=
  Classical.choose
    (exists_common_generic_cons
      (fun _ : Unit ↦ p.faceBase (d.occurrence a)) (by norm_num))

theorem seedApex_generic (a : A) :
    IsGeneric
      (coneTuple (seedApex p d a) (p.faceBase (d.occurrence a)).1) := by
  exact Classical.choose_spec
    (exists_common_generic_cons
      (fun _ : Unit ↦ p.faceBase (d.occurrence a)) (by norm_num)) ()

/-- Use the seed at the forward endpoint and transport it to the reverse
endpoint.  Thus each pair makes only one geometric choice. -/
noncomputable def pairedApex (a : A) : ProjectivePoint := by
  classical
  exact if d.pairForward a then seedApex p d a
    else d.coherentGroup (d.mate a) • seedApex p d (d.mate a)

theorem pairedApex_transport (a : A) :
    pairedApex p d (d.mate a) =
      d.coherentGroup a • pairedApex p d a := by
  classical
  by_cases h : d.pairForward a
  · have hm : ¬d.pairForward (d.mate a) :=
      (d.pairForward_ne_mate a).mp h
    simp [pairedApex, h, hm, d.mate_involutive]
  · have hm : d.pairForward (d.mate a) :=
      (d.pairForward_mate_iff a).mpr h
    rw [pairedApex, if_pos hm, pairedApex, if_neg h, smul_smul,
      d.coherentGroup_mate]
    simp

theorem pairedApex_cone_generic (a : A) :
    IsGeneric
      (coneTuple (pairedApex p d a)
        (p.faceBase (d.occurrence a)).1) := by
  classical
  by_cases h : d.pairForward a
  · simpa [pairedApex, h] using seedApex_generic p d a
  · have ht := coneTuple_smul_permute_generic
      (d.coherentGroup (d.mate a))
      (d.coherentPermutation (d.mate a))
      (seedApex p d (d.mate a))
      (p.faceBase (d.occurrence (d.mate a)))
      (seedApex_generic p d (d.mate a))
    have hbase := d.coherent_base_transport (d.mate a)
    rw [d.mate_involutive] at hbase
    rw [hbase]
    simpa [pairedApex, h] using ht

theorem pairedApex_face_generic (a : A) (i : Fin 4) :
    IsGeneric
      (coneTuple (pairedApex p d a)
        (face i (p.faceBase (d.occurrence a))).1) := by
  exact coneTuple_delete_generic _ _ (pairedApex_cone_generic p d a) i

/-- Every orientation-correct weighted face pairing admits a compatible
generic first-apex choice. -/
noncomputable def choice : PairedApexChoice p d where
  apex := pairedApex p d
  apex_transport := pairedApex_transport p d
  cone_generic := pairedApex_cone_generic p d
  face_generic := pairedApex_face_generic p d

end PairedApexChoiceConstruction

namespace PairedApexChoice

variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
variable {p : OrbitChain.WeightedFacetPresentation I}
variable {d : OrbitChain.WeightedFacePairing p A}

def firstCone (h : PairedApexChoice p d) (a : A) : ConeDatum 3 where
  apex := h.apex a
  base := p.faceBase (d.occurrence a)
  cone_generic := h.cone_generic a
  face_generic := h.face_generic a

def firstTransport (h : PairedApexChoice p d) (a : A) :
    ConeDatum.Transport (h.firstCone a) (h.firstCone (d.mate a)) where
  group := d.coherentGroup a
  permutation := d.coherentPermutation a
  base_eq := d.coherent_base_transport a
  apex_eq := h.apex_transport a

/-- Once compatible generic apices are supplied, the finite pairing
canonically becomes the complete algebraic first-cone system. -/
def toFirstConeSystem (h : PairedApexChoice p d) : FirstConeSystem I A where
  facet := p.facet
  facetCoeff := p.coeff
  parent := d.parent
  faceIndex := d.faceIndex
  atomCoeff := d.atomCoeff
  first := h.firstCone
  base_eq := fun a ↦ rfl
  boundary_refinement := by
    intro s
    convert p.paired_rawBoundary_refinement d s using 1 <;>
      simp [OrbitChain.WeightedFacePairing.parent,
        OrbitChain.WeightedFacePairing.faceIndex, firstCone]
    apply Finset.sum_congr
    · ext a
      constructor
      · exact fun ha ↦ Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
      · exact fun ha ↦ Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
    · intro a ha
      rfl
  mate := d.mate
  mate_involutive := d.mate_involutive
  mate_ne := d.mate_ne
  transport := h.firstTransport
  coeff_transport := d.coherent_coeff_transport
  faceAtomMass := by
    intro s i
    convert p.paired_faceAtomMass d s i using 1 <;>
      simp [OrbitChain.WeightedFacePairing.parent,
        OrbitChain.WeightedFacePairing.faceIndex]
    apply Finset.sum_congr
    · ext a
      constructor
      · exact fun ha ↦ Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
      · exact fun ha ↦ Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
    · intro a ha
      rfl

end PairedApexChoice

namespace FirstConeSystem

variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I]

/-- The atoms belonging to one parent facet. -/
def atomsOf (d : FirstConeSystem I A) (s : I) : Finset A := by
  classical
  exact Finset.univ.filter (fun a ↦ d.parent a = s)

/-- The selected raw presentation of one parent facet. -/
def rawFacet (d : FirstConeSystem I A) (s : I) : OrbitChain.Raw ℝ 5 :=
  d.facetCoeff s • OrbitChain.generator (d.facet s)

/-- First cones over all refined face atoms of a given facet. -/
def rawFirst (d : FirstConeSystem I A) (s : I) : OrbitChain.Raw ℝ 5 :=
  ∑ a ∈ d.atomsOf s,
    d.atomCoeff a • OrbitChain.generator (d.first a).cone

/-- The four side faces of every first cone over a given facet. -/
def rawSide (d : FirstConeSystem I A) (s : I) : OrbitChain.Raw ℝ 4 :=
  ∑ a ∈ d.atomsOf s, d.atomCoeff a • (d.first a).rawSideChain ℝ

/-- The chain left after subtracting the first cones from one facet. -/
def rawA (d : FirstConeSystem I A) (s : I) : OrbitChain.Raw ℝ 5 :=
  d.rawFacet s - d.rawFirst s

/-- The side boundary produced by the first cones over one facet. -/
def rawB (d : FirstConeSystem I A) (s : I) : OrbitChain.Raw ℝ 4 :=
  d.rawSide s

theorem rawBoundary_rawFirst (d : FirstConeSystem I A) (s : I) :
    OrbitChain.rawBoundary ℝ 4 (d.rawFirst s) =
      OrbitChain.rawBoundary ℝ 4 (d.rawFacet s) - d.rawSide s := by
  classical
  simp only [rawFirst, rawSide, map_sum, LinearMap.map_smul]
  simp_rw [ConeDatum.rawBoundary_cone, smul_sub]
  rw [Finset.sum_sub_distrib]
  have href := d.boundary_refinement s
  change (∑ a ∈ d.atomsOf s,
      d.atomCoeff a • OrbitChain.generator ((d.first a).base)) =
    OrbitChain.rawBoundary ℝ 4 (d.rawFacet s) at href
  rw [href]

/-- First-cone identity on the raw presentation of one facet. -/
theorem rawBoundary_rawA (d : FirstConeSystem I A) (s : I) :
    OrbitChain.rawBoundary ℝ 4 (d.rawA s) = d.rawB s := by
  rw [rawA, rawB, map_sub, d.rawBoundary_rawFirst]
  module

/-- The side chain is a raw cycle; this follows from the actual simplicial
identity, not from a quotient cancellation. -/
theorem rawBoundary_rawB (d : FirstConeSystem I A) (s : I) :
    OrbitChain.rawBoundary ℝ 3 (d.rawB s) = 0 := by
  have h := LinearMap.congr_fun (OrbitChain.rawBoundary_sq ℝ 3) (d.rawA s)
  change OrbitChain.rawBoundary ℝ 3
      (OrbitChain.rawBoundary ℝ 4 (d.rawA s)) = 0 at h
  rw [d.rawBoundary_rawA] at h
  exact h

/-- One paired pair of first cones cancels in alternating orbit chains. -/
theorem first_pair_cancel (d : FirstConeSystem I A) (a : A) :
    d.atomCoeff a • ofConfig (R := ℝ) (d.first a).cone +
      d.atomCoeff (d.mate a) •
        ofConfig (R := ℝ) (d.first (d.mate a)).cone = 0 := by
  rw [ConeDatum.ofConfig_cone_transport ℝ (d.transport a)]
  rw [smul_smul, d.coeff_transport]
  module

/-- One paired pair of complete first-cone side chains also cancels. -/
theorem side_pair_cancel (d : FirstConeSystem I A) (a : A) :
    d.atomCoeff a • (d.first a).sideChain ℝ +
      d.atomCoeff (d.mate a) •
        (d.first (d.mate a)).sideChain ℝ = 0 := by
  rw [ConeDatum.sideChain_transport ℝ (d.transport a)]
  rw [smul_smul, d.coeff_transport]
  module

/-- All first cones cancel pairwise after passing to orbit coinvariants. -/
theorem first_total_eq_zero (d : FirstConeSystem I A) :
    (∑ a : A, d.atomCoeff a •
      ofConfig (R := ℝ) (d.first a).cone) = 0 := by
  classical
  apply Finset.sum_involution (s := Finset.univ)
      (fun a _ ↦ d.mate a)
  · intro a _
    exact d.first_pair_cancel a
  · intro a _ _ hfix
    exact d.mate_ne a hfix
  · simp
  · intro a _
    exact d.mate_involutive a

/-- All first-cone side chains cancel pairwise in the orbit quotient. -/
theorem side_total_eq_zero (d : FirstConeSystem I A) :
    (∑ a : A, d.atomCoeff a • (d.first a).sideChain ℝ) = 0 := by
  classical
  apply Finset.sum_involution (s := Finset.univ)
      (fun a _ ↦ d.mate a)
  · intro a _
    exact d.side_pair_cancel a
  · intro a _ _ hfix
    exact d.mate_ne a hfix
  · simp
  · intro a _
    exact d.mate_involutive a

theorem mkQ_rawFacet (d : FirstConeSystem I A) (s : I) :
    (relations ℝ 5).mkQ (d.rawFacet s) =
      d.facetCoeff s • ofConfig (R := ℝ) (d.facet s) := by
  simp [rawFacet, ofConfig]

theorem mkQ_rawFirst (d : FirstConeSystem I A) (s : I) :
    (relations ℝ 5).mkQ (d.rawFirst s) =
      ∑ a ∈ d.atomsOf s,
        d.atomCoeff a • ofConfig (R := ℝ) (d.first a).cone := by
  simp [rawFirst, ofConfig]

theorem mkQ_rawSide (d : FirstConeSystem I A) (s : I) :
    (relations ℝ 4).mkQ (d.rawSide s) =
      ∑ a ∈ d.atomsOf s,
        d.atomCoeff a • (d.first a).sideChain ℝ := by
  simp [rawSide, ConeDatum.rawSideChain, ConeDatum.sideChain,
    ofConfig]

/-- Grouping atoms by their unique parent loses no terms. -/
theorem sum_over_parents {M : Type*} [AddCommMonoid M]
    (d : FirstConeSystem I A) (f : A → M) :
    (∑ s : I, ∑ a ∈ d.atomsOf s, f a) = ∑ a : A, f a := by
  classical
  simpa [atomsOf] using
    (Finset.sum_fiberwise (Finset.univ : Finset A) d.parent f)

/-- The sum of the displayed first cones vanishes in the quotient. -/
theorem sum_mkQ_rawFirst_eq_zero (d : FirstConeSystem I A) :
    (∑ s : I, (relations ℝ 5).mkQ (d.rawFirst s)) = 0 := by
  simp_rw [d.mkQ_rawFirst]
  rw [d.sum_over_parents]
  exact d.first_total_eq_zero

/-- The sum of all first-cone side chains vanishes in the quotient. -/
theorem sum_mkQ_rawSide_eq_zero (d : FirstConeSystem I A) :
    (∑ s : I, (relations ℝ 4).mkQ (d.rawSide s)) = 0 := by
  simp_rw [d.mkQ_rawSide]
  rw [d.sum_over_parents]
  exact d.side_total_eq_zero

end FirstConeSystem

/-! ## The second cone on the chosen raw presentation -/

/-- Genericity data for the second cone.  The conditions enumerate exactly
the generators of `rawA` and `rawB` and all faces needed by the simplicial
cone identity. -/
structure SecondConeSystem {I A : Type*} [Fintype I] [Fintype A]
    [DecidableEq I] (d : FirstConeSystem I A) where
  apex : I → ProjectivePoint
  facetCone_generic : ∀ s,
    IsGeneric (coneTuple (apex s) (d.facet s).1)
  facetFace_generic : ∀ s i,
    IsGeneric (coneTuple (apex s) (face i (d.facet s)).1)
  firstCone_generic : ∀ a,
    IsGeneric (coneTuple (apex (d.parent a)) (d.first a).cone.1)
  firstFace_generic : ∀ a i,
    IsGeneric
      (coneTuple (apex (d.parent a)) (face i (d.first a).cone).1)
  sideCone_generic : ∀ a j,
    IsGeneric
      (coneTuple (apex (d.parent a)) ((d.first a).sideFace j).1)
  sideFace_generic : ∀ a j i,
    IsGeneric
      (coneTuple (apex (d.parent a))
        (face i ((d.first a).sideFace j)).1)

namespace FirstConeSystem

variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I]
variable (d : FirstConeSystem I A)

/-- The finite family of five-configurations over which the second apex for
one parent must be simultaneously generic: the parent facet itself and all
first cones belonging to it. -/
abbrev BaseIndex (s : I) := Option {a : A // d.parent a = s}

def base (s : I) : d.BaseIndex s → GenericConfig 5
  | none => d.facet s
  | some a => (d.first a.1).cone

/-- A common second apex for all relevant five-configurations over one
parent facet. -/
noncomputable def apex (s : I) : ProjectivePoint :=
  Classical.choose (exists_common_generic_cons (d.base s) (by norm_num))

theorem apex_generic (s : I) (k : d.BaseIndex s) :
    IsGeneric (coneTuple (d.apex s) (d.base s k).1) := by
  exact Classical.choose_spec
    (exists_common_generic_cons (d.base s) (by norm_num)) k

theorem facetCone_generic (s : I) :
    IsGeneric (coneTuple (d.apex s) (d.facet s).1) := by
  exact d.apex_generic s none

theorem firstCone_generic (a : A) :
    IsGeneric
      (coneTuple (d.apex (d.parent a)) (d.first a).cone.1) := by
  exact d.apex_generic (d.parent a) (some ⟨a, rfl⟩)

theorem facetFace_generic (s : I) (i : Fin 5) :
    IsGeneric
      (coneTuple (d.apex s) (face i (d.facet s)).1) := by
  exact coneTuple_delete_generic _ _ (d.facetCone_generic s) i

theorem firstFace_generic (a : A) (i : Fin 5) :
    IsGeneric
      (coneTuple (d.apex (d.parent a)) (face i (d.first a).cone).1) := by
  exact coneTuple_delete_generic _ _ (d.firstCone_generic a) i

theorem sideCone_generic (a : A) (j : Fin 4) :
    IsGeneric
      (coneTuple (d.apex (d.parent a)) ((d.first a).sideFace j).1) := by
  simpa only [ConeDatum.face_succ_cone] using
    d.firstFace_generic a j.succ

theorem sideFace_generic (a : A) (j : Fin 4) (i : Fin 4) :
    IsGeneric
      (coneTuple (d.apex (d.parent a))
        (face i ((d.first a).sideFace j)).1) := by
  exact coneTuple_delete_generic _ _ (d.sideCone_generic a j) i

/-- The simultaneous finite-avoidance construction supplies every
genericity field of the second cone system. -/
noncomputable def choice : SecondConeSystem d where
  apex := d.apex
  facetCone_generic := d.facetCone_generic
  facetFace_generic := d.facetFace_generic
  firstCone_generic := d.firstCone_generic
  firstFace_generic := d.firstFace_generic
  sideCone_generic := d.sideCone_generic
  sideFace_generic := d.sideFace_generic

end FirstConeSystem

namespace SecondConeSystem

variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I]
variable {d : FirstConeSystem I A}

/-- The second cone over `A_s`, retained as a raw six-point chain. -/
def rawH (e : SecondConeSystem d) (s : I) : OrbitChain.Raw ℝ 6 :=
  rawConeMap ℝ 5 (e.apex s) (d.rawA s)

/-- The second cone over the raw side cycle `B_s`. -/
def rawS (e : SecondConeSystem d) (s : I) : OrbitChain.Raw ℝ 5 :=
  rawConeMap ℝ 4 (e.apex s) (d.rawB s)

/-- One displayed generator of the second-cone output. -/
def sideCone (e : SecondConeSystem d) (a : A) (j : Fin 4) :
    GenericConfig 5 :=
  coneConfig (e.apex (d.parent a)) ((d.first a).sideFace j)
    (e.sideCone_generic a j)

/-- Expand the raw second cone over one parent into its atom/side
generators. -/
theorem rawS_eq_sum_sideCone (e : SecondConeSystem d) (s : I) :
    e.rawS s =
      ∑ a ∈ d.atomsOf s, ∑ j : Fin 4,
        (d.atomCoeff a * (-1 : ℝ) ^ j.val) •
          OrbitChain.generator (e.sideCone a j) := by
  classical
  rw [rawS, FirstConeSystem.rawB, FirstConeSystem.rawSide]
  simp only [map_sum, LinearMap.map_smul, ConeDatum.rawSideChain,
    Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro j _hj
  rw [smul_smul]
  have hparent : d.parent a = s := (Finset.mem_filter.mp ha).2
  rw [← hparent]
  rw [rawConeMap_generator_of_generic ℝ
    (e.apex (d.parent a)) ((d.first a).sideFace j)
    (e.sideCone_generic a j)]
  rfl

/-- The original five-chain represented by the indexed facets. -/
def facetChain (e : SecondConeSystem d) : OrbitChain.Module ℝ 5 :=
  ∑ s : I, d.facetCoeff s • ofConfig (R := ℝ) (d.facet s)

/-- The output five-cycle of the two-cone construction. -/
def secondChain (e : SecondConeSystem d) : OrbitChain.Module ℝ 5 :=
  ∑ s : I, (relations ℝ 5).mkQ (e.rawS s)

/-- The six-chain witnessing homology between the input and output chains. -/
def homotopyChain (e : SecondConeSystem d) : OrbitChain.Module ℝ 6 :=
  ∑ s : I, (relations ℝ 6).mkQ (e.rawH s)

/-- A convenient raw presentation of the output five-chain. -/
def rawSecondChain (e : SecondConeSystem d) : OrbitChain.Raw ℝ 5 :=
  ∑ s : I, e.rawS s

theorem mkQ_rawSecondChain (e : SecondConeSystem d) :
    (relations ℝ 5).mkQ e.rawSecondChain = e.secondChain := by
  simp [rawSecondChain, secondChain]

/-- The quotient output is the same explicit finite atom/side sum. -/
theorem secondChain_eq_sum_sideCone (e : SecondConeSystem d) :
    e.secondChain =
      ∑ a : A, ∑ j : Fin 4,
        (d.atomCoeff a * (-1 : ℝ) ^ j.val) •
          ofConfig (R := ℝ) (e.sideCone a j) := by
  classical
  rw [secondChain]
  simp_rw [e.rawS_eq_sum_sideCone]
  simp only [map_sum, LinearMap.map_smul, ofConfig]
  rw [d.sum_over_parents]
  rfl

/-- The cone identity on the single generator forming a parent facet. -/
theorem cone_identity_rawFacet (e : SecondConeSystem d) (s : I) :
    OrbitChain.rawBoundary ℝ 5
        (rawConeMap ℝ 5 (e.apex s) (d.rawFacet s)) +
      rawConeMap ℝ 4 (e.apex s)
        (OrbitChain.rawBoundary ℝ 4 (d.rawFacet s)) =
      d.rawFacet s := by
  simp only [FirstConeSystem.rawFacet, map_smul]
  rw [← smul_add]
  rw [rawCone_homotopy_generator ℝ (e.apex s) (d.facet s)
    (e.facetCone_generic s) (e.facetFace_generic s)]

/-- The cone identity on all first cones belonging to one facet. -/
theorem cone_identity_rawFirst (e : SecondConeSystem d) (s : I) :
    OrbitChain.rawBoundary ℝ 5
        (rawConeMap ℝ 5 (e.apex s) (d.rawFirst s)) +
      rawConeMap ℝ 4 (e.apex s)
        (OrbitChain.rawBoundary ℝ 4 (d.rawFirst s)) =
      d.rawFirst s := by
  apply rawCone_homotopy_finset ℝ (d.atomsOf s) d.atomCoeff
    (fun a ↦ (d.first a).cone) (e.apex s)
  · intro a ha
    have hparent : d.parent a = s :=
      (Finset.mem_filter.mp ha).2
    simpa [hparent] using e.firstCone_generic a
  · intro a ha i
    have hparent : d.parent a = s :=
      (Finset.mem_filter.mp ha).2
    simpa [hparent] using e.firstFace_generic a i

/-- Cone homotopy on the raw difference `A_s`. -/
theorem cone_identity_rawA (e : SecondConeSystem d) (s : I) :
    OrbitChain.rawBoundary ℝ 5 (e.rawH s) +
      rawConeMap ℝ 4 (e.apex s)
        (OrbitChain.rawBoundary ℝ 4 (d.rawA s)) =
      d.rawA s := by
  rw [rawH, FirstConeSystem.rawA]
  simp only [map_sub]
  have hfacet := e.cone_identity_rawFacet s
  have hfirst := e.cone_identity_rawFirst s
  calc
    OrbitChain.rawBoundary ℝ 5
          (rawConeMap ℝ 5 (e.apex s) (d.rawFacet s)) -
        OrbitChain.rawBoundary ℝ 5
          (rawConeMap ℝ 5 (e.apex s) (d.rawFirst s)) +
        (rawConeMap ℝ 4 (e.apex s)
            (OrbitChain.rawBoundary ℝ 4 (d.rawFacet s)) -
          rawConeMap ℝ 4 (e.apex s)
            (OrbitChain.rawBoundary ℝ 4 (d.rawFirst s))) =
      (OrbitChain.rawBoundary ℝ 5
          (rawConeMap ℝ 5 (e.apex s) (d.rawFacet s)) +
        rawConeMap ℝ 4 (e.apex s)
          (OrbitChain.rawBoundary ℝ 4 (d.rawFacet s))) -
      (OrbitChain.rawBoundary ℝ 5
          (rawConeMap ℝ 5 (e.apex s) (d.rawFirst s)) +
        rawConeMap ℝ 4 (e.apex s)
          (OrbitChain.rawBoundary ℝ 4 (d.rawFirst s))) := by
            module
    _ = d.rawFacet s - d.rawFirst s := by rw [hfacet, hfirst]

/-- Cone identity on the four side faces of one first cone. -/
theorem cone_identity_rawSideChain (e : SecondConeSystem d) (a : A) :
    OrbitChain.rawBoundary ℝ 4
        (rawConeMap ℝ 4 (e.apex (d.parent a))
          ((d.first a).rawSideChain ℝ)) +
      rawConeMap ℝ 3 (e.apex (d.parent a))
        (OrbitChain.rawBoundary ℝ 3
          ((d.first a).rawSideChain ℝ)) =
      (d.first a).rawSideChain ℝ := by
  apply rawCone_homotopy_finset ℝ Finset.univ
    (fun j : Fin 4 ↦ (-1 : ℝ) ^ j.val)
    (fun j ↦ (d.first a).sideFace j) (e.apex (d.parent a))
  · intro j _
    exact e.sideCone_generic a j
  · intro j _ i
    exact e.sideFace_generic a j i

/-- Cone homotopy on the full raw side cycle `B_s`. -/
theorem cone_identity_rawB (e : SecondConeSystem d) (s : I) :
    OrbitChain.rawBoundary ℝ 4 (e.rawS s) +
      rawConeMap ℝ 3 (e.apex s)
        (OrbitChain.rawBoundary ℝ 3 (d.rawB s)) =
      d.rawB s := by
  rw [rawS, FirstConeSystem.rawB, FirstConeSystem.rawSide]
  simp only [map_sum, LinearMap.map_smul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  have hparent : d.parent a = s := (Finset.mem_filter.mp ha).2
  rw [← smul_add]
  simpa [hparent] using congrArg (fun z ↦ d.atomCoeff a • z)
    (e.cone_identity_rawSideChain a)

/-- The second cone fills the raw cycle `B_s`. -/
theorem rawBoundary_rawS (e : SecondConeSystem d) (s : I) :
    OrbitChain.rawBoundary ℝ 4 (e.rawS s) = d.rawB s := by
  have h := e.cone_identity_rawB s
  rw [d.rawBoundary_rawB, map_zero, add_zero] at h
  exact h

/-- The six-chain has boundary `A_s-S_s`. -/
theorem rawBoundary_rawH (e : SecondConeSystem d) (s : I) :
    OrbitChain.rawBoundary ℝ 5 (e.rawH s) =
      d.rawA s - e.rawS s := by
  have h := e.cone_identity_rawA s
  rw [d.rawBoundary_rawA, ← rawS] at h
  exact eq_sub_of_add_eq h

/-- Boundary commutes with projection of any selected raw presentation. -/
@[simp]
theorem boundary_mkQ_raw (R : Type*) [CommRing R] {n : ℕ}
    (c : OrbitChain.Raw R (n + 1)) :
    boundary R n ((relations R (n + 1)).mkQ c) =
      (relations R n).mkQ (OrbitChain.rawBoundary R n c) := by
  rfl

/-- The output of the second cone is a genuine orbit-chain cycle. -/
theorem boundary_secondChain (e : SecondConeSystem d) :
    boundary ℝ 4 e.secondChain = 0 := by
  simp only [secondChain, map_sum, boundary_mkQ_raw, e.rawBoundary_rawS]
  exact d.sum_mkQ_rawSide_eq_zero

/-- In the quotient, the total raw `A` chain is the original facet chain:
all first cones have cancelled pairwise. -/
theorem sum_mkQ_rawA (e : SecondConeSystem d) :
    (∑ s : I, (relations ℝ 5).mkQ (d.rawA s)) = e.facetChain := by
  simp only [FirstConeSystem.rawA, map_sub, facetChain]
  rw [Finset.sum_sub_distrib, d.sum_mkQ_rawFirst_eq_zero, sub_zero]
  simp_rw [d.mkQ_rawFacet]

/-- The two-cone output is homologous to the original finite chain. -/
theorem facetChain_sub_secondChain (e : SecondConeSystem d) :
    e.facetChain - e.secondChain = boundary ℝ 5 e.homotopyChain := by
  simp only [homotopyChain, map_sum, boundary_mkQ_raw,
    e.rawBoundary_rawH, secondChain, map_sub]
  rw [Finset.sum_sub_distrib, e.sum_mkQ_rawA]

/-! ### The sharp combinatorial mass count -/

/-- Coning an explicitly indexed generic chain does not increase its
displayed coefficient mass. -/
theorem rawMass_rawCone_finset_le {n : ℕ} {K : Type*}
    (s : Finset K) (c : K → ℝ) (x : K → GenericConfig n)
    (y : ProjectivePoint)
    (h : ∀ a ∈ s, IsGeneric (coneTuple y (x a).1)) :
    OrbitChain.rawMass
        (rawConeMap ℝ n y
          (∑ a ∈ s, c a • OrbitChain.generator (x a))) ≤
      ∑ a ∈ s, |c a| := by
  simp only [map_sum, LinearMap.map_smul]
  calc
    OrbitChain.rawMass
        (∑ a ∈ s,
          c a • rawConeMap ℝ n y (OrbitChain.generator (x a))) ≤
      ∑ a ∈ s,
        OrbitChain.rawMass
          (c a • rawConeMap ℝ n y (OrbitChain.generator (x a))) :=
        OrbitChain.rawMass_sum_le s _
    _ = ∑ a ∈ s, |c a| := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [rawConeMap_generator_of_generic ℝ y (x a) (h a ha),
        OrbitChain.rawMass_smul, OrbitChain.rawMass_generator, mul_one]

/-- The four side faces of one first cone still have mass at most four
after the second coning. -/
theorem rawMass_cone_rawSideChain_le_four
    (e : SecondConeSystem d) (a : A) :
    OrbitChain.rawMass
        (rawConeMap ℝ 4 (e.apex (d.parent a))
          ((d.first a).rawSideChain ℝ)) ≤ 4 := by
  calc
    OrbitChain.rawMass
        (rawConeMap ℝ 4 (e.apex (d.parent a))
          ((d.first a).rawSideChain ℝ)) ≤
      ∑ j : Fin 4, |(-1 : ℝ) ^ j.val| := by
        apply rawMass_rawCone_finset_le Finset.univ
          (fun j : Fin 4 ↦ (-1 : ℝ) ^ j.val)
          (fun j ↦ (d.first a).sideFace j) (e.apex (d.parent a))
        intro j _
        exact e.sideCone_generic a j
    _ = 4 := by norm_num

/-- Total atom mass over the five faces of one parent is exactly five
times the parent weight. -/
theorem atomMass_eq_five (d : FirstConeSystem I A) (s : I) :
    (∑ a ∈ d.atomsOf s, |d.atomCoeff a|) =
      5 * |d.facetCoeff s| := by
  classical
  calc
    (∑ a ∈ d.atomsOf s, |d.atomCoeff a|) =
        ∑ i : Fin 5,
          ∑ a ∈ d.atomsOf s with d.faceIndex a = i,
            |d.atomCoeff a| := by
      symm
      exact Finset.sum_fiberwise (d.atomsOf s) d.faceIndex
        (fun a ↦ |d.atomCoeff a|)
    _ = ∑ _i : Fin 5, |d.facetCoeff s| := by
      apply Finset.sum_congr rfl
      intro i _
      simpa [FirstConeSystem.atomsOf, Finset.filter_filter,
        and_assoc] using d.faceAtomMass s i
    _ = 5 * |d.facetCoeff s| := by simp

/-- One parent facet contributes at most `5 × 4 = 20` to the displayed
mass of the second-cone chain. -/
theorem rawMass_rawS_le_twenty (e : SecondConeSystem d) (s : I) :
    OrbitChain.rawMass (e.rawS s) ≤ 20 * |d.facetCoeff s| := by
  rw [rawS, FirstConeSystem.rawB, FirstConeSystem.rawSide]
  simp only [map_sum, LinearMap.map_smul]
  calc
    OrbitChain.rawMass
        (∑ a ∈ d.atomsOf s,
          d.atomCoeff a •
            rawConeMap ℝ 4 (e.apex s) ((d.first a).rawSideChain ℝ)) ≤
      ∑ a ∈ d.atomsOf s,
        OrbitChain.rawMass
          (d.atomCoeff a •
            rawConeMap ℝ 4 (e.apex s) ((d.first a).rawSideChain ℝ)) :=
        OrbitChain.rawMass_sum_le (d.atomsOf s) _
    _ = ∑ a ∈ d.atomsOf s,
        |d.atomCoeff a| *
          OrbitChain.rawMass
            (rawConeMap ℝ 4 (e.apex s)
              ((d.first a).rawSideChain ℝ)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [OrbitChain.rawMass_smul]
    _ ≤ ∑ a ∈ d.atomsOf s, |d.atomCoeff a| * 4 := by
      apply Finset.sum_le_sum
      intro a ha
      have hparent : d.parent a = s := (Finset.mem_filter.mp ha).2
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa [hparent] using e.rawMass_cone_rawSideChain_le_four a
    _ = 20 * |d.facetCoeff s| := by
      rw [← Finset.sum_mul, atomMass_eq_five d s]
      ring

/-- Displayed mass of the selected input presentation. -/
def displayedFacetMass (e : SecondConeSystem d) : ℝ :=
  ∑ s : I, |d.facetCoeff s|

/-- The chosen raw presentation of the global output has mass at most
twenty times the displayed input mass. -/
theorem rawMass_rawSecondChain_le_twenty (e : SecondConeSystem d) :
    OrbitChain.rawMass e.rawSecondChain ≤ 20 * e.displayedFacetMass := by
  calc
    OrbitChain.rawMass e.rawSecondChain ≤
        ∑ s : I, OrbitChain.rawMass (e.rawS s) := by
      exact OrbitChain.rawMass_sum_le Finset.univ e.rawS
    _ ≤ ∑ s : I, 20 * |d.facetCoeff s| := by
      apply Finset.sum_le_sum
      intro s _
      exact e.rawMass_rawS_le_twenty s
    _ = 20 * e.displayedFacetMass := by
      rw [displayedFacetMass, Finset.mul_sum]

/-- Quotient `ℓ¹` mass satisfies the same constant-`20` estimate. -/
theorem quotientL1_secondChain_le_twenty (e : SecondConeSystem d) :
    OrbitChain.quotientL1 e.secondChain ≤ 20 * e.displayedFacetMass := by
  rw [← e.mkQ_rawSecondChain]
  exact (OrbitChain.quotientL1_mkQ_le e.rawSecondChain).trans
    e.rawMass_rawSecondChain_le_twenty

end SecondConeSystem

/-! ## The complete finite two-cone construction -/

/-- Every selected raw presentation of a quotient five-cycle has a two-cone
replacement.  The replacement is a cycle, is homologous to the input, and
has quotient mass at most twenty times the displayed raw mass.  All apices
and all genericity witnesses are constructed above. -/
theorem exists_twoCone_of_raw_cycle
    (c : OrbitChain.Raw ℝ 5)
    (hc : boundary ℝ 4 ((relations ℝ 5).mkQ c) = 0) :
    ∃ (z : OrbitChain.Module ℝ 5) (H : OrbitChain.Module ℝ 6),
      boundary ℝ 4 z = 0 ∧
      (relations ℝ 5).mkQ c - z = boundary ℝ 5 H ∧
      OrbitChain.quotientL1 z ≤ 20 * OrbitChain.rawMass c := by
  classical
  let p := OrbitChain.supportPresentation c hc
  let q := p.weightedFacePairing
  let h := PairedApexChoiceConstruction.choice p q
  let d := h.toFirstConeSystem
  let e := d.choice
  refine ⟨e.secondChain, e.homotopyChain, e.boundary_secondChain, ?_, ?_⟩
  · have hhom := e.facetChain_sub_secondChain
    have hfacet : e.facetChain = (relations ℝ 5).mkQ c := by
      change (∑ s : OrbitChain.SupportIndex c,
        c s.1 • ofConfig (R := ℝ) s.1) = (relations ℝ 5).mkQ c
      have hraw := congrArg (relations ℝ 5).mkQ
        (OrbitChain.raw_eq_sum_support c)
      simpa [ofConfig] using hraw
    rwa [hfacet] at hhom
  · have hmass := e.quotientL1_secondChain_le_twenty
    have hdisplay : e.displayedFacetMass = OrbitChain.rawMass c := by
      change (∑ s : OrbitChain.SupportIndex c, |c s.1|) =
        OrbitChain.rawMass c
      exact OrbitChain.sum_abs_support_eq_rawMass c
    rwa [hdisplay] at hmass

/-- Intrinsic quotient-norm form of the finite two-cone theorem.  An
arbitrary positive error is used only to choose a near-minimal raw
presentation of the input quotient chain. -/
theorem exists_twoCone_of_cycle_epsilon
    (Z : OrbitChain.Module ℝ 5) (hZ : boundary ℝ 4 Z = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (z : OrbitChain.Module ℝ 5) (H : OrbitChain.Module ℝ 6),
      boundary ℝ 4 z = 0 ∧
      Z - z = boundary ℝ 5 H ∧
      OrbitChain.quotientL1 z ≤
        20 * (OrbitChain.quotientL1 Z + ε) := by
  obtain ⟨c, hc, hmass⟩ :=
    OrbitChain.exists_presentation_lt_quotientL1_add Z hε
  have hcycle : boundary ℝ 4 ((relations ℝ 5).mkQ c) = 0 := by
    rw [hc]
    exact hZ
  obtain ⟨z, H, hz, hhom, hbound⟩ :=
    exists_twoCone_of_raw_cycle c hcycle
  refine ⟨z, H, hz, ?_, ?_⟩
  · rwa [hc] at hhom
  · exact hbound.trans (mul_le_mul_of_nonneg_left hmass.le (by norm_num))

/-! ### Pairing the chain homotopy with a pointwise cocycle -/

/-- The pointwise five-cochain cocycle equation on every generic ordered
six-tuple. -/
def IsPointwiseCocycle5 {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : U5 → E) : Prop :=
  ∀ x : GenericConfig 6,
    (∑ i : Fin 6, (-1 : ℝ) ^ i.val • f (orbitCoord5 (face i x))) = 0

/-- A pointwise cocycle annihilates the boundary of every finite six-chain.
This is the finite-chain Stokes identity needed for exact period
preservation; it involves no almost-everywhere representative. -/
theorem evaluation5_boundary_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : U5 → E) (hf : IsAlternatingFunction5 f)
    (hc : IsPointwiseCocycle5 f) (z : OrbitChain.Module ℝ 6) :
    evaluation5 f hf (boundary ℝ 5 z) = 0 := by
  obtain ⟨c, rfl⟩ := (relations ℝ 6).mkQ_surjective z
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add x a c hx ha ih =>
      have hsingle :
          (relations ℝ 6).mkQ (Finsupp.single x a) =
            a • ofConfig (R := ℝ) x := by
        rw [show Finsupp.single x a = a • OrbitChain.generator x by
          ext y
          simp [OrbitChain.generator]]
        simp [ofConfig]
      rw [map_add, hsingle, map_add, map_smul, map_add, map_smul,
        boundary_ofConfig, map_sum]
      simp_rw [map_smul, evaluation5_ofConfig]
      rw [hc x, smul_zero, zero_add]
      exact ih

namespace SecondConeSystem

variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I]
variable {d : FirstConeSystem I A}

/-- Exact preservation of every pointwise cocycle period under the two-cone
chain homotopy. -/
theorem evaluation5_secondChain_eq_facetChain
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : SecondConeSystem d)
    (f : U5 → E) (hf : IsAlternatingFunction5 f)
    (hc : IsPointwiseCocycle5 f) :
    evaluation5 f hf e.secondChain = evaluation5 f hf e.facetChain := by
  have hzero := evaluation5_boundary_eq_zero f hf hc e.homotopyChain
  have hhom := congrArg (evaluation5 f hf) e.facetChain_sub_secondChain
  rw [map_sub, hzero] at hhom
  exact (sub_eq_zero.mp hhom).symm

end SecondConeSystem

theorem evaluation5_edgeChain (f : U5 → ℂ)
    (hf : IsAlternatingFunction5 f) (p : UEdge) :
    evaluation5 f hf (edgeChain p) =
      f (phi2 (edgeAdm2 p)) - f (phi1 (edgeAdm1 p)) := by
  rw [edgeChain, map_sub, evaluation5_ofConfig, evaluation5_ofConfig,
    orbitCoord5_normalizedConfig5, orbitCoord5_normalizedConfig5]

/-- The algebraic pairing of the affine cocycle with the displayed
eight-edge chain is exactly the period used in the pole computation. -/
theorem evaluation5_periodCycle_reducedR
    (A B : ℂ) (h : PeriodCycleAdmissible A B) :
    evaluation5 (fun q : U5 ↦ reducedR (matrix5 q.1))
        reducedR_isAlternatingFunction5 (periodCycle A B h) =
      periodCycleValue A B h := by
  rw [periodCycle, edgeSum, map_sum, periodCycleValue]
  apply Finset.sum_congr rfl
  intro i _
  rw [evaluation5_edgeChain]
  rfl

/-- The analytic signed-measure pairing and the article's explicit period
are the same quantity. -/
theorem integral_diracMap_periodCycle_reducedR
    (A B : ℂ) (h : PeriodCycleAdmissible A B) :
    (∫ᵛ q, reducedR (matrix5 q.1)
      ∂<•(diracMap5 (periodCycle A B h))) = periodCycleValue A B h := by
  rw [integral_diracMap5_eq_evaluation5
    (fun q : U5 ↦ reducedR (matrix5 q.1))
    reducedR_isAlternatingFunction5]
  exact evaluation5_periodCycle_reducedR A B h

end

end MeasureChain

end Sp4
