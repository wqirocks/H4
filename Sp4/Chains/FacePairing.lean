import Sp4.Chains.PairingCore

/-!
# Orientation-correct finite face pairings

This file applies the two finite transportation constructions to the face
orbits of a displayed quotient cycle.  The regular case uses the orientation
character and product coupling; the singular case uses an odd stabilizer and
the two-copy splitting.
-/

namespace Sp4
namespace OrbitChain

open Pfaffian
open scoped BigOperators

noncomputable section

universe u

namespace WeightedFacetPresentation

variable {I : Type u} [Fintype I] [DecidableEq I]
variable (p : WeightedFacetPresentation I)

/-! ## Concrete transport packages -/

/-- A chosen orbit relation between two actual face occurrences, together
with its realization by a symplectic transformation. -/
structure FaceTransport (o o' : p.FaceOccurrence) where
  permutation : Equiv.Perm (Fin 4)
  group : SymplecticGroup
  coord_transport :
    permute4 permutation (orbitCoord4 (p.faceBase o)) =
      orbitCoord4 (p.faceBase o')
  base_transport :
    p.faceBase o' =
      smulGeneric group (permuteGeneric permutation (p.faceBase o))

theorem nonempty_faceTransport {o o' : p.FaceOccurrence}
    (h : p.FaceRelated o o') : Nonempty (p.FaceTransport o o') := by
  obtain ⟨σ, g, hcoord, hbase⟩ :=
    p.exists_face_transport_of_same_orbit h
  exact ⟨⟨σ, g, hcoord, hbase.symm⟩⟩

noncomputable def chosenFaceTransport {o o' : p.FaceOccurrence}
    (h : p.FaceRelated o o') : p.FaceTransport o o' :=
  Classical.choice (p.nonempty_faceTransport h)

/-- A chosen odd self-transport at a singular occurrence. -/
structure OddSelfTransport {c : p.FaceOrbit} (o : p.OccurrencesIn c) where
  permutation : Equiv.Perm (Fin 4)
  group : SymplecticGroup
  sign_eq : permSign ℝ permutation = -1
  base_transport :
    p.faceBase o.1 =
      smulGeneric group (permuteGeneric permutation (p.faceBase o.1))

theorem nonempty_oddSelfTransport {c : p.FaceOrbit}
    (hc : p.FaceOrbitSingular c) (o : p.OccurrencesIn c) :
    Nonempty (p.OddSelfTransport o) := by
  obtain ⟨σ, g, hsign, hbase⟩ := p.exists_odd_self_transport hc o
  exact ⟨⟨σ, g, hsign, hbase⟩⟩

noncomputable def chosenOddSelfTransport {c : p.FaceOrbit}
    (hc : p.FaceOrbitSingular c) (o : p.OccurrencesIn c) :
    p.OddSelfTransport o :=
  Classical.choice (p.nonempty_oddSelfTransport hc o)

theorem faceRelated_of_occurrences_in
    {c : p.FaceOrbit} (o o' : p.OccurrencesIn c) :
    p.FaceRelated o.1 o'.1 := by
  exact coord4Related_trans
    (coord4Related_symm (p.occurrence_related_representative o))
    (p.occurrence_related_representative o')

/-! ## A local pairing over one finite face orbit -/

/-- The local analogue of `WeightedFacePairing`, with occurrences restricted
to one finite unoriented face orbit. -/
structure OrbitFacePairing (c : p.FaceOrbit) (A : Type*) [Fintype A] where
  occurrence : A → p.OccurrencesIn c
  atomCoeff : A → ℝ
  coeff_refinement : ∀ o,
    (∑ a ∈ Finset.univ.filter (fun a : A ↦ occurrence a = o),
      atomCoeff a) = p.faceCoeff o.1
  mass_refinement : ∀ o,
    (∑ a ∈ Finset.univ.filter (fun a : A ↦ occurrence a = o),
      |atomCoeff a|) = |p.faceCoeff o.1|
  mate : Equiv.Perm A
  mate_involutive : ∀ a, mate (mate a) = a
  mate_ne : ∀ a, mate a ≠ a
  group : A → SymplecticGroup
  permutation : A → Equiv.Perm (Fin 4)
  base_transport : ∀ a,
    p.faceBase (occurrence (mate a)).1 =
      smulGeneric (group a)
        (permuteGeneric (permutation a) (p.faceBase (occurrence a).1))
  coeff_transport : ∀ a,
    atomCoeff (mate a) * permSign ℝ (permutation a) = -atomCoeff a

/-! ## Regular-orbit data -/

abbrev orbitCoeff (c : p.FaceOrbit) : p.OccurrencesIn c → ℝ :=
  fun o ↦ p.faceCoeff o.1

abbrev orbitOrientation (c : p.FaceOrbit) : p.OccurrencesIn c → ℝ :=
  fun o ↦ coord4Orientation (p.orbitBaseCoord c)
    (orbitCoord4 (p.faceBase o.1))

abbrev RegularAtom (c : p.FaceOrbit) :=
  RegularCoupling.Atom (p.orbitCoeff c) (p.orbitOrientation c)

def regularOccurrence {c : p.FaceOrbit} (a : p.RegularAtom c) :
    p.OccurrencesIn c :=
  RegularCoupling.endpoint (p.orbitCoeff c) (p.orbitOrientation c) a

def regularAtomCoeff {c : p.FaceOrbit} (a : p.RegularAtom c) : ℝ :=
  RegularCoupling.atomCoeff (p.orbitCoeff c) (p.orbitOrientation c) a

def regularMate (c : p.FaceOrbit) : Equiv.Perm (p.RegularAtom c) :=
  RegularCoupling.mate (p.orbitCoeff c) (p.orbitOrientation c)

noncomputable def regularTransport {c : p.FaceOrbit}
    (a : p.RegularAtom c) :
    p.FaceTransport (p.regularOccurrence a).1
      (p.regularOccurrence (p.regularMate c a)).1 :=
  p.chosenFaceTransport
    (p.faceRelated_of_occurrences_in _ _)

@[simp]
theorem orientedValue_orbitCoeff {c : p.FaceOrbit}
    (o : p.OccurrencesIn c) :
    RegularCoupling.orientedValue (p.orbitCoeff c)
        (p.orbitOrientation c) o = p.orientedFaceCoeff c o := by
  rfl

theorem orbitOrientation_eq_one_or_neg_one
    {c : p.FaceOrbit} (hc : p.FaceOrbitRegular c)
    (o : p.OccurrencesIn c) :
    p.orbitOrientation c o = 1 ∨ p.orbitOrientation c o = -1 :=
  p.orientation_occurrence_eq_one_or_neg_one hc o

/-- The product coupling, together with concrete orbit transports, gives a
complete local pairing on every regular face orbit. -/
noncomputable def regularOrbitPairing
    {c : p.FaceOrbit} (hc : p.FaceOrbitRegular c) :
    p.OrbitFacePairing c (p.RegularAtom c) where
  occurrence := p.regularOccurrence
  atomCoeff := p.regularAtomCoeff
  coeff_refinement := by
    intro o
    let C := p.orbitCoeff c
    let O := p.orbitOrientation c
    letI : Nonempty (RegularCoupling.Positive C O) := by
      change Nonempty (p.PositiveOccurrences c)
      exact p.exists_positiveOccurrence hc
    have heq :
        (∑ q : RegularCoupling.Positive C O,
            RegularCoupling.positiveWeight C O q) =
          ∑ q : RegularCoupling.Negative C O,
            RegularCoupling.negativeWeight C O q := by
      change (∑ q : p.PositiveOccurrences c, p.positiveWeight q) =
        ∑ q : p.NegativeOccurrences c, p.negativeWeight q
      exact p.regular_positive_negative_mass_eq hc
    have hne :
        (∑ q : RegularCoupling.Positive C O,
          RegularCoupling.positiveWeight C O q) ≠ 0 :=
      RegularCoupling.sum_positiveWeight_ne_zero C O
    have hori : ∀ q, O q = 1 ∨ O q = -1 :=
      fun q ↦ p.orbitOrientation_eq_one_or_neg_one hc q
    have hv : RegularCoupling.orientedValue C O o ≠ 0 := by
      change p.orientedFaceCoeff c o ≠ 0
      exact p.orientedFaceCoeff_ne hc o
    rcases lt_or_gt_of_ne hv with hneg | hpos
    · convert RegularCoupling.coeff_refinement_neg C O hne hori o hneg
        using 1 <;>
        simp [regularOccurrence, regularAtomCoeff, orbitCoeff,
          orbitOrientation, C, O]
      apply Finset.sum_congr
      · ext a
        constructor
        · exact fun ha ↦ Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
        · exact fun ha ↦ Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
      · intro a ha
        rfl
    · convert RegularCoupling.coeff_refinement_pos C O heq hne hori o hpos
        using 1 <;>
        simp [regularOccurrence, regularAtomCoeff, orbitCoeff,
          orbitOrientation, C, O]
      apply Finset.sum_congr
      · ext a
        constructor
        · exact fun ha ↦ Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
        · exact fun ha ↦ Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
      · intro a ha
        rfl
  mass_refinement := by
    intro o
    let C := p.orbitCoeff c
    let O := p.orbitOrientation c
    letI : Nonempty (RegularCoupling.Positive C O) := by
      change Nonempty (p.PositiveOccurrences c)
      exact p.exists_positiveOccurrence hc
    have heq :
        (∑ q : RegularCoupling.Positive C O,
            RegularCoupling.positiveWeight C O q) =
          ∑ q : RegularCoupling.Negative C O,
            RegularCoupling.negativeWeight C O q := by
      change (∑ q : p.PositiveOccurrences c, p.positiveWeight q) =
        ∑ q : p.NegativeOccurrences c, p.negativeWeight q
      exact p.regular_positive_negative_mass_eq hc
    have hne :
        (∑ q : RegularCoupling.Positive C O,
          RegularCoupling.positiveWeight C O q) ≠ 0 :=
      RegularCoupling.sum_positiveWeight_ne_zero C O
    have hori : ∀ q, O q = 1 ∨ O q = -1 :=
      fun q ↦ p.orbitOrientation_eq_one_or_neg_one hc q
    have hv : RegularCoupling.orientedValue C O o ≠ 0 := by
      change p.orientedFaceCoeff c o ≠ 0
      exact p.orientedFaceCoeff_ne hc o
    rcases lt_or_gt_of_ne hv with hneg | hpos
    · convert RegularCoupling.mass_refinement_neg C O hne hori o hneg
        using 1 <;>
        simp [regularOccurrence, regularAtomCoeff, orbitCoeff,
          orbitOrientation, C, O]
      apply Finset.sum_congr
      · ext a
        constructor
        · exact fun ha ↦ Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
        · exact fun ha ↦ Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
      · intro a ha
        rfl
    · convert RegularCoupling.mass_refinement_pos C O heq hne hori o hpos
        using 1 <;>
        simp [regularOccurrence, regularAtomCoeff, orbitCoeff,
          orbitOrientation, C, O]
      apply Finset.sum_congr
      · ext a
        constructor
        · exact fun ha ↦ Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
        · exact fun ha ↦ Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
      · intro a ha
        rfl
  mate := p.regularMate c
  mate_involutive := RegularCoupling.mate_involutive
    (p.orbitCoeff c) (p.orbitOrientation c)
  mate_ne := RegularCoupling.mate_ne
    (p.orbitCoeff c) (p.orbitOrientation c)
  group := fun a ↦ (p.regularTransport a).group
  permutation := fun a ↦ (p.regularTransport a).permutation
  base_transport := fun a ↦ (p.regularTransport a).base_transport
  coeff_transport := by
    intro a
    let t := p.regularTransport a
    apply RegularCoupling.coeff_transport_of_orientation
      (p.orbitCoeff c) (p.orbitOrientation c) a t.permutation
    have hcov := coord4Orientation_permute hc t.permutation
      (orbitCoord4 (p.faceBase (p.regularOccurrence a).1))
    rw [t.coord_transport] at hcov
    simpa [regularOccurrence, regularMate, orbitOrientation, orbitBaseCoord,
      t] using hcov

/-! ## Singular-orbit data -/

abbrev SingularAtom (c : p.FaceOrbit) :=
  SingularSplitting.Atom (p.orbitCoeff c)

def singularOccurrence {c : p.FaceOrbit} (a : p.SingularAtom c) :
    p.OccurrencesIn c :=
  SingularSplitting.endpoint (p.orbitCoeff c) a

def singularAtomCoeff {c : p.FaceOrbit} (a : p.SingularAtom c) : ℝ :=
  SingularSplitting.atomCoeff (p.orbitCoeff c) a

def singularMate (c : p.FaceOrbit) : Equiv.Perm (p.SingularAtom c) :=
  SingularSplitting.mate (p.orbitCoeff c)

@[simp]
theorem singularOccurrence_mate {c : p.FaceOrbit}
    (a : p.SingularAtom c) :
    p.singularOccurrence (p.singularMate c a) =
      p.singularOccurrence a := by
  rcases a with ⟨o, b⟩
  rfl

noncomputable def singularTransport {c : p.FaceOrbit}
    (hc : p.FaceOrbitSingular c) (a : p.SingularAtom c) :
    p.OddSelfTransport (p.singularOccurrence a) :=
  p.chosenOddSelfTransport hc (p.singularOccurrence a)

/-- The odd-stabilizer splitting gives a complete local pairing on every
orientation-singular face orbit. -/
noncomputable def singularOrbitPairing
    {c : p.FaceOrbit} (hc : p.FaceOrbitSingular c) :
    p.OrbitFacePairing c (p.SingularAtom c) where
  occurrence := p.singularOccurrence
  atomCoeff := p.singularAtomCoeff
  coeff_refinement := by
    intro o
    convert SingularSplitting.coeff_refinement (p.orbitCoeff c) o using 1 <;>
      simp [singularOccurrence, singularAtomCoeff, orbitCoeff]
    apply Finset.sum_congr
    · ext a
      constructor
      · exact fun ha ↦ Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
      · exact fun ha ↦ Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
    · intro a ha
      rfl
  mass_refinement := by
    intro o
    convert SingularSplitting.mass_refinement (p.orbitCoeff c) o using 1 <;>
      simp [singularOccurrence, singularAtomCoeff, orbitCoeff]
    apply Finset.sum_congr
    · ext a
      constructor
      · exact fun ha ↦ Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
      · exact fun ha ↦ Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
    · intro a ha
      rfl
  mate := p.singularMate c
  mate_involutive := SingularSplitting.mate_involutive (p.orbitCoeff c)
  mate_ne := SingularSplitting.mate_ne (p.orbitCoeff c)
  group := fun a ↦ (p.singularTransport hc a).group
  permutation := fun a ↦ (p.singularTransport hc a).permutation
  base_transport := by
    intro a
    rw [p.singularOccurrence_mate]
    exact (p.singularTransport hc a).base_transport
  coeff_transport := by
    intro a
    apply SingularSplitting.coeff_transport_of_odd
      (p.orbitCoeff c) a (p.singularTransport hc a).permutation
    exact (p.singularTransport hc a).sign_eq

/-! ## Selecting one local construction in every orbit -/

/-- A local atom type is packaged with the exact `Fintype` structure used
by its pairing, avoiding any dependence on a particular enumeration. -/
structure OrbitPairingPackage (c : p.FaceOrbit) where
  Atom : Type u
  atomFintype : Fintype Atom
  pairing : @OrbitFacePairing I _ _ p c Atom atomFintype

noncomputable def orbitPairingPackage (c : p.FaceOrbit) :
    p.OrbitPairingPackage c := by
  classical
  by_cases hc : p.FaceOrbitRegular c
  · exact
      { Atom := p.RegularAtom c
        atomFintype := inferInstance
        pairing := p.regularOrbitPairing hc }
  · exact
      { Atom := p.SingularAtom c
        atomFintype := inferInstance
        pairing := p.singularOrbitPairing hc }

noncomputable instance orbitPairingPackageAtomFintype (c : p.FaceOrbit) :
    Fintype (p.orbitPairingPackage c).Atom :=
  (p.orbitPairingPackage c).atomFintype

abbrev GlobalFaceAtom :=
  Σ c : p.FaceOrbit, (p.orbitPairingPackage c).Atom

noncomputable instance globalFaceAtomFintype :
    Fintype p.GlobalFaceAtom := inferInstance

def globalOccurrence (a : p.GlobalFaceAtom) : p.FaceOccurrence :=
  ((p.orbitPairingPackage a.1).pairing.occurrence a.2).1

def globalAtomCoeff (a : p.GlobalFaceAtom) : ℝ :=
  (p.orbitPairingPackage a.1).pairing.atomCoeff a.2

def globalMate : Equiv.Perm p.GlobalFaceAtom where
  toFun a := ⟨a.1, (p.orbitPairingPackage a.1).pairing.mate a.2⟩
  invFun a := ⟨a.1, (p.orbitPairingPackage a.1).pairing.mate a.2⟩
  left_inv a := by
    rcases a with ⟨c, a⟩
    change (⟨c, (p.orbitPairingPackage c).pairing.mate
      ((p.orbitPairingPackage c).pairing.mate a)⟩ :
        p.GlobalFaceAtom) = ⟨c, a⟩
    rw [(p.orbitPairingPackage c).pairing.mate_involutive]
  right_inv a := by
    rcases a with ⟨c, a⟩
    change (⟨c, (p.orbitPairingPackage c).pairing.mate
      ((p.orbitPairingPackage c).pairing.mate a)⟩ :
        p.GlobalFaceAtom) = ⟨c, a⟩
    rw [(p.orbitPairingPackage c).pairing.mate_involutive]

@[simp]
theorem globalMate_apply (a : p.GlobalFaceAtom) :
    p.globalMate a =
      ⟨a.1, (p.orbitPairingPackage a.1).pairing.mate a.2⟩ := rfl

theorem globalMate_involutive (a : p.GlobalFaceAtom) :
    p.globalMate (p.globalMate a) = a := by
  rcases a with ⟨c, a⟩
  change (⟨c, (p.orbitPairingPackage c).pairing.mate
    ((p.orbitPairingPackage c).pairing.mate a)⟩ :
      p.GlobalFaceAtom) = ⟨c, a⟩
  rw [(p.orbitPairingPackage c).pairing.mate_involutive]

theorem globalMate_ne (a : p.GlobalFaceAtom) :
    p.globalMate a ≠ a := by
  rcases a with ⟨c, a⟩
  intro h
  change (⟨c, (p.orbitPairingPackage c).pairing.mate a⟩ :
    p.GlobalFaceAtom) = ⟨c, a⟩ at h
  have ha : (p.orbitPairingPackage c).pairing.mate a = a := by
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  exact (p.orbitPairingPackage c).pairing.mate_ne a ha

@[simp]
theorem orbitClass_globalOccurrence (a : p.GlobalFaceAtom) :
    p.orbitClass (p.globalOccurrence a) = a.1 :=
  ((p.orbitPairingPackage a.1).pairing.occurrence a.2).2

/-- A finite sum over all global atoms supported above one occurrence is
the corresponding local sum in the unique orbit containing that occurrence. -/
theorem global_refinement
    (v : (c : p.FaceOrbit) → (p.orbitPairingPackage c).Atom → ℝ)
    (target : p.FaceOccurrence → ℝ)
    (hloc : ∀ (c : p.FaceOrbit) (o : p.OccurrencesIn c),
      (∑ a ∈ Finset.univ.filter
        (fun a : (p.orbitPairingPackage c).Atom ↦
          (p.orbitPairingPackage c).pairing.occurrence a = o),
        v c a) = target o.1)
    (o : p.FaceOccurrence) :
    (∑ a ∈ Finset.univ.filter
      (fun a : p.GlobalFaceAtom ↦ p.globalOccurrence a = o),
      v a.1 a.2) = target o := by
  classical
  let c₀ : p.FaceOrbit := p.orbitClass o
  let o₀ : p.OccurrencesIn c₀ := ⟨o, rfl⟩
  rw [Finset.sum_filter, Fintype.sum_sigma]
  calc
    (∑ c : p.FaceOrbit,
      ∑ a : (p.orbitPairingPackage c).Atom,
        if p.globalOccurrence ⟨c, a⟩ = o then v c a else 0) =
      ∑ a : (p.orbitPairingPackage c₀).Atom,
        if p.globalOccurrence ⟨c₀, a⟩ = o then v c₀ a else 0 := by
        apply Fintype.sum_eq_single c₀
        intro c hc
        apply Finset.sum_eq_zero
        intro a _
        rw [if_neg]
        intro ha
        apply hc
        calc
          c = p.orbitClass (p.globalOccurrence ⟨c, a⟩) :=
            (p.orbitClass_globalOccurrence ⟨c, a⟩).symm
          _ = p.orbitClass o := congrArg p.orbitClass ha
          _ = c₀ := rfl
    _ =
      ∑ a : (p.orbitPairingPackage c₀).Atom,
        if (p.orbitPairingPackage c₀).pairing.occurrence a = o₀
          then v c₀ a else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        simp only [globalOccurrence]
        congr 1
        apply propext
        constructor
        · intro ha
          apply Subtype.ext
          exact ha
        · intro ha
          exact congrArg Subtype.val ha
    _ = target o := by
      have h := hloc c₀ o₀
      rw [Finset.sum_filter] at h
      simpa [o₀] using h

def globalGroup (a : p.GlobalFaceAtom) : SymplecticGroup :=
  (p.orbitPairingPackage a.1).pairing.group a.2

def globalPermutation (a : p.GlobalFaceAtom) : Equiv.Perm (Fin 4) :=
  (p.orbitPairingPackage a.1).pairing.permutation a.2

theorem global_base_transport (a : p.GlobalFaceAtom) :
    p.faceBase (p.globalOccurrence (p.globalMate a)) =
      smulGeneric (p.globalGroup a)
        (permuteGeneric (p.globalPermutation a)
          (p.faceBase (p.globalOccurrence a))) := by
  rcases a with ⟨c, a⟩
  exact (p.orbitPairingPackage c).pairing.base_transport a

theorem global_coeff_transport (a : p.GlobalFaceAtom) :
    p.globalAtomCoeff (p.globalMate a) *
        permSign ℝ (p.globalPermutation a) =
      -p.globalAtomCoeff a := by
  rcases a with ⟨c, a⟩
  exact (p.orbitPairingPackage c).pairing.coeff_transport a

/-- Every finite displayed quotient cycle admits an orientation-correct,
mass-preserving pairing of all of its four-face occurrences. -/
noncomputable def weightedFacePairing :
    WeightedFacePairing p p.GlobalFaceAtom where
  occurrence := p.globalOccurrence
  atomCoeff := p.globalAtomCoeff
  coeff_refinement := by
    intro o
    exact p.global_refinement
      (fun c a ↦ (p.orbitPairingPackage c).pairing.atomCoeff a)
      p.faceCoeff
      (fun c o ↦ (p.orbitPairingPackage c).pairing.coeff_refinement o)
      o
  mass_refinement := by
    intro o
    exact p.global_refinement
      (fun c a ↦ |(p.orbitPairingPackage c).pairing.atomCoeff a|)
      (fun o ↦ |p.faceCoeff o|)
      (fun c o ↦ (p.orbitPairingPackage c).pairing.mass_refinement o)
      o
  mate := p.globalMate
  mate_involutive := p.globalMate_involutive
  mate_ne := p.globalMate_ne
  group := p.globalGroup
  permutation := p.globalPermutation
  base_transport := p.global_base_transport
  coeff_transport := p.global_coeff_transport

/-! ## Regrouping the paired atoms by their parent facet -/

theorem sum_filter_fst_eq_sum_filter_pair
    {A J M : Type*} [Fintype A] [Fintype J]
    [DecidableEq J] [AddCommMonoid M]
    (occ : A → I × J) (F : A → M) (s : I) :
    (∑ a ∈ Finset.univ.filter (fun a ↦ (occ a).1 = s), F a) =
      ∑ j : J, ∑ a ∈ Finset.univ.filter
        (fun a ↦ occ a = (s, j)), F a := by
  classical
  rw [Finset.sum_filter]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : (occ a).1 = s
  · simp [h, Prod.ext_iff]
  · simp [h, Prod.ext_iff]

theorem paired_rawBoundary_refinement
    {A : Type*} [Fintype A]
    (d : WeightedFacePairing p A) (s : I) :
    (∑ a ∈ Finset.univ.filter
        (fun a : A ↦ (d.occurrence a).1 = s),
        d.atomCoeff a • generator (p.faceBase (d.occurrence a))) =
      rawBoundary ℝ 4 (p.coeff s • generator (p.facet s)) := by
  classical
  rw [sum_filter_fst_eq_sum_filter_pair d.occurrence]
  calc
    (∑ i : Fin 5, ∑ a ∈ Finset.univ.filter
        (fun a : A ↦ d.occurrence a = (s, i)),
        d.atomCoeff a • generator (p.faceBase (d.occurrence a))) =
      ∑ i : Fin 5, ∑ a ∈ Finset.univ.filter
        (fun a : A ↦ d.occurrence a = (s, i)),
        d.atomCoeff a • generator (p.faceBase (s, i)) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro a ha
          rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ i : Fin 5,
        (∑ a ∈ Finset.univ.filter
          (fun a : A ↦ d.occurrence a = (s, i)), d.atomCoeff a) •
            generator (p.faceBase (s, i)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_smul]
    _ = ∑ i : Fin 5,
        p.faceCoeff (s, i) • generator (p.faceBase (s, i)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [d.coeff_refinement]
    _ = rawBoundary ℝ 4 (p.coeff s • generator (p.facet s)) := by
      rw [map_smul, rawBoundary_generator]
      simp only [boundaryGenerator, faceCoeff, faceBase, mul_smul,
        Finset.smul_sum]

theorem paired_faceAtomMass
    {A : Type*} [Fintype A]
    (d : WeightedFacePairing p A) (s : I) (i : Fin 5) :
    (∑ a ∈ Finset.univ.filter
        (fun a : A ↦ (d.occurrence a).1 = s ∧
          (d.occurrence a).2 = i), |d.atomCoeff a|) = |p.coeff s| := by
  have h := d.mass_refinement (s, i)
  rw [p.abs_faceCoeff] at h
  convert h using 1
  apply Finset.sum_congr
  · ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact Prod.ext h₁ h₂
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · intro a ha
    rfl

end WeightedFacetPresentation

end
end OrbitChain
end Sp4
