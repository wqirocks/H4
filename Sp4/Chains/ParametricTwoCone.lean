import Sp4.Chains.TwoCone
import Sp4.Chains.Diffusion
import Sp4.Measure.Permutation
import Sp4.Symplectic.AnalyticGeneric
import Sp4.Symplectic.TwoFreeSubmersion

/-!
# Shared parameters for the two-cone diffusion

For a finite weighted face pairing, the article varies one literal vector
for every parent facet and one literal seed vector for every oriented atom
pair.  The opposite first apex is obtained by the prescribed symplectic
transport.  This file constructs the common analytic parameter locus and
the submersive orbit-coordinate maps used in the diffusion.
-/

namespace Sp4
namespace TwoConeParameterization

noncomputable section

open Set MeasureTheory
open scoped BigOperators LinearAlgebra.Projectivization

variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
variable {p : OrbitChain.WeightedFacetPresentation I}
variable (d : OrbitChain.WeightedFacePairing p A)

/-- One literal second-apex vector for each parent and one literal seed
first-apex vector for each atom-pair endpoint.  Only the canonically forward
endpoint of each mate pair is read. -/
abbrev Parameter (I A : Type*) := (I ⊕ A) → SymplecticVector

def parameterEval (k : I ⊕ A) :
    Parameter I A →L[ℂ] SymplecticVector :=
  ContinuousLinearMap.proj k

def secondVectorCLM (s : I) :
    Parameter I A →L[ℂ] SymplecticVector :=
  parameterEval (Sum.inl s)

def secondVector (q : Parameter I A) (s : I) : SymplecticVector :=
  secondVectorCLM s q

/-- The continuous linear map producing the first-apex vector at an atom.
At a reverse endpoint it applies the coherent transport to the seed stored
at the mate. -/
noncomputable def firstVectorCLM (a : A) :
    Parameter I A →L[ℂ] SymplecticVector := by
  classical
  exact if d.pairForward a then parameterEval (Sum.inr a)
    else (d.coherentGroup (d.mate a)).1.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (parameterEval (Sum.inr (d.mate a)))

noncomputable def firstVector (q : Parameter I A) (a : A) : SymplecticVector :=
  firstVectorCLM d a q

@[simp]
theorem secondVector_apply (q : Parameter I A) (s : I) :
    secondVector q s = q (Sum.inl s) :=
  rfl

theorem firstVector_apply_of_forward (q : Parameter I A) (a : A)
    (ha : d.pairForward a) :
    firstVector d q a = q (Sum.inr a) := by
  simp [firstVector, firstVectorCLM, ha, parameterEval]

theorem firstVector_apply_of_not_forward (q : Parameter I A) (a : A)
    (ha : ¬d.pairForward a) :
    firstVector d q a =
      (d.coherentGroup (d.mate a)).1 (q (Sum.inr (d.mate a))) := by
  simp [firstVector, firstVectorCLM, ha, parameterEval]

/-- Literal compatibility of the two endpoints of every paired first-apex
choice. -/
theorem firstVector_mate (q : Parameter I A) (a : A) :
    firstVector d q (d.mate a) =
      (d.coherentGroup a).1 (firstVector d q a) := by
  classical
  by_cases ha : d.pairForward a
  · have hm : ¬d.pairForward (d.mate a) :=
      (d.pairForward_ne_mate a).mp ha
    rw [firstVector_apply_of_not_forward d q (d.mate a) hm,
      d.mate_involutive, firstVector_apply_of_forward d q a ha]
  · have hm : d.pairForward (d.mate a) :=
      (d.pairForward_mate_iff a).mpr ha
    rw [firstVector_apply_of_forward d q (d.mate a) hm,
      firstVector_apply_of_not_forward d q a ha,
      d.coherentGroup_mate]
    simp

theorem secondVectorCLM_surjective (s : I) :
    Function.Surjective (secondVectorCLM (A := A) s) := by
  classical
  intro v
  let q : Parameter I A := fun k ↦ if k = Sum.inl s then v else 0
  refine ⟨q, ?_⟩
  simp [secondVectorCLM, parameterEval, q]

theorem firstVectorCLM_surjective (a : A) :
    Function.Surjective (firstVectorCLM d a) := by
  classical
  intro v
  by_cases ha : d.pairForward a
  · let q : Parameter I A := fun k ↦ if k = Sum.inr a then v else 0
    refine ⟨q, ?_⟩
    simp [firstVectorCLM, parameterEval, ha, q]
  · let g := (d.coherentGroup (d.mate a)).1
    let q : Parameter I A := fun k ↦
      if k = Sum.inr (d.mate a) then g⁻¹ v else 0
    refine ⟨q, ?_⟩
    simp [firstVectorCLM, parameterEval, ha, q, g]

/-- The two literal free vectors of the elementary output term indexed by
an atom: second apex first, transported first apex second. -/
noncomputable def outputPairCLM (a : A) :
    Parameter I A →L[ℂ] TwoFree.VectorPair :=
  (secondVectorCLM (A := A) (d.parent a)).prod (firstVectorCLM d a)

@[simp]
theorem outputPairCLM_apply (a : A) (q : Parameter I A) :
    outputPairCLM d a q =
      (secondVector q (d.parent a), firstVector d q a) :=
  rfl

/-- The parameter projection onto the two free literal vectors is onto.
The two coordinates lie in opposite summands of the parameter space, so
sharing variables among other elementary terms causes no rank loss. -/
theorem outputPairCLM_surjective (a : A) :
    Function.Surjective (outputPairCLM d a) := by
  classical
  rintro ⟨x, y⟩
  by_cases ha : d.pairForward a
  · let q : Parameter I A := fun k ↦ match k with
      | Sum.inl s => if s = d.parent a then x else 0
      | Sum.inr b => if b = a then y else 0
    refine ⟨q, ?_⟩
    apply Prod.ext
    · simp [outputPairCLM, secondVectorCLM, parameterEval, q]
    · simp [outputPairCLM, firstVectorCLM, parameterEval, ha, q]
  · let g := (d.coherentGroup (d.mate a)).1
    let q : Parameter I A := fun k ↦ match k with
      | Sum.inl s => if s = d.parent a then x else 0
      | Sum.inr b => if b = d.mate a then g⁻¹ y else 0
    refine ⟨q, ?_⟩
    apply Prod.ext
    · simp [outputPairCLM, secondVectorCLM, parameterEval, q]
    · simp [outputPairCLM, firstVectorCLM, parameterEval, ha, q, g]

/-! ## Normalizing the fixed triple in every elementary output -/

/-- The three vertices left after deleting one vertex from a four-point face
form a strong ordered triple.  This is the fixed triple in the elementary
output indexed by `(a,j)`. -/
def outputTriple (a : A) (j : Fin 4) : TwoFree.StrongTriple :=
  let b := p.faceBase (d.occurrence a)
  ⟨(OrbitChain.face j b).1,
    { generic := (OrbitChain.face j b).2
      independent :=
        (b.2.triplesIndependent_of_four_le (by norm_num)).delete j }⟩

/-- A chosen symplectic normalization of the fixed output triple. -/
noncomputable def outputNormalizer (a : A) (j : Fin 4) :
    SymplecticGroup :=
  Classical.choose (TwoFree.exists_smul_eq_standardTriple
    (outputTriple d a j))

theorem outputNormalizer_spec (a : A) (j : Fin 4) :
    outputNormalizer d a j • (outputTriple d a j).1 =
      TwoFree.standardTriple :=
  Classical.choose_spec (TwoFree.exists_smul_eq_standardTriple
    (outputTriple d a j))

/-- Apply the fixed triple-normalizer to both free literal vectors. -/
noncomputable def normalizedOutputPairCLM (a : A) (j : Fin 4) :
    Parameter I A →L[ℂ] TwoFree.VectorPair :=
  let g := outputNormalizer d a j
  (g.1.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (secondVectorCLM (A := A) (d.parent a))).prod
    (g.1.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (firstVectorCLM d a))

@[simp]
theorem normalizedOutputPairCLM_apply (a : A) (j : Fin 4)
    (q : Parameter I A) :
    normalizedOutputPairCLM d a j q =
      ((outputNormalizer d a j).1 (secondVector q (d.parent a)),
        (outputNormalizer d a j).1 (firstVector d q a)) :=
  rfl

/-- Normalizing by an invertible symplectic map does not destroy the
surjectivity of the two-free-vector projection. -/
theorem normalizedOutputPairCLM_surjective (a : A) (j : Fin 4) :
    Function.Surjective (normalizedOutputPairCLM d a j) := by
  rintro ⟨x, y⟩
  let g := (outputNormalizer d a j).1
  obtain ⟨q, hq⟩ := outputPairCLM_surjective d a (g⁻¹ x, g⁻¹ y)
  refine ⟨q, ?_⟩
  have hx := congrArg Prod.fst hq
  have hy := congrArg Prod.snd hq
  apply Prod.ext
  · simpa [g] using congrArg (fun v ↦ g v) hx
  · simpa [g] using congrArg (fun v ↦ g v) hy

/-! ## The three finite families of genericity conditions -/

/-- Literal vectors for the first cone over one paired face atom. -/
def firstConeVectors (a : A) (q : Parameter I A) :
    Fin 5 → SymplecticVector :=
  Fin.cons (firstVector d q a)
    (projectiveRepresentatives (p.faceBase (d.occurrence a)).1)

/-- Literal vectors for coning one original parent facet by its second apex. -/
def secondFacetVectors (s : I) (q : Parameter I A) :
    Fin 6 → SymplecticVector :=
  Fin.cons (secondVector q s)
    (projectiveRepresentatives (p.facet s).1)

/-- Literal vectors for the six-tuple consisting of the second apex, the
first apex, and one four-point face atom. -/
def doubleConeVectors (a : A) (q : Parameter I A) :
    Fin 6 → SymplecticVector :=
  Fin.cons (secondVector q (d.parent a))
    (Fin.cons (firstVector d q a)
      (projectiveRepresentatives (p.faceBase (d.occurrence a)).1))

def firstConeFamily (a : A) :
    AnalyticConfigFamily (Parameter I A) 5 where
  vec := firstConeVectors d a
  analytic := by
    intro i
    fin_cases i
    · change AnalyticOnNhd ℂ (fun q : Parameter I A ↦
        firstVector d q a) Set.univ
      simpa [firstVector] using (firstVectorCLM d a).analyticOnNhd Set.univ
    · exact analyticOnNhd_const
    · exact analyticOnNhd_const
    · exact analyticOnNhd_const
    · exact analyticOnNhd_const
  four_le := by norm_num

def secondFacetFamily (s : I) :
    AnalyticConfigFamily (Parameter I A) 6 where
  vec := secondFacetVectors (p := p) (A := A) s
  analytic := by
    intro i
    fin_cases i
    · change AnalyticOnNhd ℂ (fun q : Parameter I A ↦
        secondVector q s) Set.univ
      simpa [secondVector] using
        (secondVectorCLM (A := A) s).analyticOnNhd Set.univ
    · exact analyticOnNhd_const
    · exact analyticOnNhd_const
    · exact analyticOnNhd_const
    · exact analyticOnNhd_const
    · exact analyticOnNhd_const
  four_le := by norm_num

def doubleConeFamily (a : A) :
    AnalyticConfigFamily (Parameter I A) 6 where
  vec := doubleConeVectors d a
  analytic := by
    intro i
    fin_cases i
    · change AnalyticOnNhd ℂ (fun q : Parameter I A ↦
        secondVector q (d.parent a)) Set.univ
      simpa [secondVector] using
        (secondVectorCLM (A := A) (d.parent a)).analyticOnNhd Set.univ
    · change AnalyticOnNhd ℂ (fun q : Parameter I A ↦
        firstVector d q a) Set.univ
      simpa [firstVector] using (firstVectorCLM d a).analyticOnNhd Set.univ
    · exact analyticOnNhd_const
    · exact analyticOnNhd_const
    · exact analyticOnNhd_const
    · exact analyticOnNhd_const
  four_le := by norm_num

abbrev FamilyIndex (I A : Type*) := I ⊕ (A ⊕ A)

def familySize : FamilyIndex I A → ℕ
  | Sum.inl _ => 6
  | Sum.inr (Sum.inl _) => 5
  | Sum.inr (Sum.inr _) => 6

/-- The complete finite list of generic configurations required by both
cone identities. -/
def family : (j : FamilyIndex I A) →
    AnalyticConfigFamily (Parameter I A) (familySize j)
  | Sum.inl s => secondFacetFamily (p := p) (A := A) s
  | Sum.inr (Sum.inl a) => firstConeFamily d a
  | Sum.inr (Sum.inr a) => doubleConeFamily d a

theorem exists_firstConeFamily_good (a : A) :
    ∃ q, (firstConeFamily d a).Good q := by
  let b := p.faceBase (d.occurrence a)
  obtain ⟨y, hy⟩ := exists_common_generic_cons
    (fun _ : Unit ↦ b) (by norm_num)
  obtain ⟨q, hq⟩ := firstVectorCLM_surjective d a y.rep
  have hfirst : firstVector d q a = y.rep := by
    simpa [firstVector] using hq
  have hv : ∀ i, (firstConeFamily d a).vec q i ≠ 0 := by
    intro i
    fin_cases i
    · simpa [firstConeFamily, firstConeVectors, hfirst] using y.rep_nonzero
    · exact projectiveRepresentatives_ne_zero b.1 0
    · exact projectiveRepresentatives_ne_zero b.1 1
    · exact projectiveRepresentatives_ne_zero b.1 2
    · exact projectiveRepresentatives_ne_zero b.1 3
  refine ⟨q, (firstConeFamily d a).good_of_projectivized_generic hv ?_⟩
  have heq :
      (fun i ↦ Projectivization.mk ℂ ((firstConeFamily d a).vec q i) (hv i)) =
        Fin.cons y b.1 := by
    funext i
    fin_cases i
    · simpa [firstConeFamily, firstConeVectors, hfirst] using
        Projectivization.mk_rep y
    · change Projectivization.mk ℂ
        (projectiveRepresentatives (p.faceBase (d.occurrence a)).1 0) _ =
          (p.faceBase (d.occurrence a)).1 0
      exact Projectivization.mk_rep _
    · change Projectivization.mk ℂ
        (projectiveRepresentatives (p.faceBase (d.occurrence a)).1 1) _ =
          (p.faceBase (d.occurrence a)).1 1
      exact Projectivization.mk_rep _
    · change Projectivization.mk ℂ
        (projectiveRepresentatives (p.faceBase (d.occurrence a)).1 2) _ =
          (p.faceBase (d.occurrence a)).1 2
      exact Projectivization.mk_rep _
    · change Projectivization.mk ℂ
        (projectiveRepresentatives (p.faceBase (d.occurrence a)).1 3) _ =
          (p.faceBase (d.occurrence a)).1 3
      exact Projectivization.mk_rep _
  rw [heq]
  exact hy ()

theorem exists_secondFacetFamily_good (s : I) :
    ∃ q, (secondFacetFamily (p := p) (A := A) s).Good q := by
  obtain ⟨x, hx⟩ := exists_common_generic_cons
    (fun _ : Unit ↦ p.facet s) (by norm_num)
  obtain ⟨q, hq⟩ := secondVectorCLM_surjective (A := A) s x.rep
  have hsecond : secondVector q s = x.rep := by
    simpa [secondVector] using hq
  have hv : ∀ i, (secondFacetFamily (p := p) (A := A) s).vec q i ≠ 0 := by
    intro i
    fin_cases i
    · change secondVector q s ≠ 0
      rw [hsecond]
      exact x.rep_nonzero
    · exact projectiveRepresentatives_ne_zero (p.facet s).1 0
    · exact projectiveRepresentatives_ne_zero (p.facet s).1 1
    · exact projectiveRepresentatives_ne_zero (p.facet s).1 2
    · exact projectiveRepresentatives_ne_zero (p.facet s).1 3
    · exact projectiveRepresentatives_ne_zero (p.facet s).1 4
  refine ⟨q, (secondFacetFamily (p := p) (A := A) s
    ).good_of_projectivized_generic hv ?_⟩
  have heq :
      (fun i ↦ Projectivization.mk ℂ
        ((secondFacetFamily (p := p) (A := A) s).vec q i) (hv i)) =
        Fin.cons x (p.facet s).1 := by
    funext i
    fin_cases i
    · change Projectivization.mk ℂ (secondVector q s) _ = x
      calc
        Projectivization.mk ℂ (secondVector q s) _ =
            Projectivization.mk ℂ x.rep x.rep_nonzero := by
          apply (Projectivization.mk_eq_mk_iff' (K := ℂ)
            (secondVector q s) x.rep _ _).2
          exact ⟨1, by simpa using hsecond.symm⟩
        _ = x := Projectivization.mk_rep x
    · change Projectivization.mk ℂ
        (projectiveRepresentatives (p.facet s).1 0) _ = (p.facet s).1 0
      exact Projectivization.mk_rep _
    · change Projectivization.mk ℂ
        (projectiveRepresentatives (p.facet s).1 1) _ = (p.facet s).1 1
      exact Projectivization.mk_rep _
    · change Projectivization.mk ℂ
        (projectiveRepresentatives (p.facet s).1 2) _ = (p.facet s).1 2
      exact Projectivization.mk_rep _
    · change Projectivization.mk ℂ
        (projectiveRepresentatives (p.facet s).1 3) _ = (p.facet s).1 3
      exact Projectivization.mk_rep _
    · change Projectivization.mk ℂ
        (projectiveRepresentatives (p.facet s).1 4) _ = (p.facet s).1 4
      exact Projectivization.mk_rep _
  rw [heq]
  exact hx ()

theorem exists_doubleConeFamily_good (a : A) :
    ∃ q, (doubleConeFamily d a).Good q := by
  let b := p.faceBase (d.occurrence a)
  obtain ⟨y, hy⟩ := exists_common_generic_cons
    (fun _ : Unit ↦ b) (by norm_num)
  let yb : OrbitChain.GenericConfig 5 := ⟨Fin.cons y b.1, hy ()⟩
  obtain ⟨x, hx⟩ := exists_common_generic_cons
    (fun _ : Unit ↦ yb) (by norm_num)
  obtain ⟨q, hq⟩ := outputPairCLM_surjective d a (x.rep, y.rep)
  have hsecond : secondVector q (d.parent a) = x.rep := by
    exact congrArg Prod.fst hq
  have hfirst : firstVector d q a = y.rep := by
    exact congrArg Prod.snd hq
  have hv : ∀ i, (doubleConeFamily d a).vec q i ≠ 0 := by
    intro i
    fin_cases i
    · change secondVector q (d.parent a) ≠ 0
      rw [hsecond]
      exact x.rep_nonzero
    · simpa [doubleConeFamily, doubleConeVectors, hfirst] using y.rep_nonzero
    · exact projectiveRepresentatives_ne_zero b.1 0
    · exact projectiveRepresentatives_ne_zero b.1 1
    · exact projectiveRepresentatives_ne_zero b.1 2
    · exact projectiveRepresentatives_ne_zero b.1 3
  refine ⟨q, (doubleConeFamily d a).good_of_projectivized_generic hv ?_⟩
  have heq :
      (fun i ↦ Projectivization.mk ℂ ((doubleConeFamily d a).vec q i) (hv i)) =
        Fin.cons x (Fin.cons y b.1) := by
    funext i
    fin_cases i
    · change Projectivization.mk ℂ (secondVector q (d.parent a)) _ = x
      calc
        Projectivization.mk ℂ (secondVector q (d.parent a)) _ =
            Projectivization.mk ℂ x.rep x.rep_nonzero := by
          apply (Projectivization.mk_eq_mk_iff' (K := ℂ)
            (secondVector q (d.parent a)) x.rep _ _).2
          exact ⟨1, by simpa using hsecond.symm⟩
        _ = x := Projectivization.mk_rep x
    · simpa [doubleConeFamily, doubleConeVectors, hfirst] using
        Projectivization.mk_rep y
    · change Projectivization.mk ℂ
        (projectiveRepresentatives (p.faceBase (d.occurrence a)).1 0) _ =
          (p.faceBase (d.occurrence a)).1 0
      exact Projectivization.mk_rep _
    · change Projectivization.mk ℂ
        (projectiveRepresentatives (p.faceBase (d.occurrence a)).1 1) _ =
          (p.faceBase (d.occurrence a)).1 1
      exact Projectivization.mk_rep _
    · change Projectivization.mk ℂ
        (projectiveRepresentatives (p.faceBase (d.occurrence a)).1 2) _ =
          (p.faceBase (d.occurrence a)).1 2
      exact Projectivization.mk_rep _
    · change Projectivization.mk ℂ
        (projectiveRepresentatives (p.faceBase (d.occurrence a)).1 3) _ =
          (p.faceBase (d.occurrence a)).1 3
      exact Projectivization.mk_rep _
  rw [heq]
  exact hx ()

theorem family_individually_realizable (j : FamilyIndex I A) :
    ∃ q, (family d j).Good q := by
  rcases j with s | a
  · exact exists_secondFacetFamily_good (p := p) (A := A) s
  · rcases a with a | a
    · exact exists_firstConeFamily_good d a
    · exact exists_doubleConeFamily_good d a

/-! ## One common open parameter locus -/

/-- For each elementary output, record the two nonvanishing fourth
coordinates needed for the affine two-free chart. -/
abbrev ChartIndex (A : Type*) := A × (Fin 4 × Fin 2)

/-- The fourth coordinate of either normalized free vector, as a continuous
complex-linear functional of the shared parameter. -/
noncomputable def chartScalarCLM (k : ChartIndex A) :
    Parameter I A →L[ℂ] ℂ :=
  let L := normalizedOutputPairCLM d k.1 k.2.1
  if k.2.2 = 0 then
    (ContinuousLinearMap.proj (R := ℂ) (3 : Fin 4)).comp
      ((ContinuousLinearMap.fst ℂ SymplecticVector SymplecticVector).comp L)
  else
    (ContinuousLinearMap.proj (R := ℂ) (3 : Fin 4)).comp
      ((ContinuousLinearMap.snd ℂ SymplecticVector SymplecticVector).comp L)

noncomputable def chartScalar (k : ChartIndex A) (q : Parameter I A) : ℂ :=
  chartScalarCLM d k q

theorem chartScalar_analytic (k : ChartIndex A) :
    AnalyticOnNhd ℂ (chartScalar d k) Set.univ := by
  change AnalyticOnNhd ℂ (fun q ↦ chartScalarCLM d k q) Set.univ
  exact (chartScalarCLM d k).analyticOnNhd Set.univ

theorem chartScalar_nontrivial (k : ChartIndex A) :
    ∃ q, chartScalar d k q ≠ 0 := by
  rcases k with ⟨a, j, k⟩
  fin_cases k
  · obtain ⟨q, hq⟩ := normalizedOutputPairCLM_surjective d a j
      (TwoFree.f2, 0)
    refine ⟨q, ?_⟩
    have hfst := congrArg Prod.fst hq
    have heq : chartScalar d (a, j, 0) q = 1 := by
      simpa [chartScalar, chartScalarCLM, TwoFree.f2] using
        congrArg (fun v : SymplecticVector ↦ v 3) hfst
    change chartScalar d (a, j, 0) q ≠ 0
    rw [heq]
    norm_num
  · obtain ⟨q, hq⟩ := normalizedOutputPairCLM_surjective d a j
      (0, TwoFree.f2)
    refine ⟨q, ?_⟩
    have hsnd := congrArg Prod.snd hq
    have heq : chartScalar d (a, j, 1) q = 1 := by
      simpa [chartScalar, chartScalarCLM, TwoFree.f2] using
        congrArg (fun v : SymplecticVector ↦ v 3) hsnd
    change chartScalar d (a, j, 1) q ≠ 0
    rw [heq]
    norm_num

/-- All genericity and affine-chart requirements imposed simultaneously on
one shared finite-dimensional parameter. -/
def goodParameterSet : Set (Parameter I A) :=
  simultaneouslyGoodAndScalarSet (family d) (chartScalar d)

theorem goodParameterSet_isOpen_dense :
    IsOpen (goodParameterSet d) ∧ Dense (goodParameterSet d) := by
  exact simultaneouslyGoodAndScalarSet_isOpen_dense
    (family d) (family_individually_realizable d)
    (chartScalar d) (chartScalar_analytic d) (chartScalar_nontrivial d)

theorem goodParameterSet_nonempty : (goodParameterSet d).Nonempty := by
  have hdense := (goodParameterSet_isOpen_dense d).2
  simpa using hdense.inter_open_nonempty Set.univ isOpen_univ Set.univ_nonempty

/-- The shared parameter space restricted to the common open dense locus. -/
abbrev GoodParameter := {q : Parameter I A // q ∈ goodParameterSet d}

namespace GoodParameter

variable {d}

theorem secondFacetGood (q : GoodParameter d) (s : I) :
    (secondFacetFamily (p := p) (A := A) s).Good q.1 := by
  exact q.2.1 (Sum.inl s)

theorem firstConeGood (q : GoodParameter d) (a : A) :
    (firstConeFamily d a).Good q.1 := by
  exact q.2.1 (Sum.inr (Sum.inl a))

theorem doubleConeGood (q : GoodParameter d) (a : A) :
    (doubleConeFamily d a).Good q.1 := by
  exact q.2.1 (Sum.inr (Sum.inr a))

theorem chart_ne (q : GoodParameter d) (a : A) (j : Fin 4) (k : Fin 2) :
    chartScalar d (a, j, k) q.1 ≠ 0 := by
  exact q.2.2 (a, j, k)

end GoodParameter

/-! ## Recovering the two cone systems from a good parameter -/

theorem firstVector_ne_zero (q : GoodParameter d) (a : A) :
    firstVector d q.1 a ≠ 0 := by
  simpa [firstConeFamily, firstConeVectors] using
    (firstConeFamily d a).vec_ne_zero (q.firstConeGood a) 0

/-- The first projective apex at an oriented atom. -/
def firstApex (q : GoodParameter d) (a : A) : ProjectivePoint :=
  Projectivization.mk ℂ (firstVector d q.1 a) (firstVector_ne_zero d q a)

theorem firstApex_eq_mk (q : GoodParameter d) (a : A) :
    firstApex d q a = Projectivization.mk ℂ (firstVector d q.1 a)
      (firstVector_ne_zero d q a) :=
  rfl

/-- Projectivizing the literal mate identity gives exactly the required
equivariance of the first apex. -/
theorem firstApex_mate (q : GoodParameter d) (a : A) :
    firstApex d q (d.mate a) =
      d.coherentGroup a • firstApex d q a := by
  change Projectivization.mk ℂ (firstVector d q.1 (d.mate a)) _ =
    (d.coherentGroup a).1 •
      Projectivization.mk ℂ (firstVector d q.1 a) _
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  exact ⟨1, by simpa using (firstVector_mate d q.1 a).symm⟩

/-- The analytic first-cone family, packaged as a generic configuration. -/
def firstConeConfig (q : GoodParameter d) (a : A) :
    OrbitChain.GenericConfig 5 :=
  ⟨(firstConeFamily d a).config q.1 (q.firstConeGood a),
    (firstConeFamily d a).config_generic (q.firstConeGood a)⟩

theorem firstConeConfig_val (q : GoodParameter d) (a : A) :
    (firstConeConfig d q a).1 =
      MeasureChain.coneTuple (firstApex d q a)
        (p.faceBase (d.occurrence a)).1 := by
  funext i
  fin_cases i
  · rfl
  · exact Projectivization.mk_rep _
  · exact Projectivization.mk_rep _
  · exact Projectivization.mk_rep _
  · exact Projectivization.mk_rep _

theorem firstCone_generic (q : GoodParameter d) (a : A) :
    IsGeneric (MeasureChain.coneTuple (firstApex d q a)
      (p.faceBase (d.occurrence a)).1) := by
  rw [← firstConeConfig_val d q a]
  exact (firstConeConfig d q a).2

theorem firstFace_generic (q : GoodParameter d) (a : A) (j : Fin 4) :
    IsGeneric (MeasureChain.coneTuple (firstApex d q a)
      (OrbitChain.face j (p.faceBase (d.occurrence a))).1) :=
  MeasureChain.coneTuple_delete_generic _ _ (firstCone_generic d q a) j

/-- The shared parameter supplies a compatible paired first-apex choice. -/
def pairedApexChoice (q : GoodParameter d) :
    MeasureChain.PairedApexChoice p d where
  apex := firstApex d q
  apex_transport := firstApex_mate d q
  cone_generic := firstCone_generic d q
  face_generic := firstFace_generic d q

/-- The resulting complete algebraic first-cone system. -/
def firstConeSystem (q : GoodParameter d) :
    MeasureChain.FirstConeSystem I A :=
  (pairedApexChoice d q).toFirstConeSystem

theorem secondVector_ne_zero (q : GoodParameter d) (s : I) :
    secondVector q.1 s ≠ 0 := by
  simpa [secondFacetFamily, secondFacetVectors] using
    (secondFacetFamily (p := p) (A := A) s).vec_ne_zero
      (q.secondFacetGood s) 0

/-- The shared second apex attached to a parent facet. -/
def secondApex (q : GoodParameter d) (s : I) : ProjectivePoint :=
  Projectivization.mk ℂ (secondVector q.1 s) (secondVector_ne_zero d q s)

/-- The analytic second-apex/parent-facet family as a generic six-tuple. -/
def secondFacetConfig (q : GoodParameter d) (s : I) :
    OrbitChain.GenericConfig 6 :=
  ⟨(secondFacetFamily (p := p) (A := A) s).config q.1
      (q.secondFacetGood s),
    (secondFacetFamily (p := p) (A := A) s).config_generic
      (q.secondFacetGood s)⟩

theorem secondFacetConfig_val (q : GoodParameter d) (s : I) :
    (secondFacetConfig d q s).1 =
      MeasureChain.coneTuple (secondApex d q s) (p.facet s).1 := by
  funext i
  fin_cases i
  · rfl
  · exact Projectivization.mk_rep _
  · exact Projectivization.mk_rep _
  · exact Projectivization.mk_rep _
  · exact Projectivization.mk_rep _
  · exact Projectivization.mk_rep _

theorem secondFacetCone_generic (q : GoodParameter d) (s : I) :
    IsGeneric
      (MeasureChain.coneTuple (secondApex d q s) (p.facet s).1) := by
  rw [← secondFacetConfig_val d q s]
  exact (secondFacetConfig d q s).2

theorem secondFacetFace_generic (q : GoodParameter d) (s : I)
    (i : Fin 5) :
    IsGeneric (MeasureChain.coneTuple (secondApex d q s)
      (OrbitChain.face i (p.facet s)).1) :=
  MeasureChain.coneTuple_delete_generic _ _
    (secondFacetCone_generic d q s) i

/-- The analytic double-cone family as a generic six-tuple. -/
def doubleConeConfig (q : GoodParameter d) (a : A) :
    OrbitChain.GenericConfig 6 :=
  ⟨(doubleConeFamily d a).config q.1 (q.doubleConeGood a),
    (doubleConeFamily d a).config_generic (q.doubleConeGood a)⟩

theorem doubleConeConfig_val (q : GoodParameter d) (a : A) :
    (doubleConeConfig d q a).1 =
      MeasureChain.coneTuple (secondApex d q (d.parent a))
        ((firstConeSystem d q).first a).cone.1 := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact Projectivization.mk_rep _
  · exact Projectivization.mk_rep _
  · exact Projectivization.mk_rep _
  · exact Projectivization.mk_rep _

theorem secondFirstCone_generic (q : GoodParameter d) (a : A) :
    IsGeneric
      (MeasureChain.coneTuple (secondApex d q (d.parent a))
        ((firstConeSystem d q).first a).cone.1) := by
  rw [← doubleConeConfig_val d q a]
  exact (doubleConeConfig d q a).2

theorem secondFirstFace_generic (q : GoodParameter d) (a : A)
    (i : Fin 5) :
    IsGeneric
      (MeasureChain.coneTuple (secondApex d q (d.parent a))
        (OrbitChain.face i ((firstConeSystem d q).first a).cone).1) :=
  MeasureChain.coneTuple_delete_generic _ _
    (secondFirstCone_generic d q a) i

theorem secondSideCone_generic (q : GoodParameter d) (a : A)
    (j : Fin 4) :
    IsGeneric
      (MeasureChain.coneTuple (secondApex d q (d.parent a))
        (((firstConeSystem d q).first a).sideFace j).1) := by
  simpa only [MeasureChain.ConeDatum.face_succ_cone] using
    secondFirstFace_generic d q a j.succ

theorem secondSideFace_generic (q : GoodParameter d) (a : A)
    (j i : Fin 4) :
    IsGeneric
      (MeasureChain.coneTuple (secondApex d q (d.parent a))
        (OrbitChain.face i
          (((firstConeSystem d q).first a).sideFace j)).1) :=
  MeasureChain.coneTuple_delete_generic _ _
    (secondSideCone_generic d q a j) i

/-- Both levels of the article's cone construction, with all genericity
proofs extracted from the one common analytic parameter locus. -/
def secondConeSystem (q : GoodParameter d) :
    MeasureChain.SecondConeSystem (firstConeSystem d q) where
  apex := secondApex d q
  facetCone_generic := secondFacetCone_generic d q
  facetFace_generic := secondFacetFace_generic d q
  firstCone_generic := secondFirstCone_generic d q
  firstFace_generic := secondFirstFace_generic d q
  sideCone_generic := secondSideCone_generic d q
  sideFace_generic := secondSideFace_generic d q

/-! ## Elementary outputs and their explicit quotient coordinates -/

/-- One of the four side-cone generators contributed by an oriented atom. -/
def outputConfig (q : GoodParameter d) (a : A) (j : Fin 4) :
    OrbitChain.GenericConfig 5 :=
  MeasureChain.coneConfig (secondApex d q (d.parent a))
    (((firstConeSystem d q).first a).sideFace j)
    (secondSideCone_generic d q a j)

/-- An elementary output is literally `(second apex, first apex, fixed
triple)`, in this order. -/
theorem outputConfig_val (q : GoodParameter d) (a : A) (j : Fin 4) :
    (outputConfig d q a j).1 =
      TwoFree.withTriple (outputTriple d a j).1
        (secondApex d q (d.parent a)) (firstApex d q a) := by
  funext i
  fin_cases i <;> rfl

def outputAffineParam (q : Parameter I A) (a : A) (j : Fin 4) :
    TwoFree.Param :=
  TwoFree.affineParamOfPair (normalizedOutputPairCLM d a j q)

theorem normalizedOutput_fst_last_ne (q : GoodParameter d)
    (a : A) (j : Fin 4) :
    (normalizedOutputPairCLM d a j q.1).1 3 ≠ 0 := by
  simpa [chartScalar, chartScalarCLM] using q.chart_ne a j 0

theorem normalizedOutput_snd_last_ne (q : GoodParameter d)
    (a : A) (j : Fin 4) :
    (normalizedOutputPairCLM d a j q.1).2 3 ≠ 0 := by
  simpa [chartScalar, chartScalarCLM] using q.chart_ne a j 1

/-- The fixed symplectic normalizer identifies the actual elementary output
with the explicit standard two-free chart. -/
theorem normalizedOutputConfig_val (q : GoodParameter d)
    (a : A) (j : Fin 4) :
    (OrbitChain.smulGeneric (outputNormalizer d a j)
      (outputConfig d q a j)).1 =
        TwoFree.standardFiveConfig (outputAffineParam d q.1 a j) := by
  change outputNormalizer d a j • (outputConfig d q a j).1 =
    TwoFree.standardFiveConfig (outputAffineParam d q.1 a j)
  rw [outputConfig_val]
  funext i
  fin_cases i
  · change (outputNormalizer d a j).1 •
        Projectivization.mk ℂ (secondVector q.1 (d.parent a)) _ = _
    rw [Projectivization.smul_mk]
    simpa [outputAffineParam, LinearEquiv.smul_def] using
      (TwoFree.standardFiveConfig_affineParam_zero
        (normalizedOutputPairCLM d a j q.1)
        (normalizedOutput_fst_last_ne d q a j)
        (normalizedOutput_snd_last_ne d q a j)).symm
  · change (outputNormalizer d a j).1 •
        Projectivization.mk ℂ (firstVector d q.1 a) _ = _
    rw [Projectivization.smul_mk]
    simpa [outputAffineParam, LinearEquiv.smul_def] using
      (TwoFree.standardFiveConfig_affineParam_one
        (normalizedOutputPairCLM d a j q.1)
        (normalizedOutput_fst_last_ne d q a j)
        (normalizedOutput_snd_last_ne d q a j)).symm
  · exact congrFun (outputNormalizer_spec d a j) 0
  · exact congrFun (outputNormalizer_spec d a j) 1
  · exact congrFun (outputNormalizer_spec d a j) 2

theorem outputAffineParam_generic (q : GoodParameter d)
    (a : A) (j : Fin 4) :
    IsGeneric (TwoFree.standardFiveConfig (outputAffineParam d q.1 a j)) := by
  rw [← normalizedOutputConfig_val d q a j]
  exact (OrbitChain.smulGeneric (outputNormalizer d a j)
    (outputConfig d q a j)).2

/-- The ambient rational coordinate map used for coarea.  On the good locus
it is the actual orbit coordinate of the elementary output. -/
def outputAmbientCoord (a : A) (j : Fin 4) (q : Parameter I A) :
    Pfaffian.Coord5 :=
  TwoFree.betaFormula (outputAffineParam d q a j)

theorem outputAmbientCoord_hasSurjectiveComplexFDerivAt
    (q : GoodParameter d) (a : A) (j : Fin 4) :
    HasSurjectiveComplexFDerivAt (outputAmbientCoord d a j) q.1 := by
  exact TwoFree.betaFormula_comp_affineParam_compCLM_hasSurjectiveComplexFDerivAt
    (normalizedOutputPairCLM d a j)
    (normalizedOutputPairCLM_surjective d a j) q.1
    (normalizedOutput_fst_last_ne d q a j)
    (normalizedOutput_snd_last_ne d q a j)
    (outputAffineParam_generic d q a j)

theorem outputOrbitCoord_val (q : GoodParameter d) (a : A) (j : Fin 4) :
    (Pfaffian.orbitCoord5 (outputConfig d q a j)).1 =
      outputAmbientCoord d a j q.1 := by
  let std : OrbitChain.GenericConfig 5 :=
    ⟨TwoFree.standardFiveConfig (outputAffineParam d q.1 a j),
      outputAffineParam_generic d q a j⟩
  have hstd : OrbitChain.smulGeneric (outputNormalizer d a j)
      (outputConfig d q a j) = std :=
    Subtype.ext (normalizedOutputConfig_val d q a j)
  calc
    (Pfaffian.orbitCoord5 (outputConfig d q a j)).1 =
        (Pfaffian.orbitCoord5 (OrbitChain.smulGeneric
          (outputNormalizer d a j) (outputConfig d q a j))).1 := by
            rw [Pfaffian.orbitCoord5_smulGeneric]
    _ = (Pfaffian.orbitCoord5 std).1 := by rw [hstd]
    _ = outputAmbientCoord d a j q.1 := by
      simpa [std, TwoFree.beta, outputAmbientCoord] using
        TwoFree.beta_val
          (⟨outputAffineParam d q.1 a j,
            outputAffineParam_generic d q a j⟩ : TwoFree.Domain)

/-! ## Gaussian measure and nonsingularity of every output map -/

/-- Arbitrary finite-dimensional linear coordinates on the shared literal
parameter space. -/
noncomputable def parameterCoordinates : Parameter I A ≃L[ℂ]
    (Fin (Module.finrank ℂ (Parameter I A)) → ℂ) :=
  (Module.finBasis ℂ (Parameter I A)).equivFun.toContinuousLinearEquiv

/-- Independent complex Gaussians transported to the shared parameter
space. -/
def parameterGaussian : Measure (Parameter I A) :=
  Measure.map (parameterCoordinates (I := I) (A := A)).symm
    (standardComplexGaussianPi (Module.finrank ℂ (Parameter I A)))

instance parameterGaussian_isProbability :
    IsProbabilityMeasure (parameterGaussian (I := I) (A := A)) :=
  Measure.isProbabilityMeasure_map
    (parameterCoordinates (I := I) (A := A)).symm.continuous.measurable.aemeasurable

instance parameterGaussian_isOpenPos :
    Measure.IsOpenPosMeasure (parameterGaussian (I := I) (A := A)) :=
  (parameterCoordinates (I := I) (A := A)).symm.continuous.isOpenPosMeasure_map
    (parameterCoordinates (I := I) (A := A)).symm.surjective

def parameterGaussianPresentation :
    GaussianCoordinatePresentation (parameterGaussian (I := I) (A := A)) where
  dimension := Module.finrank ℂ (Parameter I A)
  coordinates := parameterCoordinates (I := I) (A := A)
  measure_eq := rfl

/-- The normalized Gaussian restriction to the simultaneous good locus. -/
def goodParameterMeasure : Measure (GoodParameter d) :=
  normalizedOpenMeasure (parameterGaussian (I := I) (A := A))
    (goodParameterSet d) (goodParameterSet_isOpen_dense d).1
      (goodParameterSet_nonempty d)

instance goodParameterMeasure_isProbability :
    IsProbabilityMeasure (goodParameterMeasure d) :=
  normalizedOpenMeasure_isProbability
    (parameterGaussian (I := I) (A := A)) (goodParameterSet d)
      (goodParameterSet_isOpen_dense d).1 (goodParameterSet_nonempty d)

instance goodParameterMeasure_isOpenPos :
    Measure.IsOpenPosMeasure (goodParameterMeasure d) :=
  normalizedOpenMeasure_isOpenPos
    (parameterGaussian (I := I) (A := A)) (goodParameterSet d)
      (goodParameterSet_isOpen_dense d).1 (goodParameterSet_nonempty d)

theorem outputAmbientCoord_mem (q : GoodParameter d) (a : A) (j : Fin 4) :
    Pfaffian.IsU5 (outputAmbientCoord d a j q.1) := by
  let dom : TwoFree.Domain :=
    ⟨outputAffineParam d q.1 a j, outputAffineParam_generic d q a j⟩
  have hmem := (TwoFree.beta dom).2
  rw [TwoFree.beta_val dom] at hmem
  exact hmem

/-- The elementary output coordinate, written using the ambient rational
formula so that the coarea theorem applies directly. -/
def outputCoord (a : A) (j : Fin 4) (q : GoodParameter d) : Pfaffian.U5 :=
  ⟨outputAmbientCoord d a j q.1, outputAmbientCoord_mem d q a j⟩

theorem outputCoord_eq_orbitCoord (q : GoodParameter d)
    (a : A) (j : Fin 4) :
    outputCoord d a j q = Pfaffian.orbitCoord5 (outputConfig d q a j) := by
  apply Subtype.ext
  exact (outputOrbitCoord_val d q a j).symm

/-- Coarea makes each elementary output nonsingular for the reference
measure class on the five-point quotient. -/
theorem outputCoord_quasiMeasurePreserving (a : A) (j : Fin 4) :
    Measure.QuasiMeasurePreserving (outputCoord d a j)
      (goodParameterMeasure d) Pfaffian.measureU5 := by
  have hmem : ∀ x, x ∈ goodParameterSet d →
      outputAmbientCoord d a j x ∈ Pfaffian.u5Set := by
    intro x hx
    exact outputAmbientCoord_mem d ⟨x, hx⟩ a j
  have h := quasiMeasurePreserving_normalizedOpenGaussian_of_submersion
    (parameterGaussian (I := I) (A := A)) Pfaffian.coord5Gaussian
    parameterGaussianPresentation Pfaffian.coord5GaussianPresentation
    (goodParameterSet d) (goodParameterSet_isOpen_dense d).1
      (goodParameterSet_nonempty d)
    Pfaffian.u5Set Pfaffian.isOpen_u5Set Pfaffian.u5Set_nonempty
    (outputAmbientCoord d a j) hmem
    (by
      intro x hx
      exact outputAmbientCoord_hasSurjectiveComplexFDerivAt d ⟨x, hx⟩ a j)
  change Measure.QuasiMeasurePreserving (outputCoord d a j)
    (normalizedOpenMeasure (parameterGaussian (I := I) (A := A))
      (goodParameterSet d) (goodParameterSet_isOpen_dense d).1
        (goodParameterSet_nonempty d))
    (normalizedOpenMeasure Pfaffian.coord5Gaussian Pfaffian.u5Set
      Pfaffian.isOpen_u5Set Pfaffian.u5Set_nonempty)
  let f : GoodParameter d → Pfaffian.U5 := fun x ↦
    ⟨outputAmbientCoord d a j x.1, hmem x.1 x.2⟩
  have hf : f = outputCoord d a j := by
    funext x
    apply Subtype.ext
    rfl
  rw [← hf]
  exact h

/-- Nonsingularity remains true after every vertex permutation, exactly as
required by the alternating measure-chain construction. -/
theorem permutedOutputCoord_quasiMeasurePreserving
    (a : A) (j : Fin 4) (sigma : Equiv.Perm (Fin 5)) :
    Measure.QuasiMeasurePreserving
      (fun q : GoodParameter d ↦
        Pfaffian.permute5 sigma
          (Pfaffian.orbitCoord5 (outputConfig d q a j)))
      (goodParameterMeasure d) Pfaffian.measureU5 := by
  have hcomp := (Pfaffian.permute5_quasiMeasurePreserving sigma).comp
    (outputCoord_quasiMeasurePreserving d a j)
  have heq : (fun q : GoodParameter d ↦
        Pfaffian.permute5 sigma
          (Pfaffian.orbitCoord5 (outputConfig d q a j))) =
      Pfaffian.permute5 sigma ∘ outputCoord d a j := by
    funext q
    exact congrArg (Pfaffian.permute5 sigma)
      (outputCoord_eq_orbitCoord d q a j).symm
  rw [heq]
  exact hcomp

/-! ## The parameterized finite output chain -/

abbrev OutputIndex (A : Type*) := A × Fin 4

def outputCoefficient (k : OutputIndex A) : ℝ :=
  d.atomCoeff k.1 * (-1 : ℝ) ^ k.2.val

def outputFamily (k : OutputIndex A) (q : GoodParameter d) :
    OrbitChain.GenericConfig 5 :=
  outputConfig d q k.1 k.2

theorem sideCone_eq_outputConfig (q : GoodParameter d)
    (a : A) (j : Fin 4) :
    (secondConeSystem d q).sideCone a j = outputConfig d q a j :=
  rfl

/-- The finite family used for diffusion is exactly the algebraic
second-cone output, including repetitions and all three kinds of signs. -/
theorem orbitChainAt_outputFamily (q : GoodParameter d) :
    MeasureChain.orbitChainAt (outputCoefficient d) (outputFamily d) q =
      (secondConeSystem d q).secondChain := by
  classical
  rw [MeasureChain.orbitChainAt, Fintype.sum_prod_type,
    MeasureChain.SecondConeSystem.secondChain_eq_sum_sideCone]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro j _hj
  rfl

theorem orbitChainAt_outputFamily_boundary (q : GoodParameter d) :
    OrbitChain.boundary ℝ 4
      (MeasureChain.orbitChainAt (outputCoefficient d) (outputFamily d) q) = 0 := by
  rw [orbitChainAt_outputFamily]
  exact (secondConeSystem d q).boundary_secondChain

/-- The original chain represented by the fixed weighted presentation. -/
def presentedChain : OrbitChain.Module ℝ 5 :=
  ∑ s : I, p.coeff s • OrbitChain.ofConfig (R := ℝ) (p.facet s)

theorem presentedChain_boundary :
    OrbitChain.boundary ℝ 4 (presentedChain (p := p)) = 0 :=
  p.isCycle

theorem secondConeSystem_facetChain (q : GoodParameter d) :
    (secondConeSystem d q).facetChain = presentedChain (p := p) :=
  rfl

theorem orbitChainAt_outputFamily_homologous (q : GoodParameter d) :
    presentedChain (p := p) -
        MeasureChain.orbitChainAt (outputCoefficient d) (outputFamily d) q =
      OrbitChain.boundary ℝ 5 (secondConeSystem d q).homotopyChain := by
  rw [orbitChainAt_outputFamily (d := d) q,
    ← secondConeSystem_facetChain (d := d) q]
  exact (secondConeSystem d q).facetChain_sub_secondChain

/-! ## Reciprocal weighting for a measurable primitive -/

/-- Every pullback of the primitive that occurs after alternation and after
taking a face. -/
abbrev PrimitiveIndex (A : Type*) :=
  OutputIndex A × (Equiv.Perm (Fin 5) × Fin 5)

def primitiveInput (k : PrimitiveIndex A) (q : GoodParameter d) :
    Pfaffian.U4 :=
  Pfaffian.face4At k.2.2
    (Pfaffian.permute5 k.2.1
      (Pfaffian.orbitCoord5 (outputFamily d k.1 q)))

def primitivePullback (f : Pfaffian.U4 → ℝ)
    (k : PrimitiveIndex A) (q : GoodParameter d) : ℝ :=
  f (primitiveInput d k q)

theorem primitiveInput_quasiMeasurePreserving (k : PrimitiveIndex A) :
    Measure.QuasiMeasurePreserving (primitiveInput d k)
      (goodParameterMeasure d) Pfaffian.measureU4 := by
  have hout := permutedOutputCoord_quasiMeasurePreserving d
    k.1.1 k.1.2 k.2.1
  have hface := Pfaffian.concreteFace4QuasiMeasurePreserving.at k.2.2
  have hcomp := hface.comp hout
  have heq : primitiveInput d k =
      (fun q : GoodParameter d ↦ Pfaffian.face4At k.2.2
        (Pfaffian.permute5 k.2.1
          (Pfaffian.orbitCoord5 (outputConfig d q k.1.1 k.1.2)))) := by
    funext q
    rfl
  rw [heq]
  exact hcomp

theorem primitivePullback_measurable (f : Pfaffian.U4 → ℝ)
    (hf : Measurable f) (k : PrimitiveIndex A) :
    Measurable (primitivePullback d f k) :=
  hf.comp (primitiveInput_quasiMeasurePreserving d k).measurable

noncomputable instance goodParameter_nonempty : Nonempty (GoodParameter d) :=
  (goodParameterSet_nonempty d).to_subtype

/-- The reciprocal-weight probability used to diffuse a given measurable
primitive. -/
def diffusionProbability (f : Pfaffian.U4 → ℝ) :
    ProbabilityMeasure (GoodParameter d) :=
  reciprocalProbability (goodParameterMeasure d) (primitivePullback d f)

def diffusionMeasure (f : Pfaffian.U4 → ℝ) :
    Measure (GoodParameter d) :=
  diffusionProbability d f

instance diffusionMeasure_isProbability (f : Pfaffian.U4 → ℝ) :
    IsProbabilityMeasure (diffusionMeasure d f) :=
  (diffusionProbability d f).2

theorem diffusionMeasure_absolutelyContinuous (f : Pfaffian.U4 → ℝ)
    (hf : Measurable f) :
    diffusionMeasure d f ≪ goodParameterMeasure d := by
  exact reciprocalProbability_absolutelyContinuous
    (goodParameterMeasure d) (primitivePullback d f)
      (primitivePullback_measurable d f hf)

theorem primitivePullback_integrable_diffusion
    (f : Pfaffian.U4 → ℝ) (hf : Measurable f) (k : PrimitiveIndex A) :
    Integrable (primitivePullback d f k) (diffusionMeasure d f) := by
  exact integrable_reciprocalProbability
    (goodParameterMeasure d) (primitivePullback d f)
      (primitivePullback_measurable d f hf) k

theorem permutedOutputCoord_quasiMeasurePreserving_diffusion
    (f : Pfaffian.U4 → ℝ) (hf : Measurable f)
    (a : A) (j : Fin 4) (sigma : Equiv.Perm (Fin 5)) :
    Measure.QuasiMeasurePreserving
      (fun q : GoodParameter d ↦
        Pfaffian.permute5 sigma
          (Pfaffian.orbitCoord5 (outputConfig d q a j)))
      (diffusionMeasure d f) Pfaffian.measureU5 :=
  (permutedOutputCoord_quasiMeasurePreserving d a j sigma).mono_left
    (diffusionMeasure_absolutelyContinuous d f hf)

/-- In particular, every unpermuted elementary output remains nonsingular
for the reciprocal-weight diffusion measure. -/
theorem outputCoord_quasiMeasurePreserving_diffusion
    (f : Pfaffian.U4 → ℝ) (hf : Measurable f) (k : OutputIndex A) :
    Measure.QuasiMeasurePreserving
      (fun q : GoodParameter d ↦
        Pfaffian.orbitCoord5 (outputFamily d k q))
      (diffusionMeasure d f) Pfaffian.measureU5 := by
  simpa [outputFamily, Pfaffian.permute5_one] using
    permutedOutputCoord_quasiMeasurePreserving_diffusion d f hf
      k.1 k.2 (1 : Equiv.Perm (Fin 5))

/-- The coboundary of the measurable primitive is integrable along every
elementary output of the diffused chain.  This is the precise analytic role
of including every output permutation and every face in the reciprocal
weight. -/
theorem D_comp_output_integrable
    (f : Pfaffian.U4 → ℝ) (hf : StronglyMeasurable f)
    (k : OutputIndex A) :
    Integrable
      (Pfaffian.D f ∘ fun q : GoodParameter d ↦
        Pfaffian.orbitCoord5 (outputFamily d k q))
      (diffusionMeasure d f) := by
  have heq :
      (Pfaffian.D f ∘ fun q : GoodParameter d ↦
          Pfaffian.orbitCoord5 (outputFamily d k q)) =
        fun q ↦ ∑ i : Fin 5, Pfaffian.faceSign i *
          f (Pfaffian.face4At i
            (Pfaffian.orbitCoord5 (outputFamily d k q))) := by
    funext q
    exact Pfaffian.D_eq_face_sum f _
  rw [heq]
  apply integrable_finsetSum Finset.univ
  intro i _hi
  have hface : Integrable
      (fun q : GoodParameter d ↦
        f (Pfaffian.face4At i
          (Pfaffian.orbitCoord5 (outputFamily d k q))))
      (diffusionMeasure d f) := by
    have hp := primitivePullback_integrable_diffusion d f hf.measurable
      (k, (1 : Equiv.Perm (Fin 5)), i)
    apply hp.congr
    filter_upwards [] with q
    simp [primitivePullback, primitiveInput, Pfaffian.permute5_one]
  exact hface.const_mul (Pfaffian.faceSign i)

/-- A representative which is essentially bounded modulo `D f` is integrable
on every elementary output of the reciprocal-weight diffusion. -/
theorem output_integrable_of_ae_eq_bounded_add_D
    (f : Pfaffian.U4 → ℝ) (hf : StronglyMeasurable f)
    (C F : Pfaffian.U5 → ℝ) (hF : StronglyMeasurable F)
    (K : ℝ) (hK : 0 ≤ K)
    (hFbound : ∀ᵐ u ∂Pfaffian.measureU5, |F u| ≤ K)
    (hrel : C =ᵐ[Pfaffian.measureU5]
      fun u ↦ F u + Pfaffian.D f u)
    (k : OutputIndex A) :
    Integrable
      (C ∘ fun q : GoodParameter d ↦
        Pfaffian.orbitCoord5 (outputFamily d k q))
      (diffusionMeasure d f) := by
  let φ : GoodParameter d → Pfaffian.U5 := fun q ↦
    Pfaffian.orbitCoord5 (outputFamily d k q)
  have hφ := outputCoord_quasiMeasurePreserving_diffusion d f hf.measurable k
  have hFint : Integrable (F ∘ φ) (diffusionMeasure d f) := by
    apply (integrable_const K).mono
    · exact (hF.comp_measurable hφ.measurable).aestronglyMeasurable
    · have hb := hφ.ae hFbound
      filter_upwards [hb] with q hq
      simpa [Real.norm_eq_abs, abs_of_nonneg hK] using hq
  have hDint : Integrable (Pfaffian.D f ∘ φ)
      (diffusionMeasure d f) := by
    exact D_comp_output_integrable d f hf k
  have hsum := hFint.add hDint
  have hpull := hφ.ae_eq hrel
  apply hsum.congr
  filter_upwards [hpull] with q hq
  exact hq.symm

/-! ## The absolutely continuous diffused measure cycle -/

theorem outputFamily_orbitCoord_measurable (k : OutputIndex A) :
    Measurable
      (fun q : GoodParameter d ↦
        Pfaffian.orbitCoord5 (outputFamily d k q)) := by
  have h := (outputCoord_quasiMeasurePreserving d k.1 k.2).measurable
  have heq : (fun q : GoodParameter d ↦
        Pfaffian.orbitCoord5 (outputFamily d k q)) =
      outputCoord d k.1 k.2 := by
    funext q
    exact (outputCoord_eq_orbitCoord d q k.1 k.2).symm
  rw [heq]
  exact h

def diffusedCycle (f : Pfaffian.U4 → ℝ) : SignedMeasure Pfaffian.U5 :=
  MeasureChain.diffusedOrbitChain (diffusionMeasure d f)
    (outputCoefficient d) (outputFamily d)

theorem diffusedCycle_boundary (f : Pfaffian.U4 → ℝ) :
    MeasureChain.boundary4 (diffusedCycle d f) = 0 := by
  apply MeasureChain.boundary_diffusedOrbitChain_eq_zero
    (diffusionMeasure d f) (outputCoefficient d) (outputFamily d)
    (outputFamily_orbitCoord_measurable d)
  exact orbitChainAt_outputFamily_boundary d

theorem diffusedCycle_isAbsolutelyContinuous
    (f : Pfaffian.U4 → ℝ) (hf : Measurable f) :
    MeasureChain.IsAbsolutelyContinuous (diffusedCycle d f)
      Pfaffian.measureU5 := by
  apply MeasureChain.diffusedOrbitChain_isAbsolutelyContinuous
    (diffusionMeasure d f) (outputCoefficient d) (outputFamily d)
  intro k sigma
  simpa [outputFamily] using
    permutedOutputCoord_quasiMeasurePreserving_diffusion d f hf
      k.1 k.2 sigma

theorem diffusedCycle_primitiveFace_integrable
    (f : Pfaffian.U4 → ℝ) (hf : StronglyMeasurable f) (i : Fin 5) :
    (diffusedCycle d f).Integrable (f ∘ Pfaffian.face4At i) := by
  apply MeasureChain.integrable_face_diffusedOrbitChain
    (diffusionMeasure d f) (outputCoefficient d) (outputFamily d)
    (outputFamily_orbitCoord_measurable d) f hf
  intro k sigma r
  change Integrable (primitivePullback d f (k, sigma, r))
    (diffusionMeasure d f)
  exact primitivePullback_integrable_diffusion d f hf.measurable
    (k, sigma, r)

/-- The displayed elementary coefficient mass is exactly `5 × 4` times
the mass of the fixed parent presentation. -/
theorem sum_abs_outputCoefficient (q : GoodParameter d) :
    (∑ k : OutputIndex A, |outputCoefficient d k|) =
      20 * ∑ s : I, |p.coeff s| := by
  classical
  let D := firstConeSystem d q
  have hatom : (∑ a : A, |D.atomCoeff a|) =
      5 * ∑ s : I, |D.facetCoeff s| := by
    calc
      (∑ a : A, |D.atomCoeff a|) =
          ∑ s : I, ∑ a ∈ D.atomsOf s, |D.atomCoeff a| := by
            rw [D.sum_over_parents]
      _ = ∑ s : I, 5 * |D.facetCoeff s| := by
            apply Finset.sum_congr rfl
            intro s _hs
            exact MeasureChain.SecondConeSystem.atomMass_eq_five D s
      _ = 5 * ∑ s : I, |D.facetCoeff s| := by
            rw [Finset.mul_sum]
  calc
    (∑ k : OutputIndex A, |outputCoefficient d k|) =
        ∑ a : A, ∑ j : Fin 4,
          |d.atomCoeff a * (-1 : ℝ) ^ j.val| := by
            simp only [Fintype.sum_prod_type, outputCoefficient]
    _ = ∑ a : A, 4 * |d.atomCoeff a| := by
          apply Finset.sum_congr rfl
          intro a _ha
          simp [abs_mul]
    _ = 4 * ∑ a : A, |d.atomCoeff a| := by
          rw [Finset.mul_sum]
    _ = 4 * (5 * ∑ s : I, |p.coeff s|) := by
          change (∑ a : A, |d.atomCoeff a|) =
            5 * ∑ s : I, |p.coeff s| at hatom
          rw [hatom]
    _ = 20 * ∑ s : I, |p.coeff s| := by ring

theorem diffusedCycle_mass_le (f : Pfaffian.U4 → ℝ)
    (q : GoodParameter d) :
    MeasureChain.mass (diffusedCycle d f) ≤
      20 * ∑ s : I, |p.coeff s| := by
  refine (MeasureChain.mass_diffusedOrbitChain_le
    (diffusionMeasure d f) (outputCoefficient d) (outputFamily d)
    (outputFamily_orbitCoord_measurable d)).trans_eq ?_
  exact sum_abs_outputCoefficient d q

/-- Averaging the pointwise two-cone homotopy preserves the period of any
pointwise alternating five-cocycle. -/
theorem integral_diffusedCycle_eq_presented
    (f : Pfaffian.U4 → ℝ)
    (C : Pfaffian.U5 → ℝ) (hCmeas : StronglyMeasurable C)
    (hCalt : MeasureChain.IsAlternatingFunction5 C)
    (hCcoc : MeasureChain.IsPointwiseCocycle5 C)
    (hint : ∀ k : OutputIndex A,
      Integrable
        (C ∘ fun q : GoodParameter d ↦
          Pfaffian.orbitCoord5 (outputFamily d k q))
        (diffusionMeasure d f)) :
    (∫ᵛ u, C u ∂<•(diffusedCycle d f)) =
      MeasureChain.evaluation5 C hCalt (presentedChain (p := p)) := by
  have havg := MeasureChain.integral_diffusedOrbitChain_eq
    (diffusionMeasure d f) (outputCoefficient d) (outputFamily d)
    (outputFamily_orbitCoord_measurable d) C hCmeas hCalt hint
  rw [show (∫ᵛ u, C u ∂<•(diffusedCycle d f)) =
      ∫ q, MeasureChain.evaluation5 C hCalt
        (MeasureChain.orbitChainAt (outputCoefficient d) (outputFamily d) q)
        ∂(diffusionMeasure d f) from havg]
  have hpoint : ∀ q : GoodParameter d,
      MeasureChain.evaluation5 C hCalt
          (MeasureChain.orbitChainAt (outputCoefficient d) (outputFamily d) q) =
        MeasureChain.evaluation5 C hCalt (presentedChain (p := p)) := by
    intro q
    rw [orbitChainAt_outputFamily (d := d) q]
    rw [(secondConeSystem d q).evaluation5_secondChain_eq_facetChain
      C hCalt hCcoc]
    rw [secondConeSystem_facetChain (d := d) q]
  simp_rw [hpoint]
  simp

/-! ## The quantitative two-cone diffusion estimate -/

/-- The article's diffusion estimate for a fixed finite presentation.

If the alternating pointwise cocycle `C` differs almost everywhere from an
essentially `K`-bounded function by the coboundary `D f`, then its period on
the presented cycle is bounded by `20 K` times the presentation mass.  The
proof below records all three measure-theoretic ingredients explicitly:
reciprocal-weight integrability, Stokes on the diffused cycle, and absolute
continuity for transporting the a.e. cochain identity. -/
theorem abs_evaluation5_presented_le_twenty_mul
    (d : OrbitChain.WeightedFacePairing p A)
    (f : Pfaffian.U4 → ℝ) (hf : StronglyMeasurable f)
    (C : Pfaffian.U5 → ℝ) (hCmeas : StronglyMeasurable C)
    (hCalt : MeasureChain.IsAlternatingFunction5 C)
    (hCcoc : MeasureChain.IsPointwiseCocycle5 C)
    (F : Pfaffian.U5 → ℝ) (hFmeas : StronglyMeasurable F)
    (K : ℝ) (hK : 0 ≤ K)
    (hFbound : ∀ᵐ u ∂Pfaffian.measureU5, |F u| ≤ K)
    (hrel : C =ᵐ[Pfaffian.measureU5]
      fun u ↦ F u + Pfaffian.D f u) :
    |MeasureChain.evaluation5 C hCalt (presentedChain (p := p))| ≤
      20 * (∑ s : I, |p.coeff s|) * K := by
  let ν : SignedMeasure Pfaffian.U5 := diffusedCycle d f
  have hint : ∀ k : OutputIndex A,
      Integrable
        (C ∘ fun q : GoodParameter d ↦
          Pfaffian.orbitCoord5 (outputFamily d k q))
        (diffusionMeasure d f) := by
    intro k
    exact output_integrable_of_ae_eq_bounded_add_D d f hf C F hFmeas
      K hK hFbound hrel k
  have hperiod :
      (∫ᵛ u, C u ∂<•ν) =
        MeasureChain.evaluation5 C hCalt (presentedChain (p := p)) := by
    exact integral_diffusedCycle_eq_presented d f C hCmeas hCalt hCcoc hint
  have hface : ∀ i : Fin 5, ν.Integrable (f ∘ Pfaffian.face4At i) := by
    intro i
    exact diffusedCycle_primitiveFace_integrable d f hf i
  obtain ⟨hDint, _hboundaryInt, hstokes⟩ :=
    MeasureChain.stokes_boundary4 ν f hf hface
  have hDzero : (∫ᵛ u, Pfaffian.D f u ∂<•ν) = 0 := by
    rw [hstokes, show MeasureChain.boundary4 ν = 0 from
      diffusedCycle_boundary d f]
    exact VectorMeasure.integral_zero_vectorMeasure
  have hνac : MeasureChain.IsAbsolutelyContinuous ν Pfaffian.measureU5 :=
    diffusedCycle_isAbsolutelyContinuous d f hf.measurable
  have hFboundν : ∀ᵐ u ∂ν.variation, |F u| ≤ K :=
    hνac.ae_le hFbound
  have hFint : ν.Integrable F := by
    change Integrable F ν.variation
    apply (integrable_const K).mono hFmeas.aestronglyMeasurable
    filter_upwards [hFboundν] with u hu
    simpa [Real.norm_eq_abs, abs_of_nonneg hK] using hu
  have hrelIntegral :
      (∫ᵛ u, C u ∂<•ν) =
        ∫ᵛ u, F u + Pfaffian.D f u ∂<•ν :=
    MeasureChain.integral_congr_ae_of_isAbsolutelyContinuous hνac hrel
  have hsumIntegral :
      (∫ᵛ u, F u + Pfaffian.D f u ∂<•ν) =
        (∫ᵛ u, F u ∂<•ν) +
          ∫ᵛ u, Pfaffian.D f u ∂<•ν :=
    VectorMeasure.integral_fun_add hFint hDint
  have hmass : MeasureChain.mass ν ≤
      20 * ∑ s : I, |p.coeff s| := by
    let q : GoodParameter d := Classical.choice
      (goodParameter_nonempty (d := d))
    exact diffusedCycle_mass_le d f q
  calc
    |MeasureChain.evaluation5 C hCalt (presentedChain (p := p))| =
        |∫ᵛ u, C u ∂<•ν| := congrArg abs hperiod.symm
    _ = |∫ᵛ u, F u + Pfaffian.D f u ∂<•ν| :=
      congrArg abs hrelIntegral
    _ = |(∫ᵛ u, F u ∂<•ν) +
          ∫ᵛ u, Pfaffian.D f u ∂<•ν| :=
      congrArg abs hsumIntegral
    _ = |∫ᵛ u, F u ∂<•ν| := by rw [hDzero, add_zero]
    _ ≤ K * MeasureChain.mass ν :=
      MeasureChain.abs_integral_flip_le_mass ν F hFboundν
    _ ≤ K * (20 * ∑ s : I, |p.coeff s|) :=
      mul_le_mul_of_nonneg_left hmass hK
    _ = 20 * (∑ s : I, |p.coeff s|) * K := by ring

/-- Near-minimal-presentation form of the diffusion estimate. -/
theorem abs_evaluation5_cycle_le_twenty_mul_add
    (Z : OrbitChain.Module ℝ 5)
    (hZ : OrbitChain.boundary ℝ 4 Z = 0)
    (f : Pfaffian.U4 → ℝ) (hf : StronglyMeasurable f)
    (C : Pfaffian.U5 → ℝ) (hCmeas : StronglyMeasurable C)
    (hCalt : MeasureChain.IsAlternatingFunction5 C)
    (hCcoc : MeasureChain.IsPointwiseCocycle5 C)
    (F : Pfaffian.U5 → ℝ) (hFmeas : StronglyMeasurable F)
    (K : ℝ) (hK : 0 ≤ K)
    (hFbound : ∀ᵐ u ∂Pfaffian.measureU5, |F u| ≤ K)
    (hrel : C =ᵐ[Pfaffian.measureU5]
      fun u ↦ F u + Pfaffian.D f u)
    (ε : ℝ) (hε : 0 < ε) :
    |MeasureChain.evaluation5 C hCalt Z| ≤
      20 * (OrbitChain.quotientL1 Z + ε) * K := by
  classical
  obtain ⟨c, hc, hcmass⟩ :=
    OrbitChain.exists_presentation_lt_quotientL1_add Z hε
  have hcycle : OrbitChain.boundary ℝ 4
      ((OrbitChain.relations ℝ 5).mkQ c) = 0 := by
    rw [hc]
    exact hZ
  let p₀ := OrbitChain.supportPresentation c hcycle
  let d₀ := p₀.weightedFacePairing
  have hfixed := abs_evaluation5_presented_le_twenty_mul
    (p := p₀) d₀ f hf C hCmeas hCalt hCcoc F hFmeas
      K hK hFbound hrel
  have hpresented : presentedChain (p := p₀) = Z := by
    change (∑ s : OrbitChain.SupportIndex c,
      c s.1 • OrbitChain.ofConfig (R := ℝ) s.1) = Z
    calc
      (∑ s : OrbitChain.SupportIndex c,
          c s.1 • OrbitChain.ofConfig (R := ℝ) s.1) =
          (OrbitChain.relations ℝ 5).mkQ c := by
        have hraw := congrArg (OrbitChain.relations ℝ 5).mkQ
          (OrbitChain.raw_eq_sum_support c)
        simpa [OrbitChain.ofConfig] using hraw
      _ = Z := hc
  have hpresentationMass :
      (∑ s : OrbitChain.SupportIndex c, |p₀.coeff s|) =
        OrbitChain.rawMass c := by
    exact OrbitChain.supportPresentation_displayedMass c hcycle
  rw [hpresented, hpresentationMass] at hfixed
  exact hfixed.trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcmass.le (by norm_num)) hK)

/-- Intrinsic quotient-seminorm form of the article's two-cone diffusion
estimate.  The auxiliary `ε` used to select a finite raw presentation has
now disappeared. -/
theorem abs_evaluation5_cycle_le_twenty_mul_quotientL1
    (Z : OrbitChain.Module ℝ 5)
    (hZ : OrbitChain.boundary ℝ 4 Z = 0)
    (f : Pfaffian.U4 → ℝ) (hf : StronglyMeasurable f)
    (C : Pfaffian.U5 → ℝ) (hCmeas : StronglyMeasurable C)
    (hCalt : MeasureChain.IsAlternatingFunction5 C)
    (hCcoc : MeasureChain.IsPointwiseCocycle5 C)
    (F : Pfaffian.U5 → ℝ) (hFmeas : StronglyMeasurable F)
    (K : ℝ) (hK : 0 ≤ K)
    (hFbound : ∀ᵐ u ∂Pfaffian.measureU5, |F u| ≤ K)
    (hrel : C =ᵐ[Pfaffian.measureU5]
      fun u ↦ F u + Pfaffian.D f u) :
    |MeasureChain.evaluation5 C hCalt Z| ≤
      20 * OrbitChain.quotientL1 Z * K := by
  by_cases hKzero : K = 0
  · have h := abs_evaluation5_cycle_le_twenty_mul_add Z hZ f hf C
      hCmeas hCalt hCcoc F hFmeas K hK hFbound hrel 1 (by norm_num)
    simpa [hKzero] using h
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hKzero)
    apply le_of_forall_pos_le_add
    intro δ hδ
    let ε := δ / (20 * K)
    have hε : 0 < ε := div_pos hδ (mul_pos (by norm_num) hKpos)
    have h := abs_evaluation5_cycle_le_twenty_mul_add Z hZ f hf C
      hCmeas hCalt hCcoc F hFmeas K hK hFbound hrel ε hε
    calc
      |MeasureChain.evaluation5 C hCalt Z| ≤
          20 * (OrbitChain.quotientL1 Z + ε) * K := h
      _ = 20 * OrbitChain.quotientL1 Z * K + δ := by
        dsimp [ε]
        field_simp
        <;> ring

end
end TwoConeParameterization
end Sp4
