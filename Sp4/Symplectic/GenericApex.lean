import Sp4.Chains.Orbit
import Mathlib.Algebra.Module.Submodule.Union

/-!
# Simultaneously generic projective apices

The two-cone argument repeatedly chooses one new projective line which is
generic for finitely many existing configurations.  This file proves that
choice directly.  The bad locus is a finite union of proper linear
subspaces: symplectic orthogonal hyperplanes to existing points and spans of
existing triples.  Over the infinite field `ℂ`, that union is proper.
-/

namespace Sp4

open scoped BigOperators
open OrbitChain

noncomputable section

/-- The span of three selected projective lines, expressed using their
canonical representatives. -/
def projectiveTripleSpan {n : ℕ} (x : ProjectiveConfig n)
    (e : Fin 3 → Fin n) : Submodule ℂ SymplecticVector :=
  ⨆ k, (x (e k)).submodule

/-- Bad subspaces used to select a common apex for a finite family of
`n`-point configurations.  `none` records the zero subspace, which ensures
that the selected vector itself is nonzero. -/
abbrev ApexBadIndex (I : Type*) (n : ℕ) :=
  Option (Sum (I × Fin n) (I × (Fin 3 → Fin n)))

/-- The kernel of pairing against a nonzero projective representative is a
proper subspace, by nondegeneracy of the symplectic form. -/
theorem symplecticKernel_ne_top (l : ProjectivePoint) :
    LinearMap.ker (omega.flip l.rep) ≠ ⊤ := by
  intro htop
  apply l.rep_nonzero
  apply omega_nondegenerate.right l.rep
  intro v
  have hv : v ∈ LinearMap.ker (omega.flip l.rep) := by
    rw [htop]
    trivial
  simpa using (LinearMap.mem_ker.mp hv)

/-- Three vectors cannot span the fixed four-dimensional symplectic space.
No independence assumption is needed here. -/
theorem projectiveTripleSpan_ne_top {n : ℕ} (x : ProjectiveConfig n)
    (e : Fin 3 → Fin n) : projectiveTripleSpan x e ≠ ⊤ := by
  intro htop
  have hspan : Submodule.span ℂ
      (Set.range (fun k : Fin 3 ↦ (x (e k)).rep)) = ⊤ := by
    rw [Submodule.span_range_eq_iSup]
    simpa [projectiveTripleSpan, Projectivization.submodule_eq] using htop
  have hrank := finrank_le_of_span_eq_top hspan
  rw [finrank_symplecticVector, Fintype.card_fin] at hrank
  omega

/-- The bad subspace attached to one finite constraint. -/
def apexBadSubmodule {I : Type*} {n : ℕ}
    (x : I → ProjectiveConfig n) :
    ApexBadIndex I n → Submodule ℂ SymplecticVector
  | none => ⊥
  | some (Sum.inl (i, j)) => LinearMap.ker (omega.flip (x i j).rep)
  | some (Sum.inr (i, e)) => projectiveTripleSpan (x i) e

theorem apexBadSubmodule_ne_top {I : Type*} {n : ℕ}
    (x : I → ProjectiveConfig n) (b : ApexBadIndex I n) :
    apexBadSubmodule x b ≠ ⊤ := by
  rcases b with _ | (_ | _)
  · exact bot_ne_top
  · exact symplecticKernel_ne_top _
  · exact projectiveTripleSpan_ne_top _ _

/-- A finite family of bad subspaces has a common avoiding vector. -/
theorem exists_vector_avoiding_apexBad {I : Type*} [Finite I] {n : ℕ}
    (x : I → ProjectiveConfig n) :
    ∃ v : SymplecticVector, ∀ b : ApexBadIndex I n,
      v ∉ apexBadSubmodule x b := by
  exact Submodule.exists_forall_notMem_of_forall_ne_top
    (apexBadSubmodule x) (apexBadSubmodule_ne_top x)

/-- A projective point is a common apex when it is transverse to every
listed point and completes every three-dimensional listed triple span to the
whole symplectic space. -/
structure IsCommonApex {I : Type*} {n : ℕ}
    (x : I → ProjectiveConfig n) (y : ProjectivePoint) : Prop where
  transverse : ∀ i j, Transverse y (x i j)
  triple_completion : ∀ i e,
    Module.finrank ℂ (projectiveTripleSpan (x i) e) = 3 →
      projectiveTripleSpan (x i) e ⊔ y.submodule = ⊤

/-- The finite-union argument produces a common projective apex. -/
theorem exists_commonApex {I : Type*} [Finite I] {n : ℕ}
    (x : I → ProjectiveConfig n) :
    ∃ y : ProjectivePoint, IsCommonApex x y := by
  obtain ⟨v, hv⟩ := exists_vector_avoiding_apexBad x
  have hv0 : v ≠ 0 := by
    simpa [apexBadSubmodule] using hv none
  refine ⟨Projectivization.mk ℂ v hv0, ?_⟩
  constructor
  · intro i j
    have h := hv (some (Sum.inl (i, j)))
    have hpair : omega v (x i j).rep ≠ 0 := by
      simpa [apexBadSubmodule, LinearMap.mem_ker] using h
    have ht := (transverse_mk_iff v (x i j).rep hv0
      (x i j).rep_nonzero).2 hpair
    simpa only [Projectivization.mk_rep] using ht
  · intro i e hdim
    rw [Projectivization.submodule_mk]
    have hvspan : v ∉ projectiveTripleSpan (x i) e := by
      simpa [apexBadSubmodule] using hv (some (Sum.inr (i, e)))
    apply Submodule.eq_top_of_finrank_eq
    rw [Submodule.finrank_sup_span_singleton hvspan, hdim,
      finrank_symplecticVector]

/-! ## Independence of triples in a generic configuration -/

/-- Extend three prescribed distinct indices by one further index. -/
theorem exists_fin4_extension {n : ℕ} (h4 : 4 ≤ n)
    (e : Fin 3 → Fin n) (he : Function.Injective e) :
    ∃ e4 : Fin 4 → Fin n, Function.Injective e4 ∧
      ∀ k : Fin 3, e4 k.succ = e k := by
  classical
  let s : Finset (Fin n) := Finset.univ.image e
  have hscard : s.card = 3 := by
    simp [s, Finset.card_image_of_injective _ he]
  have hlt : s.card < (Finset.univ : Finset (Fin n)).card := by
    simp only [hscard, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨q, _hqmem, hq⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  let e4 : Fin 4 → Fin n := Fin.cases q e
  refine ⟨e4, ?_, ?_⟩
  · intro a b hab
    refine Fin.cases (motive := fun a : Fin 4 ↦
      ∀ b : Fin 4, e4 a = e4 b → a = b) ?_ ?_ a b hab
    · intro b hb
      refine Fin.cases (motive := fun b : Fin 4 ↦
        e4 0 = e4 b → 0 = b) ?_ ?_ b hb
      · intro _
        rfl
      · intro j hj
        exfalso
        apply hq
        have hqej : q = e j := by
          simpa [e4] using hj
        exact Finset.mem_image.mpr
          ⟨j, Finset.mem_univ _, hqej.symm⟩
    · intro i b hb
      refine Fin.cases (motive := fun b : Fin 4 ↦
        e4 i.succ = e4 b → i.succ = b) ?_ ?_ b hb
      · intro hi
        exfalso
        apply hq
        have heiq : e i = q := by
          simpa [e4] using hi
        exact Finset.mem_image.mpr
          ⟨i, Finset.mem_univ _, heiq⟩
      · intro j hij
        exact congrArg Fin.succ (he (by simpa [e4] using hij))
  · intro k
    simp [e4]

/-- Every three distinct canonical representatives are linearly
independent. -/
def TriplesIndependent {n : ℕ} (x : ProjectiveConfig n) : Prop :=
  ∀ (e : Fin 3 → Fin n), Function.Injective e →
    Module.finrank ℂ (projectiveTripleSpan x e) = 3

/-- For configurations with at least four entries, the article's genericity
condition implies independence of every triple. -/
theorem IsGeneric.triplesIndependent_of_four_le {n : ℕ}
    {x : ProjectiveConfig n} (hx : IsGeneric x) (h4 : 4 ≤ n) :
    TriplesIndependent x := by
  intro e he
  obtain ⟨e4, he4, he4ext⟩ := exists_fin4_extension h4 e he
  have hfour := hx.four_spans e4 he4
  have hspan4 : Submodule.span ℂ
      (Set.range (fun k : Fin 4 ↦ (x (e4 k)).rep)) = ⊤ := by
    rw [Submodule.span_range_eq_iSup]
    simpa [Projectivization.submodule_eq] using hfour
  have hli4 : LinearIndependent ℂ
      (fun k : Fin 4 ↦ (x (e4 k)).rep) :=
    linearIndependent_of_top_le_span_of_card_le_finrank
      hspan4.ge (by norm_num)
  have hli3 : LinearIndependent ℂ (fun k : Fin 3 ↦ (x (e k)).rep) := by
    have h := hli4.comp Fin.succ (Fin.succ_injective 3)
    simpa [Function.comp_def, he4ext] using h
  have heq : projectiveTripleSpan x e = Submodule.span ℂ
      (Set.range (fun k : Fin 3 ↦ (x (e k)).rep)) := by
    simp [projectiveTripleSpan, Projectivization.submodule_eq,
      Submodule.span_range_eq_iSup]
  rw [heq, finrank_span_eq_card hli3, Fintype.card_fin]

/-- Deleting one entry preserves independence of triples. -/
theorem TriplesIndependent.delete {n : ℕ} {x : ProjectiveConfig (n + 1)}
    (hx : TriplesIndependent x) (i : Fin (n + 1)) :
    TriplesIndependent (FinTuple.delete i x) := by
  intro e he
  change Module.finrank ℂ
    (projectiveTripleSpan x (fun k ↦ i.succAbove (e k))) = 3
  exact hx _ (Fin.succAbove_right_injective.comp he)

/-! ## Turning a common apex into generic cones -/

/-- A common apex for a family is in particular a common apex for each
single member. -/
theorem IsCommonApex.single {I : Type*} {n : ℕ}
    {x : I → ProjectiveConfig n} {y : ProjectivePoint}
    (hy : IsCommonApex x y) (i : I) :
    IsCommonApex (fun _ : Unit ↦ x i) y where
  transverse _ j := hy.transverse i j
  triple_completion _ e := hy.triple_completion i e

/-- Transversality plus completion of every independent triple is exactly
what is needed to prepend an apex to a generic configuration. -/
theorem IsCommonApex.cons_generic {n : ℕ} {x : ProjectiveConfig n}
    {y : ProjectivePoint} (hy : IsCommonApex (fun _ : Unit ↦ x) y)
    (hx : IsGeneric x) (htri : TriplesIndependent x) :
    IsGeneric (Fin.cons y x) := by
  constructor
  · intro a b hab
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩
    · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨j, rfl⟩
      · exact False.elim (hab rfl)
      · simpa using hy.transverse () j
    · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨j, rfl⟩
      · simpa using (hy.transverse () i).symm
      · apply hx.pairwise_transverse i j
        intro h
        exact hab (congrArg Fin.succ h)
  · intro e he
    by_cases hzero : ∃ k, e k = 0
    · obtain ⟨k0, hk0⟩ := hzero
      have hne (r : Fin 3) : e (k0.succAbove r) ≠ 0 := by
        intro h
        have heq := he (h.trans hk0.symm)
        exact Fin.succAbove_ne k0 r heq
      let e3 : Fin 3 → Fin n :=
        fun r ↦ (e (k0.succAbove r)).pred (hne r)
      have he3 : Function.Injective e3 := by
        intro r s hrs
        apply Fin.succAbove_right_injective
        apply he
        rw [← Fin.succ_pred (e (k0.succAbove r)) (hne r),
          ← Fin.succ_pred (e (k0.succAbove s)) (hne s)]
        exact congrArg Fin.succ hrs
      have hcomp := hy.triple_completion () e3 (htri e3 he3)
      apply top_unique
      rw [← hcomp]
      apply sup_le
      · apply iSup_le
        intro r
        have hle := le_iSup
          (fun k : Fin 4 ↦
            ((Fin.cons y x : ProjectiveConfig (n + 1)) (e k)).submodule)
          (k0.succAbove r)
        have hpoint :
            (Fin.cons y x : ProjectiveConfig (n + 1))
                (e (k0.succAbove r)) = x (e3 r) := by
          calc
            (Fin.cons y x : ProjectiveConfig (n + 1))
                (e (k0.succAbove r)) =
                (Fin.cons y x : ProjectiveConfig (n + 1))
                  ((e (k0.succAbove r)).pred (hne r)).succ := by
                    exact congrArg
                      (Fin.cons y x : ProjectiveConfig (n + 1))
                      (Fin.succ_pred (e (k0.succAbove r)) (hne r)).symm
            _ = x ((e (k0.succAbove r)).pred (hne r)) := by
              simp only [Fin.cons_succ]
            _ = x (e3 r) := by rfl
        rw [hpoint] at hle
        exact hle
      · have hle := le_iSup
          (fun k : Fin 4 ↦
            ((Fin.cons y x : ProjectiveConfig (n + 1)) (e k)).submodule) k0
        simpa [hk0] using hle
    · let e4 : Fin 4 → Fin n := fun k ↦
        (e k).pred (fun hk ↦ hzero ⟨k, hk⟩)
      have he4 : Function.Injective e4 := by
        intro r s hrs
        apply he
        rw [← Fin.succ_pred (e r) (fun hr ↦ hzero ⟨r, hr⟩),
          ← Fin.succ_pred (e s) (fun hs ↦ hzero ⟨s, hs⟩)]
        exact congrArg Fin.succ hrs
      have hbase := hx.four_spans e4 he4
      have hpoint (k : Fin 4) :
          (Fin.cons y x : ProjectiveConfig (n + 1)) (e k) = x (e4 k) := by
        calc
          (Fin.cons y x : ProjectiveConfig (n + 1)) (e k) =
              (Fin.cons y x : ProjectiveConfig (n + 1))
                ((e k).pred (fun hk ↦ hzero ⟨k, hk⟩)).succ := by
                  exact congrArg
                    (Fin.cons y x : ProjectiveConfig (n + 1))
                    (Fin.succ_pred (e k)
                      (fun hk ↦ hzero ⟨k, hk⟩)).symm
          _ = x ((e k).pred (fun hk ↦ hzero ⟨k, hk⟩)) := by
            simp only [Fin.cons_succ]
          _ = x (e4 k) := by rfl
      simp_rw [hpoint]
      exact hbase

/-- One apex can be chosen so that coning every member of a finite family of
generic configurations (of size at least four) remains generic. -/
theorem exists_common_generic_cons {I : Type*} [Finite I] {n : ℕ}
    (x : I → GenericConfig n) (h4 : 4 ≤ n) :
    ∃ y : ProjectivePoint, ∀ i,
      IsGeneric (Fin.cons y (x i).1) := by
  obtain ⟨y, hy⟩ := exists_commonApex (fun i ↦ (x i).1)
  refine ⟨y, fun i ↦ (hy.single i).cons_generic (x i).2 ?_⟩
  exact (x i).2.triplesIndependent_of_four_le h4

end

end Sp4
