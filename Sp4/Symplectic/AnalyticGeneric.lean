import Sp4.Symplectic.Gram
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Simultaneous analytic genericity

This file supplies the finite-intersection argument used by the two-cone
diffusion.  A finite family of vector-valued analytic configurations is
generic when finitely many symplectic pairings and principal Gram
determinants do not vanish.  A nontrivial analytic scalar condition has an
open dense nonvanishing locus, so finitely many individually realizable
configuration requirements can be imposed simultaneously.
-/

namespace Sp4

noncomputable section

open Set Filter
open scoped BigOperators

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [CompleteSpace P]

/-- Off-diagonal Gram entries that must not vanish. -/
abbrev OffDiagonalIndex (n : ℕ) :=
  {ij : Fin n × Fin n // ij.1 ≠ ij.2}

/-- Ordered selections of four columns whose principal Gram determinant
must not vanish. -/
abbrev PrincipalFourIndex (n : ℕ) :=
  {e : Fin 4 → Fin n // Function.Injective e}

/-- The finite list of scalar conditions defining genericity. -/
abbrev GenericConditionIndex (n : ℕ) :=
  OffDiagonalIndex n ⊕ PrincipalFourIndex n

/-- An analytic family of literal vector configurations.  The lower bound
on the number of vertices is precisely what is needed to formulate the
four-spanning condition. -/
structure AnalyticConfigFamily (P : Type*) [NormedAddCommGroup P]
    [NormedSpace ℂ P] (n : ℕ) where
  vec : P → Fin n → SymplecticVector
  analytic : ∀ i, AnalyticOnNhd ℂ (fun p ↦ vec p i) Set.univ
  four_le : 4 ≤ n

namespace AnalyticConfigFamily

variable {n : ℕ} (F : AnalyticConfigFamily P n)

/-- The scalar analytic function attached to one genericity condition. -/
def condition : GenericConditionIndex n → P → ℂ
  | Sum.inl ij => fun p ↦ omega (F.vec p ij.1.1) (F.vec p ij.1.2)
  | Sum.inr e => fun p ↦
      ((gram (F.vec p)).submatrix e.1 e.1).det

/-- All defining scalar conditions are nonzero. -/
def Good (p : P) : Prop :=
  ∀ k : GenericConditionIndex n, F.condition k p ≠ 0

def goodSet : Set P := {p | F.Good p}

private theorem analyticAt_gramEntry (i j : Fin n) (p : P) :
    AnalyticAt ℂ (fun x ↦ omega (F.vec x i) (F.vec x j)) p := by
  have hi := F.analytic i p (Set.mem_univ p)
  have hj := F.analytic j p (Set.mem_univ p)
  have hcoord (v : Fin n) (k : Fin 4) :
      AnalyticAt ℂ (fun x ↦ F.vec x v k) p :=
    analyticAt_pi_iff.mp (F.analytic v p (Set.mem_univ p)) k
  rw [show (fun x ↦ omega (F.vec x i) (F.vec x j)) =
      fun x ↦ F.vec x i 0 * F.vec x j 1 -
        F.vec x i 1 * F.vec x j 0 +
        F.vec x i 2 * F.vec x j 3 -
        F.vec x i 3 * F.vec x j 2 by
      funext x
      exact omega_apply _ _]
  exact ((((hcoord i 0).mul (hcoord j 1)).sub
    ((hcoord i 1).mul (hcoord j 0))).add
      ((hcoord i 2).mul (hcoord j 3))).sub
        ((hcoord i 3).mul (hcoord j 2))

theorem condition_analytic (k : GenericConditionIndex n) :
    AnalyticOnNhd ℂ (F.condition k) Set.univ := by
  intro p _hp
  rcases k with ij | e
  · exact F.analyticAt_gramEntry ij.1.1 ij.1.2 p
  · rw [show F.condition (Sum.inr e) = fun p ↦
        ∑ σ : Equiv.Perm (Fin 4), Equiv.Perm.sign σ •
          ∏ i : Fin 4, gram (F.vec p) (e.1 (σ i)) (e.1 i) by
        funext x
        exact Matrix.det_apply _]
    simpa using
      (Finset.univ.analyticAt_fun_sum (c := p) (f := fun σ p ↦
        Equiv.Perm.sign σ •
          ∏ i : Fin 4, gram (F.vec p) (e.1 (σ i)) (e.1 i)) (by
        intro σ _hσ
        apply AnalyticAt.const_smul
        simpa using
          (Finset.univ.analyticAt_fun_prod (c := p) (f := fun i p ↦
            gram (F.vec p) (e.1 (σ i)) (e.1 i)) (by
              intro i _hi
              exact F.analyticAt_gramEntry (e.1 (σ i)) (e.1 i) p))))

theorem condition_continuous (k : GenericConditionIndex n) :
    Continuous (F.condition k) :=
  (F.condition_analytic k).continuous

/-- Nonvanishing of one nontrivial entire analytic scalar function is open
and dense.  The density proof is the several-variable identity theorem, not
an unsupported intersection heuristic. -/
theorem isOpen_dense_condition_ne (k : GenericConditionIndex n)
    (hk : ∃ p, F.condition k p ≠ 0) :
    IsOpen {p | F.condition k p ≠ 0} ∧
      Dense {p | F.condition k p ≠ 0} := by
  have hopen : IsOpen {p | F.condition k p ≠ 0} := by
    change IsOpen ((F.condition k) ⁻¹' ({0} : Set ℂ)ᶜ)
    exact isOpen_compl_singleton.preimage (F.condition_continuous k)
  refine ⟨hopen, dense_iff_inter_open.mpr ?_⟩
  intro U hU hUne
  by_contra hinter
  have hzero : ∀ x ∈ U, F.condition k x = 0 := by
    intro x hx
    by_contra hx0
    exact hinter ⟨x, hx, hx0⟩
  obtain ⟨x, hx⟩ := hUne
  have hevent : F.condition k =ᶠ[nhds x] 0 := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hzero y hy
  have hall := (F.condition_analytic k).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ x) hevent
  obtain ⟨y, hy⟩ := hk
  exact hy (hall (Set.mem_univ y))

/-- A single generic realization makes every scalar condition nontrivial;
therefore the full good locus is an open dense set. -/
theorem goodSet_isOpen_dense (hex : ∃ p, F.Good p) :
    IsOpen F.goodSet ∧ Dense F.goodSet := by
  classical
  obtain ⟨p₀, hp₀⟩ := hex
  have hpiece (k : GenericConditionIndex n) :
      IsOpen {p | F.condition k p ≠ 0} ∧
        Dense {p | F.condition k p ≠ 0} :=
    F.isOpen_dense_condition_ne k ⟨p₀, hp₀ k⟩
  have heq : F.goodSet = ⋂ k : GenericConditionIndex n,
      {p | F.condition k p ≠ 0} := by
    ext p
    simp [goodSet, Good]
  rw [heq]
  exact ⟨isOpen_iInter_of_finite fun k ↦ (hpiece k).1,
    dense_iInter_of_isOpen (fun k ↦ (hpiece k).1)
      (fun k ↦ (hpiece k).2)⟩

theorem goodSet_nonempty (hex : ∃ p, F.Good p) : F.goodSet.Nonempty := by
  have hdense := (F.goodSet_isOpen_dense hex).2
  simpa using hdense.inter_open_nonempty Set.univ isOpen_univ Set.univ_nonempty

theorem vec_ne_zero {p : P} (hp : F.Good p) (i : Fin n) :
    F.vec p i ≠ 0 := by
  have hn : 2 ≤ n := le_trans (by norm_num) F.four_le
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j, hji⟩ := exists_ne i
  have hij : i ≠ j := hji.symm
  have hpair := hp (Sum.inl ⟨(i, j), hij⟩)
  intro hi
  apply hpair
  simp [condition, hi]

/-- Projectivize a good literal vector family. -/
def config (p : P) (hp : F.Good p) : ProjectiveConfig n := fun i ↦
  Projectivization.mk ℂ (F.vec p i) (F.vec_ne_zero hp i)

def lift (p : P) (hp : F.Good p) : ProjectiveLift (F.config p hp) where
  vec := F.vec p
  ne_zero := F.vec_ne_zero hp
  projectivizes _ := rfl

theorem gram_rank_eq_four {p : P} (hp : F.Good p) :
    (gram (F.vec p)).rank = 4 := by
  let e : Fin 4 → Fin n := Fin.castLE F.four_le
  have he : Function.Injective e := Fin.castLE_injective F.four_le
  have hdet := hp (Sum.inr ⟨e, he⟩)
  apply le_antisymm (gram_rank_le_four _)
  have hsub := Matrix.rank_submatrix_le (gram (F.vec p)) e e
  rw [Matrix.rank_of_det_ne_zero hdet] at hsub
  simpa using hsub

/-- The finite nonvanishing conditions really imply projective genericity. -/
theorem config_generic {p : P} (hp : F.Good p) :
    IsGeneric (F.config p hp) := by
  apply (F.lift p hp).isGeneric_of_gram_isAdmissible
  refine
    { skew := gram_isSkew _
      rank_four := F.gram_rank_eq_four hp
      offDiagonal_ne := ?_
      principal_four_ne := ?_ }
  · intro i j hij
    exact hp (Sum.inl ⟨(i, j), hij⟩)
  · intro e he
    exact hp (Sum.inr ⟨e, he⟩)

/-- Conversely, if the literal vectors are nonzero and their
projectivizations form a generic configuration, then every scalar condition
used in `Good` is nonzero.  This is the bridge used to prove that each
analytic condition family has at least one realization. -/
theorem good_of_projectivized_generic {p : P}
    (hv : ∀ i, F.vec p i ≠ 0)
    (hg : IsGeneric (fun i ↦ Projectivization.mk ℂ (F.vec p i) (hv i))) :
    F.Good p := by
  intro k
  rcases k with ij | e
  · rw [show F.condition (Sum.inl ij) p =
        omega (F.vec p ij.1.1) (F.vec p ij.1.2) by rfl]
    rw [← transverse_mk_iff]
    exact hg.pairwise_transverse ij.1.1 ij.1.2 ij.2
  · let l : ProjectiveConfig n :=
      fun i ↦ Projectivization.mk ℂ (F.vec p i) (hv i)
    let u : ProjectiveLift l :=
      { vec := F.vec p
        ne_zero := hv
        projectivizes := fun _ ↦ rfl }
    let b := u.selectedBasis hg e.1 e.2
    have hdet :=
      (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
        omega_nondegenerate
    have hmatrix :
        (gram (F.vec p)).submatrix e.1 e.1 =
          LinearMap.BilinForm.toMatrix b omega := by
      ext i j
      simp [gram, b, u]
    change ((gram (F.vec p)).submatrix e.1 e.1).det ≠ 0
    rw [hmatrix]
    exact hdet

end AnalyticConfigFamily

/-- A finite collection of analytic configuration families that can each be
made generic separately can be made generic simultaneously. -/
theorem exists_simultaneously_good
    {J : Type*} [Fintype J] {n : J → ℕ}
    (F : ∀ j, AnalyticConfigFamily P (n j))
    (hex : ∀ j, ∃ p, (F j).Good p) :
    ∃ p, ∀ j, (F j).Good p := by
  classical
  let S : J → Set P := fun j ↦ (F j).goodSet
  have hopen : ∀ j, IsOpen (S j) := fun j ↦
    ((F j).goodSet_isOpen_dense (hex j)).1
  have hdense : ∀ j, Dense (S j) := fun j ↦
    ((F j).goodSet_isOpen_dense (hex j)).2
  have hall : Dense (⋂ j, S j) :=
    dense_iInter_of_isOpen hopen hdense
  have hne : (⋂ j, S j).Nonempty := by
    simpa using hall.inter_open_nonempty Set.univ isOpen_univ Set.univ_nonempty
  obtain ⟨p, hp⟩ := hne
  refine ⟨p, fun j ↦ ?_⟩
  exact Set.mem_iInter.mp hp j

/-! ## Adding finitely many scalar chart conditions -/

/-- The nonvanishing locus of a nontrivial entire complex-analytic scalar
function is open and dense.  This is the scalar form of the argument used
above for Gram conditions and is useful for imposing affine-chart
denominators at the same time as genericity. -/
theorem isOpen_dense_analytic_ne_zero (h : P → ℂ)
    (han : AnalyticOnNhd ℂ h Set.univ) (hne : ∃ p, h p ≠ 0) :
    IsOpen {p | h p ≠ 0} ∧ Dense {p | h p ≠ 0} := by
  have hopen : IsOpen {p | h p ≠ 0} := by
    change IsOpen (h ⁻¹' ({0} : Set ℂ)ᶜ)
    exact isOpen_compl_singleton.preimage han.continuous
  refine ⟨hopen, dense_iff_inter_open.mpr ?_⟩
  intro U hU hUne
  by_contra hinter
  have hzero : ∀ x ∈ U, h x = 0 := by
    intro x hx
    by_contra hx0
    exact hinter ⟨x, hx, hx0⟩
  obtain ⟨x, hx⟩ := hUne
  have hevent : h =ᶠ[nhds x] 0 := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hzero y hy
  have hall := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ x) hevent
  obtain ⟨y, hy⟩ := hne
  exact hy (hall (Set.mem_univ y))

/-- The common locus for finitely many configuration-genericity conditions
and finitely many scalar nonvanishing conditions. -/
def simultaneouslyGoodAndScalarSet
    {J K : Type*} {n : J → ℕ}
    (F : ∀ j, AnalyticConfigFamily P (n j))
    (h : K → P → ℂ) : Set P :=
  {p | (∀ j, (F j).Good p) ∧ ∀ k, h k p ≠ 0}

/-- The common finite locus is itself open and dense.  Recording openness is
needed later in order to normalize an ambient Gaussian measure on it. -/
theorem simultaneouslyGoodAndScalarSet_isOpen_dense
    {J K : Type*} [Fintype J] [Fintype K] {n : J → ℕ}
    (F : ∀ j, AnalyticConfigFamily P (n j))
    (hex : ∀ j, ∃ p, (F j).Good p)
    (h : K → P → ℂ)
    (han : ∀ k, AnalyticOnNhd ℂ (h k) Set.univ)
    (hne : ∀ k, ∃ p, h k p ≠ 0) :
    IsOpen (simultaneouslyGoodAndScalarSet F h) ∧
      Dense (simultaneouslyGoodAndScalarSet F h) := by
  classical
  let L : J ⊕ K → Set P
    | Sum.inl j => (F j).goodSet
    | Sum.inr k => {p | h k p ≠ 0}
  have hLopen : ∀ l, IsOpen (L l) := by
    intro l
    rcases l with j | k
    · exact ((F j).goodSet_isOpen_dense (hex j)).1
    · exact (isOpen_dense_analytic_ne_zero (h k) (han k) (hne k)).1
  have hLdense : ∀ l, Dense (L l) := by
    intro l
    rcases l with j | k
    · exact ((F j).goodSet_isOpen_dense (hex j)).2
    · exact (isOpen_dense_analytic_ne_zero (h k) (han k) (hne k)).2
  have heq : simultaneouslyGoodAndScalarSet F h = ⋂ l, L l := by
    ext p
    simp [simultaneouslyGoodAndScalarSet, L,
      AnalyticConfigFamily.goodSet]
  rw [heq]
  exact ⟨isOpen_iInter_of_finite hLopen,
    dense_iInter_of_isOpen hLopen hLdense⟩

/-- A finite list of analytic configurations and a finite list of nontrivial
analytic scalar functions have one common parameter satisfying every
genericity and chart condition. -/
theorem exists_simultaneously_good_and_scalar_ne
    {J K : Type*} [Fintype J] [Fintype K] {n : J → ℕ}
    (F : ∀ j, AnalyticConfigFamily P (n j))
    (hex : ∀ j, ∃ p, (F j).Good p)
    (h : K → P → ℂ)
    (han : ∀ k, AnalyticOnNhd ℂ (h k) Set.univ)
    (hne : ∀ k, ∃ p, h k p ≠ 0) :
    ∃ p, (∀ j, (F j).Good p) ∧ ∀ k, h k p ≠ 0 := by
  have hdense :=
    (simultaneouslyGoodAndScalarSet_isOpen_dense F hex h han hne).2
  have hneSet : (simultaneouslyGoodAndScalarSet F h).Nonempty := by
    simpa using hdense.inter_open_nonempty Set.univ isOpen_univ Set.univ_nonempty
  obtain ⟨p, hp⟩ := hneSet
  exact ⟨p, hp⟩

end

end Sp4
