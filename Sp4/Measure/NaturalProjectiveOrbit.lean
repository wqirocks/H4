import Sp4.Cohomology.ExternalInputs
import Sp4.Cohomology.ProjectiveCoordinates
import Sp4.Symplectic.Topology
import Sp4.Measure.ReferenceSix
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Natural Borel orbit charts for generic projective configurations

The orbit classification in `ProjectiveCoordinates` is set-theoretic.  This
file proves that its product parametrizations are Borel isomorphisms for the
*natural* measurable structure inherited from finite products of projective
space.  In particular, no measurable structure is transported from the orbit
coordinates merely to make the parametrizations measurable.

The proof has three concrete ingredients.

* All coordinate ratios of a nonzero vector give a scale-independent
  measurable signature of its projective line; this signature is injective.
  Hence projective space, its finite powers, and their generic subtypes are
  countably separated.
* The normalized four-, five-, and six-point slices are represented by the
  explicit rational vector families in `Chains/Normalized.lean`.  Their
  dependence on the Pfaffian coordinates is continuous.
* Before quotienting by the projective centre, the orbit parametrizations are
  visibly measurable.  Measurability descends through the group quotient, and
  the Lusin--Souslin theorem makes their set-theoretic inverses measurable.

The only external topological input is Struble's general metrization theorem,
recorded in `ExternalInputs.lean`, which supplies the standard-Borel property
of the locally compact second-countable effective group.
-/

namespace Sp4
namespace ProjectiveAction

open MeasureTheory MeasurableSpace
open scoped LinearAlgebra.Projectivization

noncomputable section

/-! ## Countable separation of the natural projective Borel structure -/

/-- The collection of every coordinate-ratio vector.  If the `i`th coordinate
is nonzero, the `i`th component is the unique representative whose `i`th
coordinate is one; if it is zero, division in `ℂ` makes that component zero.
The whole family is therefore both scale independent and injective on lines. -/
def projectiveRatioSignature :
    ProjectivePoint → Fin 4 → SymplecticVector :=
  Projectivization.lift
    (fun v i j => v.1 j / v.1 i)
    (by
      intro a b t hab
      funext i j
      by_cases ht : t = 0
      · exfalso
        apply a.2
        rw [hab, ht, zero_smul]
      · by_cases hbi : b.1 i = 0
        · simp [hab, hbi]
        · rw [hab]
          simp only [Pi.smul_apply, smul_eq_mul]
          field_simp [ht, hbi])

theorem measurable_projectiveRatioSignature :
    Measurable projectiveRatioSignature := by
  rw [measurable_from_projective]
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact ((measurable_pi_apply j).comp measurable_subtype_coe).div
    ((measurable_pi_apply i).comp measurable_subtype_coe)

theorem projectiveRatioSignature_injective :
    Function.Injective projectiveRatioSignature := by
  intro p q hpq
  induction p using Projectivization.ind with
  | h v hv =>
      induction q using Projectivization.ind with
      | h w hw =>
          obtain ⟨i, hvi⟩ : ∃ i : Fin 4, v i ≠ 0 := by
            by_contra h
            simp only [not_exists, not_not] at h
            apply hv
            funext j
            exact h j
          have hii := congrFun (congrFun hpq i) i
          change v i / v i = w i / w i at hii
          have hwi : w i ≠ 0 := by
            by_contra h
            simp [hvi, h] at hii
          rw [Projectivization.mk_eq_mk_iff']
          refine ⟨v i / w i, ?_⟩
          funext j
          change (v i / w i) * w j = v j
          have hij := congrFun (congrFun hpq i) j
          change v j / v i = w j / w i at hij
          field_simp [hvi, hwi] at hij ⊢
          simpa [mul_comm, mul_left_comm, mul_assoc] using hij.symm

/-- A measurable injection into a countably separated measurable space pulls
back a countable separating family. -/
theorem countablySeparated_of_measurable_injective_map
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [CountablySeparated B] (f : A → B) (hf : Measurable f)
    (hinj : Function.Injective f) : CountablySeparated A := by
  rw [countablySeparated_def]
  rcases exists_countable_separating B MeasurableSet Set.univ with
    ⟨S, hSc, hSm, hSsep⟩
  refine ⟨⟨{t | ∃ s ∈ S, t = f ⁻¹' s}, ?_, ?_, ?_⟩⟩
  · have heq : {t | ∃ s ∈ S, t = f ⁻¹' s} =
        (fun s => f ⁻¹' s) '' S := by
      ext t
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨s, hs, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨s, hs, rfl⟩
    rw [heq]
    exact hSc.image _
  · rintro t ⟨s, hs, rfl⟩
    exact hf (hSm s hs)
  · intro x _ y _ hxy
    apply hinj
    apply hSsep (f x) (Set.mem_univ _) (f y) (Set.mem_univ _)
    intro s hs
    simpa using hxy (f ⁻¹' s) ⟨s, hs, rfl⟩

instance projectivePoint_countablySeparated :
    CountablySeparated ProjectivePoint :=
  countablySeparated_of_measurable_injective_map projectiveRatioSignature
    measurable_projectiveRatioSignature projectiveRatioSignature_injective

def projectiveConfigRatioSignature (n : ℕ) :
    ProjectiveConfig n → Fin n → Fin 4 → SymplecticVector :=
  fun x i => projectiveRatioSignature (x i)

theorem measurable_projectiveConfigRatioSignature (n : ℕ) :
    Measurable (projectiveConfigRatioSignature n) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_projectiveRatioSignature.comp (measurable_pi_apply i)

theorem projectiveConfigRatioSignature_injective (n : ℕ) :
    Function.Injective (projectiveConfigRatioSignature n) := by
  intro x y hxy
  funext i
  apply projectiveRatioSignature_injective
  exact congrFun hxy i

instance projectiveConfig_countablySeparated (n : ℕ) :
    CountablySeparated (ProjectiveConfig n) :=
  countablySeparated_of_measurable_injective_map
    (projectiveConfigRatioSignature n)
    (measurable_projectiveConfigRatioSignature n)
    (projectiveConfigRatioSignature_injective n)

instance genericConfig_countablySeparated (n : ℕ) :
    CountablySeparated (OrbitChain.GenericConfig n) :=
  countablySeparated_of_measurable_injective_map Subtype.val
    measurable_subtype_coe Subtype.val_injective

/-! ## Standard Borel coordinate spaces and the effective group -/

instance coord4_polishSpace : PolishSpace Pfaffian.Coord4 :=
  Pfaffian.coord4EquivProd.polishSpace_induced

instance coord5_polishSpace : PolishSpace Pfaffian.Coord5 :=
  Pfaffian.coord5EquivFun.polishSpace_induced

instance coord6_polishSpace : PolishSpace Pfaffian.Coord6 :=
  Pfaffian.coord6EquivFun.polishSpace_induced

instance u4_standardBorelSpace : StandardBorelSpace Pfaffian.U4 :=
  Pfaffian.isOpen_u4Set.measurableSet.standardBorel

instance u5_standardBorelSpace : StandardBorelSpace Pfaffian.U5 :=
  Pfaffian.isOpen_u5Set.measurableSet.standardBorel

/-- Standard-Borel structure transfers across a measurable equivalence.  This
is a short internal consequence of the Lusin--Souslin characterization. -/
theorem standardBorelSpace_of_measurableEquiv
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace B] (e : A ≃ᵐ B) : StandardBorelSpace A := by
  letI := upgradeStandardBorel B
  let tA : TopologicalSpace A := TopologicalSpace.induced e inferInstance
  letI : TopologicalSpace A := tA
  let h : A ≃ₜ B := e.toEquiv.homeomorph
  haveI : PolishSpace A := e.toEquiv.polishSpace_induced
  refine ⟨⟨tA, ?_, inferInstance⟩⟩
  constructor
  rw [borel_comap, ← eq_borel_upgradeStandardBorel B]
  exact e.measurableEmbedding.comap_eq.symm

instance u6_standardBorelSpace : StandardBorelSpace Pfaffian.U6 := by
  letI : StandardBorelSpace Pfaffian.U6Chart :=
    Pfaffian.isOpen_u6ChartSet.measurableSet.standardBorel
  exact standardBorelSpace_of_measurableEquiv
    Pfaffian.u6ChartHomeomorph.toMeasurableEquiv.symm

/-- The projective kernel is closed: it consists of the identity and the
central negative identity. -/
instance projectiveKernel_isClosed :
    IsClosed (projectiveKernel : Set SymplecticGroup) := by
  rw [projectiveKernel_eq]
  exact isClosed_singleton.union isClosed_singleton

/-- Struble's theorem makes the natural lcsc quotient topology on the
effective group Polish. -/
instance effectiveSymplecticGroup_polishSpace :
    PolishSpace EffectiveSymplecticGroup :=
  polishSpace_of_lcsc_topologicalGroup _

/-! ## Continuity of the explicit normalized slices -/

theorem continuous_normalizedVectors4 :
    Continuous OrbitChain.normalizedVectors4 := by
  fun_prop [OrbitChain.normalizedVectors4, Pfaffian.delta4]

theorem continuous_normalizedVectors5 :
    Continuous OrbitChain.normalizedVectors5 := by
  have hfrac : Continuous (fun q : Pfaffian.U5 =>
      (q.1.v - q.1.u - q.1.y) / Pfaffian.p4 q.1) := by
    apply Continuous.div₀
    · fun_prop
    · exact Pfaffian.continuous_p4.comp continuous_subtype_val
    · exact fun q => q.2.p4_ne
  rw [continuous_pi_iff]
  intro i
  rw [continuous_pi_iff]
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [OrbitChain.normalizedVectors5] <;>
    first | exact hfrac | fun_prop

theorem continuous_normalizedVectors6 :
    Continuous OrbitChain.normalizedVectors6 := by
  have hpf : Continuous (fun q : Pfaffian.U6 =>
      Pfaffian.pf0123 q.1) := by
    fun_prop [Pfaffian.pf0123]
  have hfracY : Continuous (fun q : Pfaffian.U6 =>
      (q.1.v - q.1.u - q.1.y) / Pfaffian.pf0123 q.1) := by
    exact (by fun_prop : Continuous (fun q : Pfaffian.U6 =>
      q.1.v - q.1.u - q.1.y)).div₀ hpf (fun q => q.2.pf0123_ne)
  have hfracZ : Continuous (fun q : Pfaffian.U6 =>
      (q.1.s - q.1.u - q.1.z) / Pfaffian.pf0123 q.1) := by
    exact (by fun_prop : Continuous (fun q : Pfaffian.U6 =>
      q.1.s - q.1.u - q.1.z)).div₀ hpf (fun q => q.2.pf0123_ne)
  rw [continuous_pi_iff]
  intro i
  rw [continuous_pi_iff]
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [OrbitChain.normalizedVectors6] <;>
    first
    | exact hfracY
    | exact hfracZ
    | fun_prop [Pfaffian.pf0123, Pfaffian.pf0124, Pfaffian.pf0125]

theorem continuous_symplectic_apply :
    Continuous (fun p : SymplecticGroup × SymplecticVector => p.1.1 p.2) := by
  change Continuous (fun p : SymplecticGroup × SymplecticVector =>
    (symplecticOperatorUnit p.1 :
      SymplecticVector →L[ℂ] SymplecticVector) p.2)
  have hop : Continuous symplecticOperatorUnit := continuous_induced_dom
  have hval : Continuous (fun g : SymplecticGroup =>
      (symplecticOperatorUnit g :
        SymplecticVector →L[ℂ] SymplecticVector)) :=
    Units.continuous_val.comp hop
  exact (hval.comp continuous_fst).clm_apply continuous_snd

/-! ## The four-point natural Borel orbit chart -/

def liftedProductParam4
    (p : SymplecticGroup × Pfaffian.U4) : OrbitChain.GenericConfig 4 :=
  OrbitChain.smulGeneric p.1 (OrbitChain.normalizedConfig4 p.2)

theorem measurable_liftedProductParam4 :
    Measurable liftedProductParam4 := by
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro i
  change Measurable (fun p : SymplecticGroup × Pfaffian.U4 =>
    (liftedProductParam4 p).1 i)
  rw [show (fun p : SymplecticGroup × Pfaffian.U4 =>
      (liftedProductParam4 p).1 i) =
      fun p => Projectivization.mk ℂ
        (p.1.1 • OrbitChain.normalizedVectors4 p.2 i)
        ((smul_ne_zero_iff_ne p.1.1).mpr
          (OrbitChain.normalizedVectors4_ne p.2 i)) by
    funext p
    change p.1.1 • Projectivization.mk ℂ
      (OrbitChain.normalizedVectors4 p.2 i)
      (OrbitChain.normalizedVectors4_ne p.2 i) = _
    rw [Projectivization.smul_mk]]
  have hvec : Measurable (fun p : SymplecticGroup × Pfaffian.U4 =>
      p.1.1 • OrbitChain.normalizedVectors4 p.2 i) := by
    change Measurable (fun p : SymplecticGroup × Pfaffian.U4 =>
      p.1.1 (OrbitChain.normalizedVectors4 p.2 i))
    exact (continuous_symplectic_apply.comp
      (continuous_fst.prodMk
        ((continuous_apply i).comp
          (continuous_normalizedVectors4.comp continuous_snd)))).measurable
  exact measurable_projectivization_mk _ hvec _

def quotientProduct4 :
    SymplecticGroup × Pfaffian.U4 → EffectiveSymplecticGroup × Pfaffian.U4 :=
  fun p => ((p.1 : EffectiveSymplecticGroup), p.2)

theorem measurable_quotientProduct4 : Measurable quotientProduct4 :=
  (QuotientGroup.measurable_coe.comp measurable_fst).prodMk measurable_snd

theorem quotientProduct4_surjective : Function.Surjective quotientProduct4 := by
  rintro ⟨g, q⟩
  induction g using Quotient.inductionOn' with
  | _ g => exact ⟨(g, q), rfl⟩

theorem orbitProductEquiv4_comp_quotientProduct4 :
    orbitProductEquiv4 ∘ quotientProduct4 = liftedProductParam4 := by
  funext p
  rfl

theorem measurable_orbitProductEquiv4_natural :
    Measurable orbitProductEquiv4 := by
  apply (measurable_quotientProduct4.measurable_comp_iff_of_surjective
    quotientProduct4_surjective).mp
  rw [orbitProductEquiv4_comp_quotientProduct4]
  exact measurable_liftedProductParam4

theorem measurableEmbedding_orbitProductEquiv4_natural :
    MeasurableEmbedding orbitProductEquiv4 :=
  measurable_orbitProductEquiv4_natural.measurableEmbedding
    orbitProductEquiv4.injective

/-- The global four-point orbit chart for the natural projective Borel
structure. -/
def orbitProductMeasurableEquiv4 :
    EffectiveSymplecticGroup × Pfaffian.U4 ≃ᵐ OrbitChain.GenericConfig 4 where
  toEquiv := orbitProductEquiv4
  measurable_toFun := measurable_orbitProductEquiv4_natural
  measurable_invFun := by
    intro s hs
    rw [show orbitProductEquiv4.symm ⁻¹' s = orbitProductEquiv4 '' s by
      ext x
      simp]
    exact measurableEmbedding_orbitProductEquiv4_natural.measurableSet_image' hs

/-! ## The five-point natural Borel orbit chart -/

def liftedProductParam5
    (p : SymplecticGroup × Pfaffian.U5) : OrbitChain.GenericConfig 5 :=
  OrbitChain.smulGeneric p.1 (OrbitChain.normalizedConfig5 p.2)

theorem measurable_liftedProductParam5 :
    Measurable liftedProductParam5 := by
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro i
  change Measurable (fun p : SymplecticGroup × Pfaffian.U5 =>
    (liftedProductParam5 p).1 i)
  rw [show (fun p : SymplecticGroup × Pfaffian.U5 =>
      (liftedProductParam5 p).1 i) =
      fun p => Projectivization.mk ℂ
        (p.1.1 • OrbitChain.normalizedVectors5 p.2 i)
        ((smul_ne_zero_iff_ne p.1.1).mpr
          (OrbitChain.normalizedVectors5_ne p.2 i)) by
    funext p
    change p.1.1 • Projectivization.mk ℂ
      (OrbitChain.normalizedVectors5 p.2 i)
      (OrbitChain.normalizedVectors5_ne p.2 i) = _
    rw [Projectivization.smul_mk]]
  have hvec : Measurable (fun p : SymplecticGroup × Pfaffian.U5 =>
      p.1.1 • OrbitChain.normalizedVectors5 p.2 i) := by
    change Measurable (fun p : SymplecticGroup × Pfaffian.U5 =>
      p.1.1 (OrbitChain.normalizedVectors5 p.2 i))
    exact (continuous_symplectic_apply.comp
      (continuous_fst.prodMk
        ((continuous_apply i).comp
          (continuous_normalizedVectors5.comp continuous_snd)))).measurable
  exact measurable_projectivization_mk _ hvec _

def quotientProduct5 :
    SymplecticGroup × Pfaffian.U5 → EffectiveSymplecticGroup × Pfaffian.U5 :=
  fun p => ((p.1 : EffectiveSymplecticGroup), p.2)

theorem measurable_quotientProduct5 : Measurable quotientProduct5 :=
  (QuotientGroup.measurable_coe.comp measurable_fst).prodMk measurable_snd

theorem quotientProduct5_surjective : Function.Surjective quotientProduct5 := by
  rintro ⟨g, q⟩
  induction g using Quotient.inductionOn' with
  | _ g => exact ⟨(g, q), rfl⟩

theorem orbitProductEquiv5_comp_quotientProduct5 :
    orbitProductEquiv5 ∘ quotientProduct5 = liftedProductParam5 := by
  funext p
  rfl

theorem measurable_orbitProductEquiv5_natural :
    Measurable orbitProductEquiv5 := by
  apply (measurable_quotientProduct5.measurable_comp_iff_of_surjective
    quotientProduct5_surjective).mp
  rw [orbitProductEquiv5_comp_quotientProduct5]
  exact measurable_liftedProductParam5

theorem measurableEmbedding_orbitProductEquiv5_natural :
    MeasurableEmbedding orbitProductEquiv5 :=
  measurable_orbitProductEquiv5_natural.measurableEmbedding
    orbitProductEquiv5.injective

/-- The global five-point orbit chart for the natural projective Borel
structure. -/
def orbitProductMeasurableEquiv5 :
    EffectiveSymplecticGroup × Pfaffian.U5 ≃ᵐ OrbitChain.GenericConfig 5 where
  toEquiv := orbitProductEquiv5
  measurable_toFun := measurable_orbitProductEquiv5_natural
  measurable_invFun := by
    intro s hs
    rw [show orbitProductEquiv5.symm ⁻¹' s = orbitProductEquiv5 '' s by
      ext x
      simp]
    exact measurableEmbedding_orbitProductEquiv5_natural.measurableSet_image' hs

/-! ## The six-point natural Borel orbit chart -/

def liftedProductParam6
    (p : SymplecticGroup × Pfaffian.U6) : OrbitChain.GenericConfig 6 :=
  OrbitChain.smulGeneric p.1 (OrbitChain.normalizedConfig6 p.2)

theorem measurable_liftedProductParam6 :
    Measurable liftedProductParam6 := by
  apply Measurable.subtype_mk
  apply measurable_pi_lambda
  intro i
  change Measurable (fun p : SymplecticGroup × Pfaffian.U6 =>
    (liftedProductParam6 p).1 i)
  rw [show (fun p : SymplecticGroup × Pfaffian.U6 =>
      (liftedProductParam6 p).1 i) =
      fun p => Projectivization.mk ℂ
        (p.1.1 • OrbitChain.normalizedVectors6 p.2 i)
        ((smul_ne_zero_iff_ne p.1.1).mpr
          (OrbitChain.normalizedVectors6_ne p.2 i)) by
    funext p
    change p.1.1 • Projectivization.mk ℂ
      (OrbitChain.normalizedVectors6 p.2 i)
      (OrbitChain.normalizedVectors6_ne p.2 i) = _
    rw [Projectivization.smul_mk]]
  have hvec : Measurable (fun p : SymplecticGroup × Pfaffian.U6 =>
      p.1.1 • OrbitChain.normalizedVectors6 p.2 i) := by
    change Measurable (fun p : SymplecticGroup × Pfaffian.U6 =>
      p.1.1 (OrbitChain.normalizedVectors6 p.2 i))
    exact (continuous_symplectic_apply.comp
      (continuous_fst.prodMk
        ((continuous_apply i).comp
          (continuous_normalizedVectors6.comp continuous_snd)))).measurable
  exact measurable_projectivization_mk _ hvec _

def quotientProduct6 :
    SymplecticGroup × Pfaffian.U6 → EffectiveSymplecticGroup × Pfaffian.U6 :=
  fun p => ((p.1 : EffectiveSymplecticGroup), p.2)

theorem measurable_quotientProduct6 : Measurable quotientProduct6 :=
  (QuotientGroup.measurable_coe.comp measurable_fst).prodMk measurable_snd

theorem quotientProduct6_surjective : Function.Surjective quotientProduct6 := by
  rintro ⟨g, q⟩
  induction g using Quotient.inductionOn' with
  | _ g => exact ⟨(g, q), rfl⟩

theorem orbitProductEquiv6_comp_quotientProduct6 :
    orbitProductEquiv6 ∘ quotientProduct6 = liftedProductParam6 := by
  funext p
  rfl

theorem measurable_orbitProductEquiv6_natural :
    Measurable orbitProductEquiv6 := by
  apply (measurable_quotientProduct6.measurable_comp_iff_of_surjective
    quotientProduct6_surjective).mp
  rw [orbitProductEquiv6_comp_quotientProduct6]
  exact measurable_liftedProductParam6

theorem measurableEmbedding_orbitProductEquiv6_natural :
    MeasurableEmbedding orbitProductEquiv6 :=
  measurable_orbitProductEquiv6_natural.measurableEmbedding
    orbitProductEquiv6.injective

/-- The global six-point orbit chart for the natural projective Borel
structure. -/
def orbitProductMeasurableEquiv6 :
    EffectiveSymplecticGroup × Pfaffian.U6 ≃ᵐ OrbitChain.GenericConfig 6 where
  toEquiv := orbitProductEquiv6
  measurable_toFun := measurable_orbitProductEquiv6_natural
  measurable_invFun := by
    intro s hs
    rw [show orbitProductEquiv6.symm ⁻¹' s = orbitProductEquiv6 '' s by
      ext x
      simp]
    exact measurableEmbedding_orbitProductEquiv6_natural.measurableSet_image' hs

/-! The natural measurable structures on the three generic configuration
spaces are standard Borel.  This also lets Lusin--Souslin recognize the
inclusions into the countably separated ambient projective powers as
measurable embeddings. -/

instance genericConfig4_standardBorelSpace :
    StandardBorelSpace (OrbitChain.GenericConfig 4) :=
  standardBorelSpace_of_measurableEquiv orbitProductMeasurableEquiv4.symm

instance genericConfig5_standardBorelSpace :
    StandardBorelSpace (OrbitChain.GenericConfig 5) :=
  standardBorelSpace_of_measurableEquiv orbitProductMeasurableEquiv5.symm

instance genericConfig6_standardBorelSpace :
    StandardBorelSpace (OrbitChain.GenericConfig 6) :=
  standardBorelSpace_of_measurableEquiv orbitProductMeasurableEquiv6.symm

end
end ProjectiveAction
end Sp4
