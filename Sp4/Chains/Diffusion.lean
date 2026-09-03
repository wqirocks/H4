import Sp4.Chains.Measure
import Sp4.Measure.ReciprocalWeight
import Sp4.Measure.SmoothProbability

/-!
# Finite diffusion of point-supported chains

The averaged chain is defined as a finite sum of pushforwards.  No
measure-valued Bochner integral is used.  The lemmas below justify passing
pointwise signed-Dirac identities to identities of signed measures and give
the exact mass and absolute-continuity estimates needed by the two-cone
argument.
-/

namespace Sp4
namespace MeasureChain

noncomputable section

open MeasureTheory
open Pfaffian OrbitChain
open scoped BigOperators ENNReal

variable {P X Y J : Type*} [MeasurableSpace P] [MeasurableSpace X]
  [MeasurableSpace Y] [Fintype J]

/-- The finite signed Dirac chain at one parameter value. -/
def pointDirac (c : J → ℝ) (f : J → P → X) (p : P) : SignedMeasure X :=
  ∑ j, c j • signedDirac (f j p)

/-- Average a finite family of points by a finite source measure.  This
finite sum of signed pushforwards is the primary definition. -/
def averagedDirac (mu : Measure P) [IsFiniteMeasure mu]
    (c : J → ℝ) (f : J → P → X) : SignedMeasure X :=
  ∑ j, c j • mu.toSignedMeasure.map (f j)

variable [MeasurableSingletonClass X]

theorem integrable_pointDirac
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c : J → ℝ) (f : J → P → X) (p : P) (g : X → E) :
    (pointDirac c f p).Integrable g := by
  rw [pointDirac]
  apply VectorMeasure.Integrable.finsetSum_vectorMeasure
  intro j _hj
  exact (integrable_signedDirac g (f j p)).smul_vectorMeasure _

theorem integral_pointDirac
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c : J → ℝ) (f : J → P → X) (p : P) (g : X → E) :
    (∫ᵛ x, g x ∂<•(pointDirac c f p)) = ∑ j, c j • g (f j p) := by
  rw [pointDirac, VectorMeasure.integral_finsetSum_vectorMeasure]
  · simp_rw [VectorMeasure.integral_smul_vectorMeasure,
      integral_signedDirac]
  · intro j _hj
    exact (integrable_signedDirac g (f j p)).smul_vectorMeasure _

theorem integrable_averagedDirac
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : Measure P) [IsFiniteMeasure mu]
    (c : J → ℝ) (f : J → P → X) (hf : ∀ j, Measurable (f j))
    (g : X → E) (hg : StronglyMeasurable g)
    (hint : ∀ j, Integrable (g ∘ f j) mu) :
    (averagedDirac mu c f).Integrable g := by
  rw [averagedDirac]
  apply VectorMeasure.Integrable.finsetSum_vectorMeasure
  intro j _hj
  apply VectorMeasure.Integrable.smul_vectorMeasure
  apply VectorMeasure.Integrable.map hg.aestronglyMeasurable
  simpa [VectorMeasure.Integrable] using hint j

/-- Integrating an averaged finite chain is the ordinary integral of its
pointwise finite evaluation. -/
theorem integral_averagedDirac
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : Measure P) [IsFiniteMeasure mu]
    (c : J → ℝ) (f : J → P → X) (hf : ∀ j, Measurable (f j))
    (g : X → E) (hg : StronglyMeasurable g)
    (hint : ∀ j, Integrable (g ∘ f j) mu) :
    (∫ᵛ x, g x ∂<•(averagedDirac mu c f)) =
      ∫ p, (∑ j, c j • g (f j p)) ∂mu := by
  rw [averagedDirac, VectorMeasure.integral_finsetSum_vectorMeasure]
  · simp_rw [VectorMeasure.integral_smul_vectorMeasure]
    have hmap (j : J) :
        (∫ᵛ x, g x ∂<•(mu.toSignedMeasure.map (f j))) =
          ∫ p, g (f j p) ∂mu := by
      have hi : mu.toSignedMeasure.Integrable (g ∘ f j) := by
        simpa [VectorMeasure.Integrable] using hint j
      rw [VectorMeasure.integral_map (hf j) hg.aestronglyMeasurable hi,
        VectorMeasure.integral_toSignedMeasure]
    simp_rw [hmap]
    rw [integral_finsetSum]
    · simp_rw [integral_smul]
    · intro j _hj
      exact (hint j).smul (c j)
  · intro j _hj
    apply VectorMeasure.Integrable.smul_vectorMeasure
    apply VectorMeasure.Integrable.map hg.aestronglyMeasurable
    simpa [VectorMeasure.Integrable] using hint j

/-- A pointwise identity between finite signed Dirac chains remains true
after averaging.  The proof uses bounded measurable test functions, so the
conclusion is equality of signed measures rather than only a weak identity
against continuous tests. -/
theorem averagedDirac_eq_zero_of_pointwise
    (mu : Measure P) [IsFiniteMeasure mu]
    (c : J → ℝ) (f : J → P → X) (hf : ∀ j, Measurable (f j))
    (hpoint : ∀ p, pointDirac c f p = 0) :
    averagedDirac mu c f = 0 := by
  apply signedMeasure_ext_of_integral_eq
  intro g hg hbound
  have hint : ∀ j, Integrable (g ∘ f j) mu := by
    intro j
    apply (integrable_const (1 : ℝ)).mono
    · exact (hg.comp_measurable (hf j)).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs, norm_one]
      exact hbound (f j p)
  rw [integral_averagedDirac mu c f hf g hg hint]
  have hz : (fun p ↦ ∑ j, c j • g (f j p)) = 0 := by
    funext p
    have hp := congrArg
      (fun nu : SignedMeasure X ↦ ∫ᵛ x, g x ∂<•nu) (hpoint p)
    rw [integral_pointDirac, VectorMeasure.integral_zero_vectorMeasure] at hp
    exact hp
  rw [hz]
  simp

/-- The source measure, viewed as a signed measure, is absolutely continuous
with respect to itself. -/
theorem toSignedMeasure_isAbsolutelyContinuous
    (mu : Measure P) [IsFiniteMeasure mu] :
    IsAbsolutelyContinuous mu.toSignedMeasure mu := by
  intro s hs
  simpa using hs

/-- A finite sum of nonsingular pushforwards is absolutely continuous. -/
theorem averagedDirac_isAbsolutelyContinuous
    (mu : Measure P) [IsFiniteMeasure mu]
    (xi : Measure X) (c : J → ℝ) (f : J → P → X)
    (hf : ∀ j, Measure.QuasiMeasurePreserving (f j) mu xi) :
    IsAbsolutelyContinuous (averagedDirac mu c f) xi := by
  rw [averagedDirac]
  apply IsAbsolutelyContinuous.finsetSum Finset.univ
  intro j _hj
  exact ((toSignedMeasure_isAbsolutelyContinuous mu).map (hf j)).smul (c j)

/-- The total variation of a finite averaged chain is bounded by its
displayed coefficient mass times the mass of the source. -/
theorem mass_averagedDirac_le
    (mu : Measure P) [IsFiniteMeasure mu]
    (c : J → ℝ) (f : J → P → X) (hf : ∀ j, Measurable (f j)) :
    mass (averagedDirac mu c f) ≤
      (∑ j, |c j|) * mu.real Set.univ := by
  rw [averagedDirac]
  calc
    mass (∑ j, c j • mu.toSignedMeasure.map (f j)) ≤
        ∑ j, mass (c j • mu.toSignedMeasure.map (f j)) :=
      mass_finset_sum_le Finset.univ _
    _ ≤ ∑ j, |c j| * mu.real Set.univ := by
      apply Finset.sum_le_sum
      intro j _hj
      rw [mass_smul]
      gcongr
      calc
        mass (mu.toSignedMeasure.map (f j)) ≤ mass mu.toSignedMeasure :=
          mass_map_le mu.toSignedMeasure (hf j)
        _ = mu.real Set.univ := by simp [mass]
    _ = (∑ j, |c j|) * mu.real Set.univ := by
      rw [Finset.sum_mul]

theorem mass_averagedDirac_le_of_probability
    (mu : Measure P) [IsProbabilityMeasure mu]
    (c : J → ℝ) (f : J → P → X) (hf : ∀ j, Measurable (f j)) :
    mass (averagedDirac mu c f) ≤ ∑ j, |c j| := by
  simpa using mass_averagedDirac_le mu c f hf

/-! ## Finite pushforward operators commute with averaging -/

/-- A finite real linear combination of measurable pushforward maps. -/
structure FiniteMapOperator (X Y K : Type*) [MeasurableSpace X]
    [MeasurableSpace Y] [Fintype K] where
  coeff : K → ℝ
  map : K → X → Y
  measurable : ∀ k, Measurable (map k)

namespace FiniteMapOperator

variable {K : Type*} [Fintype K]

def apply (T : FiniteMapOperator X Y K) :
    SignedMeasure X →ₗ[ℝ] SignedMeasure Y :=
  ∑ k, T.coeff k • pushforward (T.map k)

theorem apply_def (T : FiniteMapOperator X Y K) (nu : SignedMeasure X) :
    T.apply nu = ∑ k, T.coeff k • nu.map (T.map k) := by
  simp [apply, pushforward]

def pairedCoeff (T : FiniteMapOperator X Y K) (c : J → ℝ) : K × J → ℝ :=
  fun kj ↦ T.coeff kj.1 * c kj.2

def pairedPoint (T : FiniteMapOperator X Y K)
    (f : J → P → X) : K × J → P → Y :=
  fun kj p ↦ T.map kj.1 (f kj.2 p)

theorem measurable_pairedPoint (T : FiniteMapOperator X Y K)
    (f : J → P → X) (hf : ∀ j, Measurable (f j)) (kj : K × J) :
    Measurable (T.pairedPoint f kj) :=
  (T.measurable kj.1).comp (hf kj.2)

theorem apply_pointDirac [MeasurableSingletonClass X]
    [MeasurableSingletonClass Y]
    (T : FiniteMapOperator X Y K) (c : J → ℝ)
    (f : J → P → X) (p : P) :
    T.apply (pointDirac c f p) =
      pointDirac (T.pairedCoeff c) (T.pairedPoint f) p := by
  classical
  rw [T.apply_def, pointDirac, pointDirac]
  simp only [map_fintype_sum, VectorMeasure.map_smul,
    map_signedDirac _ _ (T.measurable _)]
  rw [Fintype.sum_prod_type]
  simp [pairedCoeff, pairedPoint, Finset.smul_sum, smul_smul]

theorem apply_averagedDirac [MeasurableSingletonClass X]
    [MeasurableSingletonClass Y]
    (T : FiniteMapOperator X Y K)
    (mu : Measure P) [IsFiniteMeasure mu]
    (c : J → ℝ) (f : J → P → X) (hf : ∀ j, Measurable (f j)) :
    T.apply (averagedDirac mu c f) =
      averagedDirac mu (T.pairedCoeff c) (T.pairedPoint f) := by
  classical
  rw [T.apply_def, averagedDirac, averagedDirac]
  simp only [map_fintype_sum, VectorMeasure.map_smul,
    MeasureChain.map_map _ (hf _) (T.measurable _)]
  rw [Fintype.sum_prod_type]
  simp only [pairedCoeff, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro j _hj
  congr 2

/-- A finite pushforward operator takes an averaged pointwise kernel
identity to an actual signed-measure identity. -/
theorem apply_averagedDirac_eq_zero_of_pointwise
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (T : FiniteMapOperator X Y K)
    (mu : Measure P) [IsFiniteMeasure mu]
    (c : J → ℝ) (f : J → P → X) (hf : ∀ j, Measurable (f j))
    (hpoint : ∀ p, T.apply (pointDirac c f p) = 0) :
    T.apply (averagedDirac mu c f) = 0 := by
  rw [T.apply_averagedDirac mu c f hf]
  apply averagedDirac_eq_zero_of_pointwise
    mu (T.pairedCoeff c) (T.pairedPoint f) (T.measurable_pairedPoint f hf)
  intro p
  rw [← T.apply_pointDirac c f p]
  exact hpoint p

end FiniteMapOperator

/-! ## The boundary of the alternated five-point average -/

abbrev BoundaryAlternationIndex :=
  Equiv.Perm (Fin 5) × Fin 5

/-- The finite pushforward operator equal to `boundary4 ∘ alternation4`. -/
def boundaryAlternationOperator :
    FiniteMapOperator U5 U4 BoundaryAlternationIndex where
  coeff := fun si ↦
    (1 / (Nat.factorial 5 : ℝ)) *
      permSign ℝ si.1 * (-1 : ℝ) ^ si.2.val
  map := fun si ↦ face4At si.2 ∘ permute5 si.1
  measurable := fun si ↦
    (measurable_face4At si.2).comp (measurable_permute5 si.1)

theorem boundaryAlternationOperator_apply (nu : SignedMeasure U5) :
    boundaryAlternationOperator.apply nu =
      boundary4 (alternation4 nu) := by
  classical
  rw [FiniteMapOperator.apply_def, Fintype.sum_prod_type,
    boundary4_apply, alternation4_apply]
  simp only [boundaryAlternationOperator, VectorMeasure.map_smul,
    map_fintype_sum]
  simp_rw [map_map _ (measurable_permute5 _) (measurable_face4At _),
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sigma _hsigma
  apply Finset.sum_congr rfl
  intro i _hi
  congr 1
  ring

/-- If every finite point chain is a cycle, then its alternated diffusion is
a cycle as an equality of signed measures. -/
theorem boundary4_alternation4_averagedDirac_eq_zero
    {J : Type*} [Fintype J] {P : Type*} [MeasurableSpace P]
    (mu : Measure P) [IsFiniteMeasure mu]
    (c : J → ℝ) (f : J → P → U5) (hf : ∀ j, Measurable (f j))
    (hcycle : ∀ p, boundary4 (alternation4 (pointDirac c f p)) = 0) :
    boundary4 (alternation4 (averagedDirac mu c f)) = 0 := by
  rw [← boundaryAlternationOperator_apply]
  apply boundaryAlternationOperator.apply_averagedDirac_eq_zero_of_pointwise
    mu c f hf
  intro p
  rw [boundaryAlternationOperator_apply]
  exact hcycle p

/-! ## Pairing an alternating function with a diffusion -/

/-- Alternating projection does not change the integral of an alternating
function.  The explicit integrability assumptions are exactly the finitely
many pullbacks occurring in the definition of `alternation4`. -/
theorem integral_alternation4_eq_self
    (nu : SignedMeasure U5) (g : U5 → ℝ)
    (hg : StronglyMeasurable g) (hgAlt : IsAlternatingFunction5 g)
    (hperm : ∀ sigma : Equiv.Perm (Fin 5),
      nu.Integrable (g ∘ permute5 sigma)) :
    (∫ᵛ q, g q ∂<•(alternation4 nu)) = ∫ᵛ q, g q ∂<•nu := by
  rw [alternation4_apply, VectorMeasure.integral_smul_vectorMeasure]
  rw [VectorMeasure.integral_finsetSum_vectorMeasure]
  · simp_rw [VectorMeasure.integral_smul_vectorMeasure]
    have hmap (sigma : Equiv.Perm (Fin 5)) :
        (∫ᵛ q, g q ∂<•(nu.map (permute5 sigma))) =
          permSign ℝ sigma • (∫ᵛ q, g q ∂<•nu) := by
      rw [VectorMeasure.integral_map (measurable_permute5 sigma)
        hg.aestronglyMeasurable (hperm sigma)]
      rw [show (fun q => g (permute5 sigma q)) =
          (fun q => permSign ℝ sigma • g q) by
        funext q
        exact hgAlt sigma q]
      rw [integral_flip_eq_integral nu _, integral_flip_eq_integral nu g]
      exact VectorMeasure.integral_fun_smul nu
        (ContinuousLinearMap.lsmul ℝ ℝ) _ _
    simp_rw [hmap, smul_smul, permSign_sq, one_smul]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    norm_num
  · intro sigma _hsigma
    exact VectorMeasure.Integrable.smul_vectorMeasure
      (VectorMeasure.Integrable.map hg.aestronglyMeasurable (hperm sigma))
      (permSign ℝ sigma)

/-- The finite orbit chain represented by a parameterized list of generic
five-tuples. -/
def orbitChainAt {J P : Type*} [Fintype J]
    (c : J → ℝ) (x : J → P → GenericConfig 5) (p : P) :
    OrbitChain.Module ℝ 5 :=
  ∑ j, c j • OrbitChain.ofConfig (x j p)

/-- The signed-measure diffusion of a finite parameterized orbit chain. -/
def diffusedOrbitChain {J P : Type*} [Fintype J] [MeasurableSpace P]
    (mu : Measure P) [IsFiniteMeasure mu]
    (c : J → ℝ) (x : J → P → GenericConfig 5) : SignedMeasure U5 :=
  alternation4 (averagedDirac mu c
    (fun j p => orbitCoord5 (x j p)))

theorem alternation4_pointDirac_orbitCoord_eq_diracMap
    {J P : Type*} [Fintype J]
    (c : J → ℝ) (x : J → P → GenericConfig 5) (p : P) :
    alternation4
        (pointDirac c (fun j p => orbitCoord5 (x j p)) p) =
      diracMap5 (orbitChainAt c x p) := by
  classical
  simp only [pointDirac, orbitChainAt, map_sum, LinearMap.map_smul,
    diracMap5_ofConfig, diracConfig5]

/-- Pointwise orbit-cycle identities pass to the parameter diffusion as a
literal equality of signed measures. -/
theorem boundary_diffusedOrbitChain_eq_zero
    {J P : Type*} [Fintype J] [MeasurableSpace P]
    (mu : Measure P) [IsFiniteMeasure mu]
    (c : J → ℝ) (x : J → P → GenericConfig 5)
    (hx : ∀ j, Measurable (fun p => orbitCoord5 (x j p)))
    (hcycle : ∀ p, OrbitChain.boundary ℝ 4 (orbitChainAt c x p) = 0) :
    boundary4 (diffusedOrbitChain mu c x) = 0 := by
  apply boundary4_alternation4_averagedDirac_eq_zero mu c
    (fun j p => orbitCoord5 (x j p)) hx
  intro p
  rw [alternation4_pointDirac_orbitCoord_eq_diracMap,
    diracMap_boundary, hcycle p, map_zero]

/-- If every coordinate map is nonsingular, the diffused orbit chain is
absolutely continuous for the reference measure on `U5`. -/
theorem diffusedOrbitChain_isAbsolutelyContinuous
    {J P : Type*} [Fintype J] [MeasurableSpace P]
    (mu : Measure P) [IsFiniteMeasure mu]
    (c : J → ℝ) (x : J → P → GenericConfig 5)
    (hx : ∀ j (sigma : Equiv.Perm (Fin 5)),
      Measure.QuasiMeasurePreserving
        (fun p => permute5 sigma (orbitCoord5 (x j p))) mu measureU5) :
    IsAbsolutelyContinuous (diffusedOrbitChain mu c x) measureU5 := by
  classical
  rw [diffusedOrbitChain, alternation4_apply, averagedDirac]
  apply IsAbsolutelyContinuous.smul
  apply IsAbsolutelyContinuous.finsetSum Finset.univ
  intro sigma _hsigma
  apply IsAbsolutelyContinuous.smul
  rw [map_fintype_sum]
  apply IsAbsolutelyContinuous.finsetSum Finset.univ
  intro j _hj
  have hcoord : Measurable (fun p => orbitCoord5 (x j p)) := by
    simpa using (hx j (1 : Equiv.Perm (Fin 5))).measurable
  rw [VectorMeasure.map_smul,
    map_map _ hcoord (measurable_permute5 sigma)]
  apply IsAbsolutelyContinuous.smul
  apply (toSignedMeasure_isAbsolutelyContinuous mu).map
  change Measure.QuasiMeasurePreserving
    (fun p => permute5 sigma (orbitCoord5 (x j p))) mu measureU5
  exact hx j sigma

/-- The reciprocal-weight construction supplies exactly these hypotheses:
integrability of every primitive face after every permutation and every
elementary output.  They imply facewise integrability against the fully
alternated diffused signed measure. -/
theorem integrable_face_diffusedOrbitChain
    {J P : Type*} [Fintype J] [MeasurableSpace P]
    (mu : Measure P) [IsFiniteMeasure mu]
    (c : J → ℝ) (x : J → P → GenericConfig 5)
    (hx : ∀ j, Measurable (fun p ↦ orbitCoord5 (x j p)))
    (f : U4 → ℝ) (hf : StronglyMeasurable f)
    (hint : ∀ j (sigma : Equiv.Perm (Fin 5)) (i : Fin 5),
      Integrable
        (fun p ↦ f (face4At i (permute5 sigma (orbitCoord5 (x j p))))) mu)
    (i : Fin 5) :
    (diffusedOrbitChain mu c x).Integrable (f ∘ face4At i) := by
  classical
  rw [diffusedOrbitChain, alternation4_apply, averagedDirac]
  apply VectorMeasure.Integrable.smul_vectorMeasure
  apply VectorMeasure.Integrable.finsetSum_vectorMeasure
  intro sigma _hsigma
  apply VectorMeasure.Integrable.smul_vectorMeasure
  rw [map_fintype_sum]
  apply VectorMeasure.Integrable.finsetSum_vectorMeasure
  intro j _hj
  rw [VectorMeasure.map_smul,
    map_map _ (hx j) (measurable_permute5 sigma)]
  apply VectorMeasure.Integrable.smul_vectorMeasure
  apply VectorMeasure.Integrable.map
    ((hf.comp_measurable (measurable_face4At i)).aestronglyMeasurable)
  simpa [VectorMeasure.Integrable, Function.comp_def] using hint j sigma i

/-- The displayed coefficient mass controls the total variation of the
diffused orbit chain. -/
theorem mass_diffusedOrbitChain_le
    {J P : Type*} [Fintype J] [MeasurableSpace P]
    (mu : Measure P) [IsProbabilityMeasure mu]
    (c : J → ℝ) (x : J → P → GenericConfig 5)
    (hx : ∀ j, Measurable (fun p => orbitCoord5 (x j p))) :
    mass (diffusedOrbitChain mu c x) ≤ ∑ j, |c j| := by
  exact (mass_alternation4_le _).trans
    (mass_averagedDirac_le_of_probability mu c
      (fun j p => orbitCoord5 (x j p)) hx)

/-- Averaging preserves the algebraic period of a parameterized finite orbit
chain.  This statement is deliberately phrased with ordinary scalar
integrability on the parameter space. -/
theorem integral_diffusedOrbitChain_eq
    {J P : Type*} [Fintype J] [MeasurableSpace P]
    (mu : Measure P) [IsFiniteMeasure mu]
    (c : J → ℝ) (x : J → P → GenericConfig 5)
    (hx : ∀ j, Measurable (fun p => orbitCoord5 (x j p)))
    (g : U5 → ℝ) (hg : StronglyMeasurable g)
    (hgAlt : IsAlternatingFunction5 g)
    (hint : ∀ j, Integrable (g ∘ fun p => orbitCoord5 (x j p)) mu) :
    (∫ᵛ q, g q ∂<•(diffusedOrbitChain mu c x)) =
      ∫ p, evaluation5 g hgAlt (orbitChainAt c x p) ∂mu := by
  let coord : J → P → U5 := fun j p => orbitCoord5 (x j p)
  have hraw :
      (∫ᵛ q, g q ∂<•(averagedDirac mu c coord)) =
        ∫ p, (∑ j, c j • g (coord j p)) ∂mu :=
    integral_averagedDirac mu c coord hx g hg hint
  have hperm (sigma : Equiv.Perm (Fin 5)) :
      (averagedDirac mu c coord).Integrable (g ∘ permute5 sigma) := by
    apply integrable_averagedDirac mu c coord hx
      (g ∘ permute5 sigma)
      (hg.comp_measurable (measurable_permute5 sigma))
    intro j
    have heq :
        (g ∘ permute5 sigma) ∘ coord j =
          fun p => permSign ℝ sigma • (g ∘ coord j) p := by
      funext p
      exact hgAlt sigma (coord j p)
    rw [heq]
    exact (hint j).smul (permSign ℝ sigma)
  rw [diffusedOrbitChain,
    integral_alternation4_eq_self _ g hg hgAlt hperm, hraw]
  congr 1
  funext p
  simp only [orbitChainAt, map_sum, LinearMap.map_smul,
    evaluation5_ofConfig]
  rfl

end
end MeasureChain
end Sp4
