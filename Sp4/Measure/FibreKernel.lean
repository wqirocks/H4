import Sp4.Measure.L0
import Sp4.Measure.SmoothSubmersion
import Sp4.Pfaffian.Operators
import Sp4.Cohomology.ExternalInputs

/-!
Interfaces between fibrewise regularization and the a.e. function spaces.

The structures in this file do not assert that a regularizer exists.  They package
the precise, representative-independent output that must be constructed from a
properly supported vertical probability kernel.  This keeps the algebraic constant-
seven proof independent from the later differential-topological construction.
-/

namespace Sp4

open MeasureTheory ProbabilityTheory

variable {X Y : Type*}
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y}

/-- The a.e.-class of a continuous real-valued function. -/
def continuousClass (g : X → ℝ) (hg : Continuous g) : L0 X μ :=
  AEEqFun.mk g hg.aestronglyMeasurable

theorem coeFn_continuousClass (g : X → ℝ) (hg : Continuous g) :
    (continuousClass (μ := μ) g hg : X → ℝ) =ᵐ[μ] g :=
  AEEqFun.coeFn_mk _ _

/-- A continuous representative modulo an explicitly bounded a.e.-class. -/
structure ContinuousModuloBounded (f : L0 X μ) (M : ℝ) where
  representative : X → ℝ
  continuous : Continuous representative
  error : Linfty X μ
  error_coe : error.1 = f - continuousClass representative continuous
  norm_error_le : ‖error‖ ≤ M

/-- Generic regularization property for a linear defect operator.  Establishing this
property is the sole task of the fibre-kernel construction; consuming it requires no
choice of pointwise representative of the input class. -/
def HasContinuousRegularization
    (A : L0 X μ →ₗ[ℝ] L0 Y ν) : Prop :=
  ∀ (f : L0 X μ) (F : Linfty Y ν), A f = F.1 →
    Nonempty (ContinuousModuloBounded f ‖F‖)

end Sp4

namespace Sp4.Pfaffian

noncomputable section

open MeasureTheory ProbabilityTheory

/-! ## The projection and nuisance maps used by fibrewise averaging -/

/-- The base projection in the article's splitting
`(u,v,w,x,y) = ((u,w),(v,x,y))`. -/
def fibreProjection : U5 → U4 := face4_4

/-- The four non-base faces in the sliced formula for `D`. -/
def nuisanceFace : Fin 4 → U5 → U4
  | 0 => face4_0
  | 1 => face4_1
  | 2 => face4_2
  | 3 => face4_3

@[continuity, fun_prop]
theorem continuous_fibreProjection : Continuous fibreProjection :=
  continuous_face4_4

@[continuity, fun_prop]
theorem continuous_nuisanceFace (i : Fin 4) : Continuous (nuisanceFace i) := by
  fin_cases i <;> simp only [nuisanceFace] <;>
    first
    | exact continuous_face4_0
    | exact continuous_face4_1
    | exact continuous_face4_2
    | exact continuous_face4_3

/-- The sliced five-term differential, with the base term displayed separately. -/
theorem D_eq_nuisance_faces {A : Type*} [AddGroup A] (f : U4 → A) (q : U5) :
    D f q =
      f (nuisanceFace 0 q) - f (nuisanceFace 1 q) +
        f (nuisanceFace 2 q) - f (nuisanceFace 3 q) + f (fibreProjection q) :=
  rfl

/-- The base projection is onto.  This is the article's finite-avoidance
construction, specialized to the harmless choices `v = x = 1`. -/
theorem fibreProjection_surjective : Function.Surjective fibreProjection := by
  intro z
  obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset
    ({0, z.1.x - z.1.y, 1 - z.1.y, 1 - z.1.x} : Finset ℂ)
  have hy0 : y ≠ 0 := by
    intro h
    apply hy
    simp [h]
  have hyp0 : y - z.1.x * 1 + 1 * z.1.y ≠ 0 := by
    intro h
    apply hy
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    left
    apply sub_eq_zero.mp
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  have hyp1 : y - 1 + z.1.y ≠ 0 := by
    intro h
    apply hy
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    right
    left
    apply sub_eq_zero.mp
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  have hyp2 : y - 1 + z.1.x ≠ 0 := by
    intro h
    apply hy
    simp only [Finset.mem_insert, Finset.mem_singleton]
    right
    right
    right
    apply sub_eq_zero.mp
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
  let q : Coord5 := ⟨z.1.x, 1, z.1.y, 1, y⟩
  have hq : IsU5 q := by
    refine ⟨z.2.x_ne, one_ne_zero, z.2.y_ne, one_ne_zero, hy0, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [q, p0] using hyp0
    · simpa [q, p1] using hyp1
    · simpa [q, p2] using hyp2
    · simp [q, p3]
    · intro h
      change z.1.y - z.1.x + 1 = 0 at h
      apply z.2.delta_ne
      dsimp [delta4]
      linear_combination h
  refine ⟨⟨q, hq⟩, ?_⟩
  apply Subtype.ext
  rfl

/-! ## Kernel-checked differential-rank certificates -/

/-- Ambient coordinate projection extending `fibreProjection`. -/
def ambientFibreProjection (q : Coord5) : Coord4 := ⟨q.u, q.w⟩

/-- Ambient rational maps extending the four nuisance faces. -/
def ambientNuisanceFace : Fin 4 → Coord5 → Coord4
  | 0 => fun q => ⟨q.u * q.x / (q.v * q.w), q.y / (q.v * q.w)⟩
  | 1 => fun q => ⟨q.x / q.w, q.y / q.w⟩
  | 2 => fun q => ⟨q.v / q.u, q.y / q.u⟩
  | 3 => fun q => ⟨q.v, q.x⟩

/-- The ambient version of `(π,θᵢ)`. -/
def ambientCombinedFace (i : Fin 4) (q : Coord5) : Coord4 × Coord4 :=
  (ambientFibreProjection q, ambientNuisanceFace i q)

@[simp]
theorem ambientFibreProjection_restrict (q : U5) :
    ambientFibreProjection q.1 = (fibreProjection q).1 := rfl

@[simp]
theorem ambientNuisanceFace_restrict (i : Fin 4) (q : U5) :
    ambientNuisanceFace i q.1 = (nuisanceFace i q).1 := by
  fin_cases i <;> rfl

/-- A local right inverse for `ambientCombinedFace i` through the prescribed
point.  Only the first branch uses division; its denominator is the base `u`
coordinate and is nonzero near every point of `U5`. -/
def ambientCombinedFaceSection (i : Fin 4) (q : Coord5) :
    Coord4 × Coord4 → Coord5 :=
  match i with
  | 0 => fun a =>
      ⟨a.1.x, q.v, a.1.y, a.2.x * q.v * a.1.y / a.1.x,
        a.2.y * q.v * a.1.y⟩
  | 1 => fun a =>
      ⟨a.1.x, q.v, a.1.y, a.2.x * a.1.y, a.2.y * a.1.y⟩
  | 2 => fun a =>
      ⟨a.1.x, a.2.x * a.1.x, a.1.y, q.x, a.2.y * a.1.x⟩
  | 3 => fun a =>
      ⟨a.1.x, a.2.x, a.1.y, a.2.y, q.y⟩

theorem ambientCombinedFaceSection_at (i : Fin 4) (q : U5) :
    ambientCombinedFaceSection i q.1 (ambientCombinedFace i q.1) = q.1 := by
  fin_cases i
  all_goals
    apply Coord5.ext <;>
      simp [ambientCombinedFaceSection, ambientCombinedFace,
        ambientFibreProjection, ambientNuisanceFace]
  all_goals field_simp [q.2.u_ne, q.2.v_ne, q.2.w_ne]

/-- The displayed section is a right inverse on a neighborhood of the relevant
target point.  This is the exact local-normal-form certificate used for the rank
calculation. -/
theorem eventually_ambientCombinedFace_section (i : Fin 4) (q : U5) :
    ambientCombinedFace i ∘ ambientCombinedFaceSection i q.1 =ᶠ[
      nhds (ambientCombinedFace i q.1)] id := by
  have hu : ∀ᶠ a in nhds (ambientCombinedFace i q.1), a.1.x ≠ 0 :=
    (continuous_coord4_x.comp continuous_fst).continuousAt.eventually_ne q.2.u_ne
  have hw : ∀ᶠ a in nhds (ambientCombinedFace i q.1), a.1.y ≠ 0 :=
    (continuous_coord4_y.comp continuous_fst).continuousAt.eventually_ne q.2.w_ne
  fin_cases i
  · filter_upwards [hu, hw] with a hua hwa
    apply Prod.ext <;> apply Coord4.ext <;>
      simp [ambientCombinedFaceSection, ambientCombinedFace,
        ambientFibreProjection, ambientNuisanceFace]
    all_goals field_simp [hua, hwa, q.2.v_ne]
  · filter_upwards [hw] with a hwa
    apply Prod.ext <;> apply Coord4.ext <;>
      simp [ambientCombinedFaceSection, ambientCombinedFace,
        ambientFibreProjection, ambientNuisanceFace]
    all_goals field_simp [hwa]
  · filter_upwards [hu] with a hua
    apply Prod.ext <;> apply Coord4.ext <;>
      simp [ambientCombinedFaceSection, ambientCombinedFace,
        ambientFibreProjection, ambientNuisanceFace]
    all_goals field_simp [hua]
  · filter_upwards with a
    apply Prod.ext <;> apply Coord4.ext <;>
      simp [ambientCombinedFaceSection, ambientCombinedFace,
        ambientFibreProjection, ambientNuisanceFace]

theorem differentiableAt_ambientCombinedFace (i : Fin 4) (q : U5) :
    DifferentiableAt ℂ (ambientCombinedFace i) q.1 := by
  fin_cases i
  · simp only [ambientCombinedFace, ambientFibreProjection, ambientNuisanceFace]
    apply DifferentiableAt.prodMk <;> apply differentiableAt_coord4_mk <;>
      fun_prop (disch := exact mul_ne_zero q.2.v_ne q.2.w_ne)
  · simp only [ambientCombinedFace, ambientFibreProjection, ambientNuisanceFace]
    apply DifferentiableAt.prodMk <;> apply differentiableAt_coord4_mk <;>
      fun_prop (disch := exact q.2.w_ne)
  · simp only [ambientCombinedFace, ambientFibreProjection, ambientNuisanceFace]
    apply DifferentiableAt.prodMk <;> apply differentiableAt_coord4_mk <;>
      fun_prop (disch := exact q.2.u_ne)
  · simp only [ambientCombinedFace, ambientFibreProjection, ambientNuisanceFace]
    apply DifferentiableAt.prodMk <;> apply differentiableAt_coord4_mk <;> fun_prop

theorem differentiableAt_ambientCombinedFaceSection (i : Fin 4) (q : U5) :
    DifferentiableAt ℂ (ambientCombinedFaceSection i q.1)
      (ambientCombinedFace i q.1) := by
  fin_cases i
  · simp only [ambientCombinedFaceSection]
    apply differentiableAt_coord5_mk <;>
      fun_prop (disch := simpa [ambientCombinedFace, ambientFibreProjection,
        ambientNuisanceFace] using q.2.u_ne)
  · simp only [ambientCombinedFaceSection]
    apply differentiableAt_coord5_mk <;> fun_prop
  · simp only [ambientCombinedFaceSection]
    apply differentiableAt_coord5_mk <;> fun_prop
  · simp only [ambientCombinedFaceSection]
    apply differentiableAt_coord5_mk <;> fun_prop

/-- Each `(π,θᵢ)` has surjective complex Fréchet derivative on `U5`.
The proof uses the explicit local sections above and the chain rule. -/
theorem ambientCombinedFace_hasSurjectiveComplexFDerivAt (i : Fin 4) (q : U5) :
    HasSurjectiveComplexFDerivAt (ambientCombinedFace i) q.1 := by
  refine ⟨differentiableAt_ambientCombinedFace i q, ?_⟩
  let s := ambientCombinedFaceSection i q.1
  let a := ambientCombinedFace i q.1
  have hs : DifferentiableAt ℂ s a :=
    differentiableAt_ambientCombinedFaceSection i q
  have hf : DifferentiableAt ℂ (ambientCombinedFace i) (s a) := by
    rw [show s a = q.1 from ambientCombinedFaceSection_at i q]
    exact differentiableAt_ambientCombinedFace i q
  have hcomp := fderiv_comp a hf hs
  have heq : fderiv ℂ (ambientCombinedFace i ∘ s) a = 1 := by
    rw [(eventually_ambientCombinedFace_section i q).fderiv_eq]
    exact fderiv_id
  have hright : Function.RightInverse (fderiv ℂ s a)
      (fderiv ℂ (ambientCombinedFace i) q.1) := by
    intro v
    have hc := congrArg
      (fun L : (Coord4 × Coord4) →L[ℂ] (Coord4 × Coord4) => L v)
      (hcomp.symm.trans heq)
    simpa [s, a, ambientCombinedFaceSection_at i q] using hc
  exact hright.surjective

theorem ambientNuisanceFace_eq_snd_comp (i : Fin 4) :
    ambientNuisanceFace i = Prod.snd ∘ ambientCombinedFace i := by
  funext q
  rfl

/-- Each nuisance face separately is a submersion as well.  It follows from the
stronger rank certificate for `(π,θᵢ)` by projecting to the second factor. -/
theorem ambientNuisanceFace_hasSurjectiveComplexFDerivAt (i : Fin 4) (q : U5) :
    HasSurjectiveComplexFDerivAt (ambientNuisanceFace i) q.1 := by
  have hcomb := ambientCombinedFace_hasSurjectiveComplexFDerivAt i q
  have hsnd : DifferentiableAt ℂ (Prod.snd : Coord4 × Coord4 → Coord4)
      (ambientCombinedFace i q.1) := by fun_prop
  have hchain := fderiv_comp q.1 hsnd hcomb.1
  rw [← ambientNuisanceFace_eq_snd_comp i] at hchain
  refine ⟨?_, ?_⟩
  · rw [ambientNuisanceFace_eq_snd_comp]
    exact hsnd.comp q.1 hcomb.1
  · intro y
    obtain ⟨x, hx⟩ := hcomb.2 (0, y)
    refine ⟨x, ?_⟩
    have hc := congrArg (fun L : Coord5 →L[ℂ] Coord4 => L x) hchain
    rw [ContinuousLinearMap.comp_apply, hx, fderiv_snd] at hc
    simpa using hc

/-- A section of the base coordinate projection through `q`. -/
def ambientFibreProjectionSection (q : Coord5) (z : Coord4) : Coord5 :=
  ⟨z.x, q.v, z.y, q.x, q.y⟩

@[simp]
theorem ambientFibreProjection_section (q : Coord5) (z : Coord4) :
    ambientFibreProjection (ambientFibreProjectionSection q z) = z := rfl

@[simp]
theorem ambientFibreProjectionSection_at (q : Coord5) :
    ambientFibreProjectionSection q (ambientFibreProjection q) = q := by
  apply Coord5.ext <;> rfl

/-- The base projection itself has surjective derivative. -/
theorem ambientFibreProjection_hasSurjectiveComplexFDerivAt (q : U5) :
    HasSurjectiveComplexFDerivAt ambientFibreProjection q.1 := by
  have hf : DifferentiableAt ℂ ambientFibreProjection q.1 := by
    apply differentiableAt_coord4_mk <;> fun_prop
  refine ⟨hf, ?_⟩
  let s := ambientFibreProjectionSection q.1
  let a := ambientFibreProjection q.1
  have hs : DifferentiableAt ℂ s a := by
    apply differentiableAt_coord5_mk <;> fun_prop
  have hsa : s a = q.1 := ambientFibreProjectionSection_at q.1
  have hfa : DifferentiableAt ℂ ambientFibreProjection (s a) := by
    rw [hsa]
    exact hf
  have hcomp := fderiv_comp a hfa hs
  rw [hsa] at hcomp
  have heq : fderiv ℂ (ambientFibreProjection ∘ s) a = 1 := by
    have hfun : ambientFibreProjection ∘ s = id := by
      funext z
      exact ambientFibreProjection_section q.1 z
    rw [hfun]
    exact fderiv_id
  have hright : Function.RightInverse (fderiv ℂ s a)
      (fderiv ℂ ambientFibreProjection q.1) := by
    intro v
    have hc := congrArg (fun L : Coord4 →L[ℂ] Coord4 => L v)
      (hcomp.symm.trans heq)
    simpa using hc
  exact hright.surjective

/-! ## Nonsingularity of the five face maps -/

/-- Each nuisance face is nonsingular for the concrete normalized Gaussian
measures.  All coordinate and rank checks are proved above; the only external
ingredient is the general coarea theorem recorded in `ExternalInputs`. -/
theorem nuisanceFace_quasiMeasurePreserving (i : Fin 4) :
    Measure.QuasiMeasurePreserving (nuisanceFace i) measureU5 measureU4 := by
  have hmem : ∀ x, x ∈ u5Set → ambientNuisanceFace i x ∈ u4Set := by
    intro x hx
    let q : U5 := ⟨x, hx⟩
    fin_cases i
    · exact face4Coord0_mem q
    · exact face4Coord1_mem q
    · exact face4Coord2_mem q
    · exact face4Coord3_mem q
  have h := quasiMeasurePreserving_normalizedOpenGaussian_of_submersion
    coord5Gaussian coord4Gaussian
    coord5GaussianPresentation coord4GaussianPresentation
    u5Set isOpen_u5Set u5Set_nonempty
    u4Set isOpen_u4Set u4Set_nonempty
    (ambientNuisanceFace i)
    hmem
    (by
      intro x hx
      exact ambientNuisanceFace_hasSurjectiveComplexFDerivAt i ⟨x, hx⟩)
  change Measure.QuasiMeasurePreserving (nuisanceFace i)
    (normalizedOpenMeasure coord5Gaussian u5Set isOpen_u5Set u5Set_nonempty)
    (normalizedOpenMeasure coord4Gaussian u4Set isOpen_u4Set u4Set_nonempty)
  refine h.congr (continuous_nuisanceFace i).measurable ?_
  filter_upwards with q
  apply Subtype.ext
  fin_cases i <;> rfl

/-- The base projection is nonsingular for the concrete normalized Gaussian
measures. -/
theorem fibreProjection_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving fibreProjection measureU5 measureU4 := by
  have hmem : ∀ x, x ∈ u5Set → ambientFibreProjection x ∈ u4Set := by
    intro x hx
    exact face4Coord4_mem ⟨x, hx⟩
  have h := quasiMeasurePreserving_normalizedOpenGaussian_of_submersion
    coord5Gaussian coord4Gaussian
    coord5GaussianPresentation coord4GaussianPresentation
    u5Set isOpen_u5Set u5Set_nonempty
    u4Set isOpen_u4Set u4Set_nonempty
    ambientFibreProjection
    hmem
    (by
      intro x hx
      exact ambientFibreProjection_hasSurjectiveComplexFDerivAt ⟨x, hx⟩)
  change Measure.QuasiMeasurePreserving fibreProjection
    (normalizedOpenMeasure coord5Gaussian u5Set isOpen_u5Set u5Set_nonempty)
    (normalizedOpenMeasure coord4Gaussian u4Set isOpen_u4Set u4Set_nonempty)
  refine h.congr continuous_fibreProjection.measurable ?_
  filter_upwards with q
  apply Subtype.ext
  rfl

/-- Nonsingularity package for all five face maps entering the measurable
differential `D0`. -/
theorem concreteFace4QuasiMeasurePreserving :
    Face4QuasiMeasurePreserving measureU4 measureU5 where
  face0 := nuisanceFace_quasiMeasurePreserving 0
  face1 := nuisanceFace_quasiMeasurePreserving 1
  face2 := nuisanceFace_quasiMeasurePreserving 2
  face3 := nuisanceFace_quasiMeasurePreserving 3
  face4 := fibreProjection_quasiMeasurePreserving

/-- The properly supported vertical probability kernel for the article's
projection and four nuisance maps.  The ambient rank certificates and projection
surjectivity are all proved in this file; only the generic differential-topology
construction is imported from `ExternalInputs`. -/
theorem exists_concreteSmoothFibreKernel :
    Nonempty (SmoothFibreKernel measureU4 measureU5
      fibreProjection nuisanceFace) := by
  apply exists_smoothFibreKernel_normalizedOpenGaussian_of_submersions
    coord5Gaussian coord4Gaussian
    coord5GaussianPresentation coord4GaussianPresentation
    u5Set isOpen_u5Set u5Set_nonempty
    u4Set isOpen_u4Set u4Set_nonempty
    fibreProjection nuisanceFace
    ambientFibreProjection ambientNuisanceFace
  · intro q
    exact ambientFibreProjection_restrict q
  · intro i q
    exact (ambientNuisanceFace_restrict i q).symm
  · exact fibreProjection_surjective
  · intro x hx
    exact ambientFibreProjection_hasSurjectiveComplexFDerivAt ⟨x, hx⟩
  · intro i x hx
    change HasSurjectiveComplexFDerivAt (ambientCombinedFace i) x
    exact ambientCombinedFace_hasSurjectiveComplexFDerivAt i ⟨x, hx⟩

/-- The representative of a bounded `D0`-defect agrees almost everywhere with
the displayed five-term pointwise differential. -/
theorem D_representative_ae_eq
    (f : L0 U4 measureU4) (F : Linfty U5 measureU5)
    (hF : D0 concreteFace4QuasiMeasurePreserving f = F.1) :
    D f =ᵐ[measureU5] F := by
  have hclass :
      (D0 concreteFace4QuasiMeasurePreserving f : U5 → ℝ) =ᵐ[measureU5] F := by
    rw [hF]
  exact (coeFn_D0 concreteFace4QuasiMeasurePreserving f).symm.trans hclass

/-- Local essential boundedness, implemented by the four-kernel union-bound
argument in the article.  In particular, the canonical representative of `f` is
locally integrable, which is the input needed by proper fibre integration. -/
theorem locallyIntegrable_of_bounded_defect
    (K : SmoothFibreKernel measureU4 measureU5 fibreProjection nuisanceFace)
    (f : L0 U4 measureU4) (F : Linfty U5 measureU5)
    (hF : D0 concreteFace4QuasiMeasurePreserving f = F.1) :
    LocallyIntegrable (fun z => f z) measureU4 := by
  letI : IsMarkovKernel K.kernel := K.markov
  have hDF : D f =ᵐ[measureU5] F := D_representative_ae_eq f F hF
  have hDFbound : ∀ᵐ q ∂measureU5, D f q = F q ∧ |F q| ≤ ‖F‖ :=
    hDF.and (Linfty.ae_abs_le_norm F)
  have hfibreDF :
      ∀ᵐ z ∂measureU4, ∀ᵐ q ∂K.kernel z,
        D f q = F q ∧ |F q| ≤ ‖F‖ :=
    K.ae_ae hDFbound
  intro z₀
  obtain ⟨V, hVopen, hz₀V, C, hC, hdom⟩ := K.local_density_bound z₀
  let C' : ℝ := max C 1
  have hCC' : C ≤ C' := le_max_left _ _
  have hC'pos : 0 < C' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨n, hn⟩ := SmoothFibreKernel.exists_nat_measureReal_abs_gt_lt
    (mu := measureU4) (fun z => f z) f.stronglyMeasurable
    (show 0 < 1 / (4 * C') by positivity)
  let tail : Set U4 := {z | (n : ℝ) < |f z|}
  have htailmeas : MeasurableSet tail := by
    dsimp [tail]
    measurability
  have htail : measureU4.real tail < 1 / (4 * C') := by
    simpa [tail] using hn
  have hlocal :
      ∀ᵐ z ∂measureU4.restrict V, |f z| ≤ ‖F‖ + 4 * (n : ℝ) := by
    apply (ae_restrict_iff' hVopen.measurableSet).2
    filter_upwards [hfibreDF] with z hz hzV
    let bad : Fin 4 → Set U5 := fun i => nuisanceFace i ⁻¹' tail
    have hbadmeas (i : Fin 4) : MeasurableSet (bad i) :=
      (K.nuisance_measurable i) htailmeas
    have hbadlt (i : Fin 4) :
        (K.kernel z).real (bad i) < (1 / 4 : ℝ) := by
      calc
        (K.kernel z).real (bad i) ≤ C * measureU4.real tail := by
          exact hdom z hzV i tail htailmeas
        _ ≤ C' * measureU4.real tail := by
          gcongr
        _ < C' * (1 / (4 * C')) :=
          mul_lt_mul_of_pos_left htail hC'pos
        _ = 1 / 4 := by
          field_simp [ne_of_gt hC'pos]
    have hbadUnionMeas : MeasurableSet (⋃ i, bad i) :=
      MeasurableSet.iUnion hbadmeas
    have hbadUnion : (K.kernel z).real (⋃ i, bad i) < 1 := by
      calc
        (K.kernel z).real (⋃ i, bad i) ≤
            ∑ i : Fin 4, (K.kernel z).real (bad i) :=
          measureReal_iUnion_fintype_le bad
        _ < ∑ _i : Fin 4, (1 / 4 : ℝ) :=
          Finset.sum_lt_sum_of_nonempty (by simp) fun i _ => hbadlt i
        _ = 1 := by norm_num
    have hgoodReal : 0 < (K.kernel z).real (⋃ i, bad i)ᶜ := by
      rw [probReal_compl_eq_one_sub hbadUnionMeas]
      linarith
    have hgoodMeasure : K.kernel z (⋃ i, bad i)ᶜ ≠ 0 :=
      (measureReal_ne_zero_iff (μ := K.kernel z)).mp hgoodReal.ne'
    have hgoodFrequently : ∃ᶠ q in ae (K.kernel z), q ∈ (⋃ i, bad i)ᶜ :=
      frequently_ae_iff.2 hgoodMeasure
    obtain ⟨q, hqgood, hqDF, hqproj⟩ :=
      (hgoodFrequently.and_eventually
        (hz.and (K.projection_ae z))).exists
    have htheta (i : Fin 4) : |f (nuisanceFace i q)| ≤ (n : ℝ) := by
      by_contra hnot
      have htailq : nuisanceFace i q ∈ tail := by
        change (n : ℝ) < |f (nuisanceFace i q)|
        exact lt_of_not_ge hnot
      have hqbad : q ∈ ⋃ i, bad i := Set.mem_iUnion_of_mem i htailq
      exact hqgood hqbad
    have heq :
        f z = F q - f (nuisanceFace 0 q) + f (nuisanceFace 1 q) -
          f (nuisanceFace 2 q) + f (nuisanceFace 3 q) := by
      rw [← hqproj, ← hqDF.1, D_eq_nuisance_faces]
      ring
    rw [heq, abs_le]
    have hFpair := (abs_le.mp hqDF.2)
    have h0 := abs_le.mp (htheta 0)
    have h1 := abs_le.mp (htheta 1)
    have h2 := abs_le.mp (htheta 2)
    have h3 := abs_le.mp (htheta 3)
    constructor <;> linarith
  refine ⟨V, hVopen.mem_nhds hz₀V, ?_⟩
  apply IntegrableOn.of_bound (measure_lt_top measureU4 V)
    f.stronglyMeasurable.aestronglyMeasurable.restrict
    (‖F‖ + 4 * (n : ℝ))
  simpa only [Real.norm_eq_abs] using hlocal

/-! ## The smoothing average -/

/-- The signed average of the four nuisance terms.  The base term is omitted,
exactly as in the displayed definition of `Sf` in the article. -/
def fibreSmooth
    (K : SmoothFibreKernel measureU4 measureU5 fibreProjection nuisanceFace)
    (f : L0 U4 measureU4) (z : U4) : ℝ :=
  -(∫ q, f (nuisanceFace 0 q) ∂(K.kernel z)) +
    (∫ q, f (nuisanceFace 1 q) ∂(K.kernel z)) -
    (∫ q, f (nuisanceFace 2 q) ∂(K.kernel z)) +
    (∫ q, f (nuisanceFace 3 q) ∂(K.kernel z))

theorem continuous_fibreSmooth
    (K : SmoothFibreKernel measureU4 measureU5 fibreProjection nuisanceFace)
    (f : L0 U4 measureU4)
    (hloc : LocallyIntegrable (fun z => f z) measureU4) :
    Continuous (fibreSmooth K f) := by
  exact (((K.nuisance_average_continuous (fun z => f z) hloc 0).neg.add
    (K.nuisance_average_continuous (fun z => f z) hloc 1)).sub
      (K.nuisance_average_continuous (fun z => f z) hloc 2)).add
        (K.nuisance_average_continuous (fun z => f z) hloc 3)

/-- Fibrewise integration of the sliced identity.  This holds at every base
point because the kernel is supported on the corresponding fibre; no a.e.
identity has been restricted to a point-set fibre here. -/
theorem fibreSmooth_error_eq_integral
    (K : SmoothFibreKernel measureU4 measureU5 fibreProjection nuisanceFace)
    (f : L0 U4 measureU4)
    (hloc : LocallyIntegrable (fun z => f z) measureU4) (z : U4) :
    f z - fibreSmooth K f z = ∫ q, D f q ∂(K.kernel z) := by
  letI : IsMarkovKernel K.kernel := K.markov
  have h0 : Integrable (fun q => f (nuisanceFace 0 q)) (K.kernel z) := by
    simpa [Function.comp_def] using K.nuisance_integrable (fun z => f z) hloc z 0
  have h1 : Integrable (fun q => f (nuisanceFace 1 q)) (K.kernel z) := by
    simpa [Function.comp_def] using K.nuisance_integrable (fun z => f z) hloc z 1
  have h2 : Integrable (fun q => f (nuisanceFace 2 q)) (K.kernel z) := by
    simpa [Function.comp_def] using K.nuisance_integrable (fun z => f z) hloc z 2
  have h3 : Integrable (fun q => f (nuisanceFace 3 q)) (K.kernel z) := by
    simpa [Function.comp_def] using K.nuisance_integrable (fun z => f z) hloc z 3
  have h01 : Integrable
      (fun q => f (nuisanceFace 0 q) - f (nuisanceFace 1 q)) (K.kernel z) :=
    h0.sub h1
  have h012 : Integrable
      (fun q => f (nuisanceFace 0 q) - f (nuisanceFace 1 q) +
        f (nuisanceFace 2 q)) (K.kernel z) :=
    h01.add h2
  have h0123 : Integrable
      (fun q => f (nuisanceFace 0 q) - f (nuisanceFace 1 q) +
        f (nuisanceFace 2 q) - f (nuisanceFace 3 q)) (K.kernel z) :=
    h012.sub h3
  have hc : Integrable (fun _q : U5 => f z) (K.kernel z) :=
    integrable_const _
  have heq : D f =ᵐ[K.kernel z]
      fun q => f (nuisanceFace 0 q) - f (nuisanceFace 1 q) +
        f (nuisanceFace 2 q) - f (nuisanceFace 3 q) + f z := by
    filter_upwards [K.projection_ae z] with q hq
    rw [D_eq_nuisance_faces, hq]
  rw [integral_congr_ae heq]
  rw [integral_add h0123 hc, integral_sub h012 h3,
    integral_add h01 h2, integral_sub h0 h1]
  simp only [integral_const, probReal_univ, one_smul]
  unfold fibreSmooth
  ring

/-- Averaging the bounded pointwise defect against a probability fibre kernel
gives the sharp error bound one. -/
theorem fibreSmooth_error_ae_bound
    (K : SmoothFibreKernel measureU4 measureU5 fibreProjection nuisanceFace)
    (f : L0 U4 measureU4) (F : Linfty U5 measureU5)
    (hF : D0 concreteFace4QuasiMeasurePreserving f = F.1) :
    ∀ᵐ z ∂measureU4, |f z - fibreSmooth K f z| ≤ ‖F‖ := by
  letI : IsMarkovKernel K.kernel := K.markov
  have hloc := locallyIntegrable_of_bounded_defect K f F hF
  have hDF : D f =ᵐ[measureU5] F := D_representative_ae_eq f F hF
  have hDbound : ∀ᵐ q ∂measureU5, |D f q| ≤ ‖F‖ := by
    filter_upwards [hDF, Linfty.ae_abs_le_norm F] with q hq hFq
    calc
      |D f q| = |F q| := congrArg abs hq
      _ ≤ ‖F‖ := hFq
  have hfibreBound :
      ∀ᵐ z ∂measureU4, ∀ᵐ q ∂K.kernel z, |D f q| ≤ ‖F‖ :=
    K.ae_ae hDbound
  filter_upwards [hfibreBound] with z hz
  rw [fibreSmooth_error_eq_integral K f hloc z]
  have hz' : ∀ᵐ q ∂K.kernel z, ‖D f q‖ ≤ ‖F‖ := by
    simpa only [Real.norm_eq_abs] using hz
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := K.kernel z) hz')

/-- The fully constructed regularization package for any chosen geometric fibre
kernel.  The local boundedness, Fubini transfer, integral identity, and norm
estimate are all proved above rather than included in the external interface. -/
theorem hasContinuousRegularization_of_smoothFibreKernel
    (K : SmoothFibreKernel measureU4 measureU5 fibreProjection nuisanceFace) :
    HasContinuousRegularization (D0 concreteFace4QuasiMeasurePreserving) := by
  intro f F hF
  let g : U4 → ℝ := fibreSmooth K f
  have hg : Continuous g :=
    continuous_fibreSmooth K f (locallyIntegrable_of_bounded_defect K f F hF)
  let g0 : L0 U4 measureU4 := continuousClass g hg
  let err0 : L0 U4 measureU4 := f - g0
  have herrBound : ∀ᵐ z ∂measureU4, |err0 z| ≤ ‖F‖ := by
    filter_upwards [AEEqFun.coeFn_sub f g0,
      coeFn_continuousClass (μ := measureU4) g hg,
      fibreSmooth_error_ae_bound K f F hF] with z hsub hg0 hbound
    rw [hsub, Pi.sub_apply, hg0]
    exact hbound
  let err : Linfty U4 measureU4 :=
    Linfty.ofClassBound err0 ‖F‖ (norm_nonneg F) herrBound
  refine ⟨⟨g, hg, err, ?_, ?_⟩⟩
  · change err0 = f - continuousClass g hg
    rfl
  · exact Linfty.norm_ofClassBound_le err0 ‖F‖ (norm_nonneg F) herrBound

/-- A fixed choice of the standard properly supported smooth fibre kernel. -/
noncomputable def concreteSmoothFibreKernel :
    SmoothFibreKernel measureU4 measureU5 fibreProjection nuisanceFace :=
  Classical.choice exists_concreteSmoothFibreKernel

/-- Unconditional continuous regularization for the concrete measures and face
maps used by the Pfaffian complex. -/
theorem concrete_hasContinuousRegularization :
    HasContinuousRegularization (D0 concreteFace4QuasiMeasurePreserving) :=
  hasContinuousRegularization_of_smoothFibreKernel concreteSmoothFibreKernel

end

end Sp4.Pfaffian
