import Sp4.Cohomology.ExternalInputs
import Sp4.Pfaffian.Operators

/-!
# A concrete reference measure on the six-point Pfaffian locus

The Pfaffian equation is linear in the last normalized Gram coordinate.  We
therefore identify `U6` with an explicit open subset of `ℂ⁸`, put the normalized
product Gaussian on that chart, and transport it to `U6`.  The nonsingularity of
the six deletion maps is derived below from their explicitly checked submersion
property and the generic coarea input in `ExternalInputs`; it is not postulated
as an article-specific assumption.
-/

namespace Sp4
namespace Pfaffian

noncomputable section

open MeasureTheory

/-- The eight free coordinates in the graph chart for the Pfaffian equation. -/
abbrev Coord8 := Fin 8 → ℂ

/-- The rational last coordinate obtained by solving `pi6 = 0`. -/
def chartR (p : Coord8) : ℂ :=
  (p 2 * p 3 - p 2 * p 4 + p 2 * p 6 - p 5 * p 0 +
      p 5 * p 1 - p 5 * p 6 + p 0 * p 4 - p 1 * p 3 -
      p 1 * p 7 + p 4 * p 7 - p 6 + p 7) /
    (p 3 - p 0 + 1)

theorem chartR_mul_den (p : Coord8) (hp : p 3 - p 0 + 1 ≠ 0) :
    chartR p * (p 3 - p 0 + 1) =
      p 2 * p 3 - p 2 * p 4 + p 2 * p 6 - p 5 * p 0 +
        p 5 * p 1 - p 5 * p 6 + p 0 * p 4 - p 1 * p 3 -
        p 1 * p 7 + p 4 * p 7 - p 6 + p 7 := by
  rw [chartR, div_mul_cancel₀ _ hp]

/-- The graph of the rational solution, in the coordinate order
`(u,v,s,w,x,t,y,z,r)`. -/
def chartCoord6 (p : Coord8) : Coord6 :=
  ⟨p 0, p 1, p 2, p 3, p 4, p 5, p 6, p 7, chartR p⟩

@[simp] theorem chartCoord6_u (p : Coord8) : (chartCoord6 p).u = p 0 := rfl
@[simp] theorem chartCoord6_v (p : Coord8) : (chartCoord6 p).v = p 1 := rfl
@[simp] theorem chartCoord6_s (p : Coord8) : (chartCoord6 p).s = p 2 := rfl
@[simp] theorem chartCoord6_w (p : Coord8) : (chartCoord6 p).w = p 3 := rfl
@[simp] theorem chartCoord6_x (p : Coord8) : (chartCoord6 p).x = p 4 := rfl
@[simp] theorem chartCoord6_t (p : Coord8) : (chartCoord6 p).t = p 5 := rfl
@[simp] theorem chartCoord6_y (p : Coord8) : (chartCoord6 p).y = p 6 := rfl
@[simp] theorem chartCoord6_z (p : Coord8) : (chartCoord6 p).z = p 7 := rfl
@[simp] theorem chartCoord6_r (p : Coord8) : (chartCoord6 p).r = chartR p := rfl

/-- The open set on which the graph is defined and all generic discriminants
are nonzero. -/
def chartDenSet : Set Coord8 := {p | p 3 - p 0 + 1 ≠ 0}

def u6ChartSet : Set Coord8 :=
  chartDenSet ∩ chartCoord6 ⁻¹' {q | u6Discriminant q ≠ 0}

abbrev U6Chart := {p : Coord8 // p ∈ u6ChartSet}

theorem isOpen_chartDenSet : IsOpen chartDenSet := by
  exact isOpen_ne_fun (by fun_prop) continuous_const

theorem differentiableAt_chartCoord6 {p : Coord8} (hp : p ∈ chartDenSet) :
    DifferentiableAt ℂ chartCoord6 p := by
  change DifferentiableAt ℂ
    (fun z : Coord8 => coord6LinearIsometryEquivFun.symm
      (![z 0, z 1, z 2, z 3, z 4, z 5, z 6, z 7, chartR z])) p
  apply coord6LinearIsometryEquivFun.toContinuousLinearEquiv.symm.differentiableAt.comp p
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;> simp [chartR] <;>
    fun_prop (disch := simpa [chartDenSet] using hp)

theorem continuousOn_chartCoord6 : ContinuousOn chartCoord6 chartDenSet := by
  intro p hp
  exact (differentiableAt_chartCoord6 hp).continuousAt.continuousWithinAt

theorem isOpen_u6ChartSet : IsOpen u6ChartSet := by
  apply continuousOn_chartCoord6.isOpen_inter_preimage isOpen_chartDenSet
  exact isOpen_ne_fun continuous_u6Discriminant continuous_const

theorem chartCoord6_pi6_eq_zero {p : Coord8} (hp : p ∈ chartDenSet) :
    pi6 (chartCoord6 p) = 0 := by
  rw [pi6_eq_r_mul_pf0123_sub]
  apply sub_eq_zero.mpr
  change chartR p * (p 3 - p 0 + 1) = _
  rw [chartR, div_mul_cancel₀]
  · rfl
  · simpa [chartDenSet] using hp

theorem chartCoord6_isU6 (p : U6Chart) : IsU6 (chartCoord6 p.1) := by
  apply isU6_of_pi6_eq_zero_of_discriminant_ne
  · exact chartCoord6_pi6_eq_zero p.2.1
  · exact p.2.2

/-- Inclusion of the graph chart into the original hypersurface subtype. -/
def chartToU6 (p : U6Chart) : U6 :=
  ⟨chartCoord6 p.1, chartCoord6_isU6 p⟩

/-- Forget the dependent ninth coordinate. -/
def dropR (q : Coord6) : Coord8 :=
  ![q.u, q.v, q.s, q.w, q.x, q.t, q.y, q.z]

@[simp] theorem dropR_chartCoord6 (p : Coord8) :
    dropR (chartCoord6 p) = p := by
  funext i
  fin_cases i <;> rfl

theorem chartCoord6_dropR (q : U6) : chartCoord6 (dropR q.1) = q.1 := by
  apply Coord6.ext <;> simp [chartCoord6, dropR]
  change chartR (dropR q.1) = q.1.r
  rw [chartR]
  exact (pi6_eq_zero_iff_r_eq_div q.1 q.2.pf0123_ne).mp q.2.pi_zero |>.symm

theorem dropR_mem_u6ChartSet (q : U6) : dropR q.1 ∈ u6ChartSet := by
  constructor
  · simpa [chartDenSet, dropR, pf0123] using q.2.pf0123_ne
  · change u6Discriminant (chartCoord6 (dropR q.1)) ≠ 0
    rw [chartCoord6_dropR q]
    exact q.2.discriminant_ne

def u6ToChart (q : U6) : U6Chart := ⟨dropR q.1, dropR_mem_u6ChartSet q⟩

/-- The graph parametrization is a genuine equivalence, not merely a choice of
coordinates almost everywhere. -/
def u6ChartEquiv : U6Chart ≃ U6 where
  toFun := chartToU6
  invFun := u6ToChart
  left_inv p := by
    apply Subtype.ext
    exact dropR_chartCoord6 p.1
  right_inv q := by
    apply Subtype.ext
    exact chartCoord6_dropR q

theorem continuous_chartToU6 : Continuous chartToU6 := by
  apply continuous_induced_rng.2
  change Continuous fun p : U6Chart => chartCoord6 p.1
  have hOn : ContinuousOn chartCoord6 u6ChartSet :=
    continuousOn_chartCoord6.mono (fun _ hp => hp.1)
  exact continuousOn_iff_continuous_restrict.mp hOn

theorem continuous_u6ToChart : Continuous u6ToChart := by
  apply continuous_induced_rng.2
  change Continuous fun q : U6 => dropR q.1
  fun_prop [dropR]

/-- Homeomorphism between the open eight-dimensional chart and `U6`. -/
def u6ChartHomeomorph : U6Chart ≃ₜ U6 where
  toEquiv := u6ChartEquiv
  continuous_toFun := continuous_chartToU6
  continuous_invFun := continuous_u6ToChart

/-- A concrete rational point proving that the chart is nonempty. -/
def u6ChartWitness : Coord8
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => 1
  | 5 => 4
  | 6 => 2
  | 7 => 4

theorem u6ChartSet_nonempty : u6ChartSet.Nonempty := by
  refine ⟨u6ChartWitness, ?_⟩
  constructor
  · norm_num [u6ChartWitness, chartDenSet]
  · norm_num [u6ChartWitness, chartCoord6, chartR, u6Discriminant,
      pf0123, pf0124, pf0125, pf0134, pf0135, pf0145, pf0234,
      pf0235, pf0245, pf0345, pf1234, pf1235, pf1245, pf1345,
      pf2345]

/-- The ambient product Gaussian on the eight free coordinates. -/
def coord8Gaussian : Measure Coord8 := standardComplexGaussianPi 8

instance : IsProbabilityMeasure coord8Gaussian := by
  dsimp [coord8Gaussian]
  infer_instance

instance : coord8Gaussian.IsOpenPosMeasure := by
  dsimp [coord8Gaussian]
  infer_instance

def coord8GaussianPresentation : GaussianCoordinatePresentation coord8Gaussian where
  dimension := 8
  coordinates := ContinuousLinearEquiv.refl ℂ Coord8
  measure_eq := by simp [coord8Gaussian]

/-- Probability measure on the open graph chart. -/
def measureU6Chart : Measure U6Chart :=
  normalizedOpenMeasure coord8Gaussian u6ChartSet isOpen_u6ChartSet
    u6ChartSet_nonempty

instance : IsProbabilityMeasure measureU6Chart :=
  normalizedOpenMeasure_isProbability coord8Gaussian u6ChartSet
    isOpen_u6ChartSet u6ChartSet_nonempty

instance : measureU6Chart.IsOpenPosMeasure :=
  normalizedOpenMeasure_isOpenPos coord8Gaussian u6ChartSet
    isOpen_u6ChartSet u6ChartSet_nonempty

/-- The fixed positive smooth probability measure on `U6`. -/
def measureU6 : Measure U6 := Measure.map chartToU6 measureU6Chart

instance : IsProbabilityMeasure measureU6 :=
  Measure.isProbabilityMeasure_map continuous_chartToU6.measurable.aemeasurable

instance : measureU6.IsOpenPosMeasure :=
  continuous_chartToU6.isOpenPosMeasure_map u6ChartEquiv.surjective

/-! ## The six graph-chart face maps are submersions -/

def chartFace5_0 (p : Coord8) : Coord5 := face5Coord0 (chartCoord6 p)
def chartFace5_1 (p : Coord8) : Coord5 := face5Coord1 (chartCoord6 p)
def chartFace5_2 (p : Coord8) : Coord5 := face5Coord2 (chartCoord6 p)
def chartFace5_3 (p : Coord8) : Coord5 := face5Coord3 (chartCoord6 p)
def chartFace5_4 (p : Coord8) : Coord5 := face5Coord4 (chartCoord6 p)
def chartFace5_5 (p : Coord8) : Coord5 := face5Coord5 (chartCoord6 p)

def chartFace5At : Fin 6 → Coord8 → Coord5
  | 0 => chartFace5_0
  | 1 => chartFace5_1
  | 2 => chartFace5_2
  | 3 => chartFace5_3
  | 4 => chartFace5_4
  | 5 => chartFace5_5

@[simp]
theorem chartFace5At_restrict (i : Fin 6) (p : U6Chart) :
    chartFace5At i p.1 = (face5At i (chartToU6 p)).1 := by
  fin_cases i <;> rfl

/-- A differentiable local right inverse makes the derivative onto. -/
theorem hasSurjectiveComplexFDerivAt_of_eventual_section
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : E → F) (x : E) (sec : F → E)
    (hf : DifferentiableAt ℂ f x)
    (hs : DifferentiableAt ℂ sec (f x))
    (hsection : sec (f x) = x)
    (hright : f ∘ sec =ᶠ[nhds (f x)] id) :
    HasSurjectiveComplexFDerivAt f x := by
  refine ⟨hf, ?_⟩
  have hfsection : DifferentiableAt ℂ f (sec (f x)) := by
    rw [hsection]
    exact hf
  have hcomp := fderiv_comp (f x) hfsection hs
  rw [hsection] at hcomp
  have heq : fderiv ℂ (f ∘ sec) (f x) = 1 := by
    rw [hright.fderiv_eq]
    exact fderiv_id
  have hrightDeriv : Function.RightInverse (fderiv ℂ sec (f x))
      (fderiv ℂ f x) := by
    intro v
    have hv := congrArg (fun L : F →L[ℂ] F => L v) (hcomp.symm.trans heq)
    simpa using hv
  exact hrightDeriv.surjective

/-! The last two faces are literal coordinate projections in this chart. -/

def chartFace5Section5 (p : Coord8) (a : Coord5) : Coord8 :=
  ![a.u, a.v, p 2, a.w, a.x, p 5, a.y, p 7]

def chartFace5Section4 (p : Coord8) (a : Coord5) : Coord8 :=
  ![a.u, p 1, a.v, a.w, p 4, a.x, p 6, a.y]

theorem chartFace5_5_section (p : Coord8) (a : Coord5) :
    chartFace5_5 (chartFace5Section5 p a) = a := by
  ext <;> simp [chartFace5_5, chartFace5Section5, face5Coord5,
    chartCoord6]

theorem chartFace5_4_section (p : Coord8) (a : Coord5) :
    chartFace5_4 (chartFace5Section4 p a) = a := by
  ext <;> simp [chartFace5_4, chartFace5Section4, face5Coord4,
    chartCoord6]

theorem chartFace5Section5_at (p : Coord8) :
    chartFace5Section5 p (chartFace5_5 p) = p := by
  funext i
  fin_cases i <;> simp [chartFace5Section5, chartFace5_5, face5Coord5,
    chartCoord6]

theorem chartFace5Section4_at (p : Coord8) :
    chartFace5Section4 p (chartFace5_4 p) = p := by
  funext i
  fin_cases i <;> simp [chartFace5Section4, chartFace5_4, face5Coord4,
    chartCoord6]

theorem differentiableAt_chartFace5_5 (p : U6Chart) :
    DifferentiableAt ℂ chartFace5_5 p.1 := by
  apply differentiableAt_coord5_mk <;>
    simp [chartFace5_5, face5Coord5, chartCoord6] <;> fun_prop

theorem differentiableAt_chartFace5_4 (p : U6Chart) :
    DifferentiableAt ℂ chartFace5_4 p.1 := by
  apply differentiableAt_coord5_mk <;>
    simp [chartFace5_4, face5Coord4, chartCoord6] <;> fun_prop

theorem differentiableAt_chartFace5Section5 (p : Coord8) (a : Coord5) :
    DifferentiableAt ℂ (chartFace5Section5 p) a := by
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;> simp [chartFace5Section5] <;> fun_prop

theorem differentiableAt_chartFace5Section4 (p : Coord8) (a : Coord5) :
    DifferentiableAt ℂ (chartFace5Section4 p) a := by
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;> simp [chartFace5Section4] <;> fun_prop

theorem chartFace5_5_hasSurjectiveComplexFDerivAt (p : U6Chart) :
    HasSurjectiveComplexFDerivAt chartFace5_5 p.1 := by
  apply hasSurjectiveComplexFDerivAt_of_eventual_section
    chartFace5_5 p.1 (chartFace5Section5 p.1)
      (differentiableAt_chartFace5_5 p)
      (differentiableAt_chartFace5Section5 p.1 _)
      (chartFace5Section5_at p.1)
  exact Filter.Eventually.of_forall (chartFace5_5_section p.1)

theorem chartFace5_4_hasSurjectiveComplexFDerivAt (p : U6Chart) :
    HasSurjectiveComplexFDerivAt chartFace5_4 p.1 := by
  apply hasSurjectiveComplexFDerivAt_of_eventual_section
    chartFace5_4 p.1 (chartFace5Section4 p.1)
      (differentiableAt_chartFace5_4 p)
      (differentiableAt_chartFace5Section4 p.1 _)
      (chartFace5Section4_at p.1)
  exact Filter.Eventually.of_forall (chartFace5_4_section p.1)

/-! For face three, keep `u,w,y` fixed and solve linearly for `z`.
The coefficient is the nonzero `p4` of the target five-point chart. -/

def chartFace5Section3Z (p : Coord8) (a : Coord5) : ℂ :=
  (a.y * (p 3 - p 0 + 1) -
      (a.v * p 3 - a.v * a.w + a.v * p 6 - a.x * p 0 +
        a.x * a.u - a.x * p 6 + p 0 * a.w - a.u * p 3 -
        p 6)) /
    (a.w - a.u + 1)

def chartFace5Section3 (p : Coord8) (a : Coord5) : Coord8 :=
  ![p 0, a.u, a.v, p 3, a.w, a.x, p 6, chartFace5Section3Z p a]

theorem chartFace5_3_section (p : Coord8) (a : Coord5)
    (hpden : p 3 - p 0 + 1 ≠ 0) (ha : a.w - a.u + 1 ≠ 0) :
    chartFace5_3 (chartFace5Section3 p a) = a := by
  apply Coord5.ext <;>
    simp [chartFace5_3, chartFace5Section3, face5Coord3, chartCoord6]
  change chartR (chartFace5Section3 p a) = a.y
  simp [chartR, chartFace5Section3, chartFace5Section3Z]
  field_simp [hpden, ha]
  ring

theorem chartFace5Section3_at (p : U6Chart) :
    chartFace5Section3 p.1 (chartFace5_3 p.1) = p.1 := by
  have hpden : p.1 3 - p.1 0 + 1 ≠ 0 := p.2.1
  have hp4 : (chartFace5_3 p.1).w - (chartFace5_3 p.1).u + 1 ≠ 0 := by
    simpa [chartFace5_3, face5Coord3, chartCoord6, pf0124] using
      (chartCoord6_isU6 p).pf0124_ne
  have hp4' : 1 + p.1 4 - p.1 1 ≠ 0 := by
    have h : 1 + p.1 4 - p.1 1 = 1 + (p.1 4 - p.1 1) := by ring
    rw [h]
    simpa [chartFace5_3, face5Coord3, chartCoord6, add_comm] using hp4
  funext i
  fin_cases i <;>
    simp [chartFace5Section3, chartFace5_3, face5Coord3, chartCoord6]
  change
    (chartR p.1 * (p.1 3 - p.1 0 + 1) -
        (p.1 2 * p.1 3 - p.1 2 * p.1 4 + p.1 2 * p.1 6 -
          p.1 5 * p.1 0 + p.1 5 * p.1 1 - p.1 5 * p.1 6 +
          p.1 0 * p.1 4 - p.1 1 * p.1 3 - p.1 6)) /
      (p.1 4 - p.1 1 + 1) = p.1 7
  rw [chartR, div_mul_cancel₀ _ hpden]
  have hp4'' : p.1 4 - p.1 1 + 1 ≠ 0 := by
    intro hzero
    apply hp4'
    calc
      1 + p.1 4 - p.1 1 = p.1 4 - p.1 1 + 1 := by ring
      _ = 0 := hzero
  field_simp [hp4'']
  ring

theorem differentiableAt_chartFace5_3 (p : U6Chart) :
    DifferentiableAt ℂ chartFace5_3 p.1 := by
  apply differentiableAt_coord5_mk <;>
    simp [chartFace5_3, face5Coord3, chartCoord6, chartR] <;>
    fun_prop (disch := exact p.2.1)

theorem differentiableAt_chartFace5Section3 (p : U6Chart) :
    DifferentiableAt ℂ (chartFace5Section3 p.1) (chartFace5_3 p.1) := by
  have hp4 : (chartFace5_3 p.1).w - (chartFace5_3 p.1).u + 1 ≠ 0 := by
    simpa [chartFace5_3, face5Coord3, chartCoord6, pf0124] using
      (chartCoord6_isU6 p).pf0124_ne
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;> simp [chartFace5Section3, chartFace5Section3Z] <;>
    fun_prop (disch := exact hp4)

theorem eventually_chartFace5_3_section (p : U6Chart) :
    chartFace5_3 ∘ chartFace5Section3 p.1 =ᶠ[nhds (chartFace5_3 p.1)] id := by
  have hp4 : (chartFace5_3 p.1).w - (chartFace5_3 p.1).u + 1 ≠ 0 := by
    simpa [chartFace5_3, face5Coord3, chartCoord6, pf0124] using
      (chartCoord6_isU6 p).pf0124_ne
  have hopen : IsOpen {a : Coord5 | a.w - a.u + 1 ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds hp4] with a ha
  exact chartFace5_3_section p.1 a p.2.1 ha

theorem chartFace5_3_hasSurjectiveComplexFDerivAt (p : U6Chart) :
    HasSurjectiveComplexFDerivAt chartFace5_3 p.1 := by
  exact hasSurjectiveComplexFDerivAt_of_eventual_section
    chartFace5_3 p.1 (chartFace5Section3 p.1)
      (differentiableAt_chartFace5_3 p)
      (differentiableAt_chartFace5Section3 p)
      (chartFace5Section3_at p)
      (eventually_chartFace5_3_section p)

/-! For face two, keep `u,w,t` fixed and solve linearly for `x`.
The coefficient is `u` times the nonzero `p3` of the target. -/

def chartFace5Section2X (p : Coord8) (a : Coord5) : ℂ :=
  (a.y * p 0 * (p 3 - p 0 + 1) -
      (a.v * p 0 * p 3 + a.v * p 0 * (a.w * p 0) -
        p 5 * p 0 + p 5 * (a.u * p 0) - p 5 * (a.w * p 0) -
        (a.u * p 0) * p 3 - (a.u * p 0) * (a.x * p 0) -
        a.w * p 0 + a.x * p 0)) /
    (p 0 - a.v * p 0 + a.x * p 0)

def chartFace5Section2 (p : Coord8) (a : Coord5) : Coord8 :=
  ![p 0, a.u * p 0, a.v * p 0, p 3, chartFace5Section2X p a,
    p 5, a.w * p 0, a.x * p 0]

theorem chartFace5_2_section (p : Coord8) (a : Coord5)
    (hu : p 0 ≠ 0) (hpden : p 3 - p 0 + 1 ≠ 0)
    (ha : a.x - a.v + 1 ≠ 0) :
    chartFace5_2 (chartFace5Section2 p a) = a := by
  have hcoef : p 0 - a.v * p 0 + a.x * p 0 ≠ 0 := by
    intro hzero
    apply mul_ne_zero hu ha
    calc
      p 0 * (a.x - a.v + 1) =
          p 0 - a.v * p 0 + a.x * p 0 := by ring
      _ = 0 := hzero
  have ha' : 1 - a.v + a.x ≠ 0 := by
    intro hzero
    apply ha
    calc
      a.x - a.v + 1 = 1 - a.v + a.x := by ring
      _ = 0 := hzero
  apply Coord5.ext <;>
    simp [chartFace5_2, chartFace5Section2, face5Coord2, chartCoord6] <;>
    field_simp [hu]
  simp [chartR, chartFace5Section2, chartFace5Section2X]
  field_simp [hpden, hcoef, ha']
  ring

theorem chartFace5Section2_at (p : U6Chart) :
    chartFace5Section2 p.1 (chartFace5_2 p.1) = p.1 := by
  have hU := chartCoord6_isU6 p
  have hu : p.1 0 ≠ 0 := by simpa [chartCoord6] using hU.u_ne
  have hp3 : (chartFace5_2 p.1).x - (chartFace5_2 p.1).v + 1 ≠ 0 := by
    intro hzero
    apply hU.pf0135_ne
    have hmul : p.1 0 * ((chartFace5_2 p.1).x -
        (chartFace5_2 p.1).v + 1) = p.1 7 - p.1 2 + p.1 0 := by
      simp [chartFace5_2, face5Coord2, chartCoord6]
      field_simp [hu]
    rw [hzero, mul_zero] at hmul
    exact hmul.symm
  have hcoef : p.1 0 - (chartFace5_2 p.1).v * p.1 0 +
      (chartFace5_2 p.1).x * p.1 0 ≠ 0 := by
    intro hzero
    apply mul_ne_zero hu hp3
    calc
      p.1 0 * ((chartFace5_2 p.1).x - (chartFace5_2 p.1).v + 1) =
          p.1 0 - (chartFace5_2 p.1).v * p.1 0 +
            (chartFace5_2 p.1).x * p.1 0 := by ring
      _ = 0 := hzero
  have h0135 : -p.1 2 + p.1 0 + p.1 7 ≠ 0 := by
    intro hzero
    apply hU.pf0135_ne
    calc
      p.1 7 - p.1 2 + p.1 0 = -p.1 2 + p.1 0 + p.1 7 := by ring
      _ = 0 := hzero
  funext i
  fin_cases i
  case «4» =>
    change chartFace5Section2X p.1 (chartFace5_2 p.1) = p.1 4
    unfold chartFace5Section2X
    rw [div_eq_iff hcoef]
    simp [chartFace5_2, face5Coord2, chartCoord6]
    field_simp [hu]
    linear_combination chartR_mul_den p.1 p.2.1
  all_goals
    simp [chartFace5Section2, chartFace5_2, face5Coord2, chartCoord6] <;>
      field_simp [hu, h0135] <;> ring

theorem differentiableAt_chartFace5_2 (p : U6Chart) :
    DifferentiableAt ℂ chartFace5_2 p.1 := by
  have hU := chartCoord6_isU6 p
  apply differentiableAt_coord5_mk <;>
    simp [chartFace5_2, face5Coord2, chartCoord6, chartR] <;>
    fun_prop (disch := first | exact p.2.1 | exact hU.u_ne)

theorem differentiableAt_chartFace5Section2 (p : U6Chart) :
    DifferentiableAt ℂ (chartFace5Section2 p.1) (chartFace5_2 p.1) := by
  have hU := chartCoord6_isU6 p
  have hp3 : (chartFace5_2 p.1).x - (chartFace5_2 p.1).v + 1 ≠ 0 := by
    have hu : p.1 0 ≠ 0 := by simpa [chartCoord6] using hU.u_ne
    intro hzero
    apply hU.pf0135_ne
    have hmul : p.1 0 * ((chartFace5_2 p.1).x -
        (chartFace5_2 p.1).v + 1) = p.1 7 - p.1 2 + p.1 0 := by
      simp [chartFace5_2, face5Coord2, chartCoord6]
      field_simp [hu]
    rw [hzero, mul_zero] at hmul
    exact hmul.symm
  have hcoef : p.1 0 - (chartFace5_2 p.1).v * p.1 0 +
      (chartFace5_2 p.1).x * p.1 0 ≠ 0 := by
    intro hzero
    apply mul_ne_zero hU.u_ne hp3
    calc
      p.1 0 * ((chartFace5_2 p.1).x - (chartFace5_2 p.1).v + 1) =
          p.1 0 - (chartFace5_2 p.1).v * p.1 0 +
            (chartFace5_2 p.1).x * p.1 0 := by ring
      _ = 0 := hzero
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;> simp [chartFace5Section2, chartFace5Section2X] <;>
    fun_prop (disch := exact hcoef)

theorem eventually_chartFace5_2_section (p : U6Chart) :
    chartFace5_2 ∘ chartFace5Section2 p.1 =ᶠ[nhds (chartFace5_2 p.1)] id := by
  have hU := chartCoord6_isU6 p
  have hp3 : (chartFace5_2 p.1).x - (chartFace5_2 p.1).v + 1 ≠ 0 := by
    have hu : p.1 0 ≠ 0 := by simpa [chartCoord6] using hU.u_ne
    intro hzero
    apply hU.pf0135_ne
    have hmul : p.1 0 * ((chartFace5_2 p.1).x -
        (chartFace5_2 p.1).v + 1) = p.1 7 - p.1 2 + p.1 0 := by
      simp [chartFace5_2, face5Coord2, chartCoord6]
      field_simp [hu]
    rw [hzero, mul_zero] at hmul
    exact hmul.symm
  have hopen : IsOpen {a : Coord5 | a.x - a.v + 1 ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds hp3] with a ha
  exact chartFace5_2_section p.1 a hU.u_ne p.2.1 ha

theorem chartFace5_2_hasSurjectiveComplexFDerivAt (p : U6Chart) :
    HasSurjectiveComplexFDerivAt chartFace5_2 p.1 := by
  exact hasSurjectiveComplexFDerivAt_of_eventual_section
    chartFace5_2 p.1 (chartFace5Section2 p.1)
      (differentiableAt_chartFace5_2 p)
      (differentiableAt_chartFace5Section2 p)
      (chartFace5Section2_at p)
      (eventually_chartFace5_2_section p)

/-! For face one, keep `u,s,w` fixed and solve linearly for `v`.
Its coefficient is minus `w` times the target `p3`. -/

def chartFace5Section1V (p : Coord8) (a : Coord5) : ℂ :=
  ((p 2 * p 3 - p 2 * (a.u * p 3) + p 2 * (a.w * p 3) -
        (a.v * p 3) * p 0 - (a.v * p 3) * (a.w * p 3) +
        p 0 * (a.u * p 3) + (a.u * p 3) * (a.x * p 3) -
        a.w * p 3 + a.x * p 3) -
      a.y * p 3 * (p 3 - p 0 + 1)) /
    (p 3 - a.v * p 3 + a.x * p 3)

def chartFace5Section1 (p : Coord8) (a : Coord5) : Coord8 :=
  ![p 0, chartFace5Section1V p a, p 2, p 3, a.u * p 3,
    a.v * p 3, a.w * p 3, a.x * p 3]

theorem chartFace5_1_section (p : Coord8) (a : Coord5)
    (hw : p 3 ≠ 0) (hpden : p 3 - p 0 + 1 ≠ 0)
    (ha : a.x - a.v + 1 ≠ 0) :
    chartFace5_1 (chartFace5Section1 p a) = a := by
  have hcoef : p 3 - a.v * p 3 + a.x * p 3 ≠ 0 := by
    intro hzero
    apply mul_ne_zero hw ha
    calc
      p 3 * (a.x - a.v + 1) =
          p 3 - a.v * p 3 + a.x * p 3 := by ring
      _ = 0 := hzero
  have ha' : 1 - a.v + a.x ≠ 0 := by
    intro hzero
    apply ha
    calc
      a.x - a.v + 1 = 1 - a.v + a.x := by ring
      _ = 0 := hzero
  apply Coord5.ext <;>
    simp [chartFace5_1, chartFace5Section1, face5Coord1, chartCoord6] <;>
    field_simp [hw]
  simp [chartR, chartFace5Section1, chartFace5Section1V]
  field_simp [hpden, hcoef, ha']
  ring

theorem chartFace5Section1_at (p : U6Chart) :
    chartFace5Section1 p.1 (chartFace5_1 p.1) = p.1 := by
  have hU := chartCoord6_isU6 p
  have hw : p.1 3 ≠ 0 := by simpa [chartCoord6] using hU.w_ne
  have hp3 : (chartFace5_1 p.1).x - (chartFace5_1 p.1).v + 1 ≠ 0 := by
    intro hzero
    apply hU.pf0235_ne
    have hmul : p.1 3 * ((chartFace5_1 p.1).x -
        (chartFace5_1 p.1).v + 1) = p.1 7 - p.1 5 + p.1 3 := by
      simp [chartFace5_1, face5Coord1, chartCoord6]
      field_simp [hw]
    rw [hzero, mul_zero] at hmul
    exact hmul.symm
  have hcoef : p.1 3 - (chartFace5_1 p.1).v * p.1 3 +
      (chartFace5_1 p.1).x * p.1 3 ≠ 0 := by
    intro hzero
    apply mul_ne_zero hw hp3
    calc
      p.1 3 * ((chartFace5_1 p.1).x -
          (chartFace5_1 p.1).v + 1) =
          p.1 3 - (chartFace5_1 p.1).v * p.1 3 +
            (chartFace5_1 p.1).x * p.1 3 := by ring
      _ = 0 := hzero
  have h0235 : -p.1 3 + p.1 5 - p.1 7 ≠ 0 := by
    intro hzero
    apply hU.pf0235_ne
    calc
      p.1 7 - p.1 5 + p.1 3 = -(-p.1 3 + p.1 5 - p.1 7) := by ring
      _ = 0 := by rw [hzero, neg_zero]
  funext i
  fin_cases i
  case «1» =>
    change chartFace5Section1V p.1 (chartFace5_1 p.1) = p.1 1
    unfold chartFace5Section1V
    rw [div_eq_iff hcoef]
    simp [chartFace5_1, face5Coord1, chartCoord6]
    field_simp [hw]
    linear_combination -chartR_mul_den p.1 p.2.1
  all_goals
    simp [chartFace5Section1, chartFace5_1, face5Coord1, chartCoord6] <;>
      field_simp [hw, h0235] <;> ring

theorem differentiableAt_chartFace5_1 (p : U6Chart) :
    DifferentiableAt ℂ chartFace5_1 p.1 := by
  have hU := chartCoord6_isU6 p
  apply differentiableAt_coord5_mk <;>
    simp [chartFace5_1, face5Coord1, chartCoord6, chartR] <;>
    fun_prop (disch := first | exact p.2.1 | exact hU.w_ne)

theorem differentiableAt_chartFace5Section1 (p : U6Chart) :
    DifferentiableAt ℂ (chartFace5Section1 p.1) (chartFace5_1 p.1) := by
  have hU := chartCoord6_isU6 p
  have hp3 : (chartFace5_1 p.1).x - (chartFace5_1 p.1).v + 1 ≠ 0 := by
    have hw : p.1 3 ≠ 0 := by simpa [chartCoord6] using hU.w_ne
    intro hzero
    apply hU.pf0235_ne
    have hmul : p.1 3 * ((chartFace5_1 p.1).x -
        (chartFace5_1 p.1).v + 1) = p.1 7 - p.1 5 + p.1 3 := by
      simp [chartFace5_1, face5Coord1, chartCoord6]
      field_simp [hw]
    rw [hzero, mul_zero] at hmul
    exact hmul.symm
  have hcoef : p.1 3 - (chartFace5_1 p.1).v * p.1 3 +
      (chartFace5_1 p.1).x * p.1 3 ≠ 0 := by
    intro hzero
    have hw : p.1 3 ≠ 0 := by simpa [chartCoord6] using hU.w_ne
    apply mul_ne_zero hw hp3
    calc
      p.1 3 * ((chartFace5_1 p.1).x -
          (chartFace5_1 p.1).v + 1) =
          p.1 3 - (chartFace5_1 p.1).v * p.1 3 +
            (chartFace5_1 p.1).x * p.1 3 := by ring
      _ = 0 := hzero
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;> simp [chartFace5Section1, chartFace5Section1V] <;>
    fun_prop (disch := exact hcoef)

theorem eventually_chartFace5_1_section (p : U6Chart) :
    chartFace5_1 ∘ chartFace5Section1 p.1 =ᶠ[nhds (chartFace5_1 p.1)] id := by
  have hU := chartCoord6_isU6 p
  have hp3 : (chartFace5_1 p.1).x - (chartFace5_1 p.1).v + 1 ≠ 0 := by
    have hw : p.1 3 ≠ 0 := by simpa [chartCoord6] using hU.w_ne
    intro hzero
    apply hU.pf0235_ne
    have hmul : p.1 3 * ((chartFace5_1 p.1).x -
        (chartFace5_1 p.1).v + 1) = p.1 7 - p.1 5 + p.1 3 := by
      simp [chartFace5_1, face5Coord1, chartCoord6]
      field_simp [hw]
    rw [hzero, mul_zero] at hmul
    exact hmul.symm
  have hopen : IsOpen {a : Coord5 | a.x - a.v + 1 ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  filter_upwards [hopen.mem_nhds hp3] with a ha
  exact chartFace5_1_section p.1 a hU.w_ne p.2.1 ha

theorem chartFace5_1_hasSurjectiveComplexFDerivAt (p : U6Chart) :
    HasSurjectiveComplexFDerivAt chartFace5_1 p.1 := by
  exact hasSurjectiveComplexFDerivAt_of_eventual_section
    chartFace5_1 p.1 (chartFace5Section1 p.1)
      (differentiableAt_chartFace5_1 p)
      (differentiableAt_chartFace5Section1 p)
      (chartFace5Section1_at p)
      (eventually_chartFace5_1_section p)

/-! For face zero, keep `u,v,s` fixed.  The first four target coordinates
determine `x,t,y,z` once `w` is known.  Substitution in the Pfaffian equation
is linear in `w`, with coefficient `v * s * p0(a)`. -/

def chartFace5Section0Num (p : Coord8) (a : Coord5) : ℂ :=
  -p 0 * p 1 * p4 a + p 0 * p 1 * p 2 * p1 a +
    p 0 * p 2 * p3 a - p 1 * p 2 * p2 a

def chartFace5Section0Den (p : Coord8) (a : Coord5) : ℂ :=
  p 1 * p 2 * p0 a

def chartFace5Section0W (p : Coord8) (a : Coord5) : ℂ :=
  chartFace5Section0Num p a / chartFace5Section0Den p a

def chartFace5Section0 (p : Coord8) (a : Coord5) : Coord8 :=
  let w := chartFace5Section0W p a
  ![p 0, p 1, p 2, w, a.u * p 1 * w / p 0,
    a.v * w * p 2 / p 0, a.w * p 1 * w, a.x * w * p 2]

theorem chartFace5_0_section (p : Coord8) (a : Coord5)
    (hu : p 0 ≠ 0) (hv : p 1 ≠ 0) (hs : p 2 ≠ 0)
    (hw : chartFace5Section0W p a ≠ 0)
    (hchart : chartFace5Section0W p a - p 0 + 1 ≠ 0)
    (hp0 : p0 a ≠ 0) :
    chartFace5_0 (chartFace5Section0 p a) = a := by
  have hden : chartFace5Section0Den p a ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hv hs) hp0
  have hWmul : chartFace5Section0W p a * chartFace5Section0Den p a =
      chartFace5Section0Num p a := by
    rw [chartFace5Section0W, div_mul_cancel₀ _ hden]
  dsimp [chartFace5Section0Den, chartFace5Section0Num,
    p0, p1, p2, p3, p4] at hWmul
  apply Coord5.ext
  case u =>
    simp [chartFace5_0, chartFace5Section0, face5Coord0, chartCoord6]
    field_simp [hu, hv, hw]
  case v =>
    simp [chartFace5_0, chartFace5Section0, face5Coord0, chartCoord6]
    field_simp [hu, hs, hw]
  case w =>
    simp [chartFace5_0, chartFace5Section0, face5Coord0, chartCoord6]
    field_simp [hv, hw]
  case x =>
    simp [chartFace5_0, chartFace5Section0, face5Coord0, chartCoord6]
    field_simp [hs, hw]
  case y =>
    simp [chartFace5_0, chartFace5Section0, face5Coord0, chartCoord6]
    rw [chartR]
    simp
    field_simp [hu, hv, hs, hw, hchart, hp0, hden,
      chartFace5Section0W, chartFace5Section0Den,
      chartFace5Section0Num, p0, p1, p2, p3, p4]
    linear_combination -hWmul

theorem chartFace5Section0W_at (p : U6Chart) :
    chartFace5Section0W p.1 (chartFace5_0 p.1) = p.1 3 := by
  have hU := chartCoord6_isU6 p
  have hu : p.1 0 ≠ 0 := by simpa [chartCoord6] using hU.u_ne
  have hv : p.1 1 ≠ 0 := by simpa [chartCoord6] using hU.v_ne
  have hs : p.1 2 ≠ 0 := by simpa [chartCoord6] using hU.s_ne
  have hw : p.1 3 ≠ 0 := by simpa [chartCoord6] using hU.w_ne
  have htarget : IsU5 (chartFace5_0 p.1) := by
    change IsU5 (face5Coord0 (chartToU6 p).1)
    exact face5Coord0_mem (chartToU6 p)
  have hden : chartFace5Section0Den p.1 (chartFace5_0 p.1) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hv hs) htarget.p0_ne
  unfold chartFace5Section0W
  rw [div_eq_iff hden]
  simp [chartFace5_0, face5Coord0, chartCoord6,
    chartFace5Section0Num, chartFace5Section0Den, p0, p1, p2, p3, p4]
  field_simp [hu, hv, hs, hw]
  linear_combination -chartR_mul_den p.1 p.2.1

theorem chartFace5Section0_at (p : U6Chart) :
    chartFace5Section0 p.1 (chartFace5_0 p.1) = p.1 := by
  have hU := chartCoord6_isU6 p
  have hu : p.1 0 ≠ 0 := by simpa [chartCoord6] using hU.u_ne
  have hv : p.1 1 ≠ 0 := by simpa [chartCoord6] using hU.v_ne
  have hs : p.1 2 ≠ 0 := by simpa [chartCoord6] using hU.s_ne
  have hw : p.1 3 ≠ 0 := by simpa [chartCoord6] using hU.w_ne
  have hWat := chartFace5Section0W_at p
  funext i
  fin_cases i <;>
    simp [chartFace5Section0, hWat] <;>
    simp [chartFace5_0, face5Coord0, chartCoord6] <;>
    field_simp [hu, hv, hs, hw] <;> ring

theorem differentiableAt_chartFace5_0 (p : U6Chart) :
    DifferentiableAt ℂ chartFace5_0 p.1 := by
  have hU := chartCoord6_isU6 p
  have hvw : p.1 1 * p.1 3 ≠ 0 := mul_ne_zero hU.v_ne hU.w_ne
  have hws : p.1 3 * p.1 2 ≠ 0 := mul_ne_zero hU.w_ne hU.s_ne
  have hvws : p.1 1 * p.1 3 * p.1 2 ≠ 0 :=
    mul_ne_zero hvw hU.s_ne
  apply differentiableAt_coord5_mk <;>
    simp [chartFace5_0, face5Coord0, chartCoord6, chartR] <;>
    fun_prop (disch := first
      | exact p.2.1
      | exact hvw
      | exact hws
      | exact hvws
      | exact hU.u_ne
      | exact hU.v_ne
      | exact hU.s_ne
      | exact hU.w_ne)

theorem differentiableAt_chartFace5Section0 (p : U6Chart) :
    DifferentiableAt ℂ (chartFace5Section0 p.1) (chartFace5_0 p.1) := by
  have hU := chartCoord6_isU6 p
  have htarget : IsU5 (chartFace5_0 p.1) := by
    change IsU5 (face5Coord0 (chartToU6 p).1)
    exact face5Coord0_mem (chartToU6 p)
  have hden : chartFace5Section0Den p.1 (chartFace5_0 p.1) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hU.v_ne hU.s_ne) htarget.p0_ne
  have hW : DifferentiableAt ℂ (chartFace5Section0W p.1)
      (chartFace5_0 p.1) := by
    fun_prop [chartFace5Section0W, chartFace5Section0Num,
      chartFace5Section0Den, p0, p1, p2, p3, p4]
  rw [differentiableAt_pi]
  intro i
  fin_cases i <;> simp [chartFace5Section0] <;>
    fun_prop (disch := first | exact hU.u_ne | exact hW)

def chartFace5Section0ChartNum (p : Coord8) (a : Coord5) : ℂ :=
  chartFace5Section0Num p a +
    (1 - p 0) * chartFace5Section0Den p a

theorem chartFace5Section0_chartDen (p : Coord8) (a : Coord5)
    (hden : chartFace5Section0Den p a ≠ 0) :
    chartFace5Section0W p a - p 0 + 1 =
      chartFace5Section0ChartNum p a / chartFace5Section0Den p a := by
  rw [chartFace5Section0W]
  unfold chartFace5Section0ChartNum
  field_simp [hden]
  ring

theorem eventually_chartFace5_0_section (p : U6Chart) :
    chartFace5_0 ∘ chartFace5Section0 p.1 =ᶠ[nhds (chartFace5_0 p.1)] id := by
  have hU := chartCoord6_isU6 p
  have hu : p.1 0 ≠ 0 := by simpa [chartCoord6] using hU.u_ne
  have hv : p.1 1 ≠ 0 := by simpa [chartCoord6] using hU.v_ne
  have hs : p.1 2 ≠ 0 := by simpa [chartCoord6] using hU.s_ne
  have hw : p.1 3 ≠ 0 := by simpa [chartCoord6] using hU.w_ne
  have htarget : IsU5 (chartFace5_0 p.1) := by
    change IsU5 (face5Coord0 (chartToU6 p).1)
    exact face5Coord0_mem (chartToU6 p)
  have hden0 : chartFace5Section0Den p.1 (chartFace5_0 p.1) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hv hs) htarget.p0_ne
  have hnum0 : chartFace5Section0Num p.1 (chartFace5_0 p.1) ≠ 0 := by
    intro hzero
    apply hw
    rw [← chartFace5Section0W_at p, chartFace5Section0W, hzero,
      zero_div]
  have hchart0 : chartFace5Section0W p.1 (chartFace5_0 p.1) -
      p.1 0 + 1 ≠ 0 := by
    rw [chartFace5Section0W_at p]
    exact p.2.1
  have hchartNum0 :
      chartFace5Section0ChartNum p.1 (chartFace5_0 p.1) ≠ 0 := by
    intro hzero
    apply hchart0
    rw [chartFace5Section0_chartDen p.1 _ hden0, hzero, zero_div]
  have hopen0 : IsOpen {a : Coord5 | p0 a ≠ 0} :=
    isOpen_ne_fun continuous_p0 continuous_const
  have hopenNum :
      IsOpen {a : Coord5 | chartFace5Section0Num p.1 a ≠ 0} :=
    isOpen_ne_fun
      (by fun_prop [chartFace5Section0Num, p1, p2, p3, p4])
      continuous_const
  have hopenChart :
      IsOpen {a : Coord5 | chartFace5Section0ChartNum p.1 a ≠ 0} :=
    isOpen_ne_fun
      (by fun_prop [chartFace5Section0ChartNum, chartFace5Section0Num,
        chartFace5Section0Den, p0, p1, p2, p3, p4])
      continuous_const
  filter_upwards [hopen0.mem_nhds htarget.p0_ne,
      hopenNum.mem_nhds hnum0, hopenChart.mem_nhds hchartNum0]
      with a ha0 hnum hchartNum
  have hden : chartFace5Section0Den p.1 a ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hv hs) ha0
  have hW : chartFace5Section0W p.1 a ≠ 0 := by
    exact div_ne_zero hnum hden
  have hchart : chartFace5Section0W p.1 a - p.1 0 + 1 ≠ 0 := by
    rw [chartFace5Section0_chartDen p.1 a hden]
    exact div_ne_zero hchartNum hden
  exact chartFace5_0_section p.1 a hu hv hs hW hchart ha0

theorem chartFace5_0_hasSurjectiveComplexFDerivAt (p : U6Chart) :
    HasSurjectiveComplexFDerivAt chartFace5_0 p.1 := by
  exact hasSurjectiveComplexFDerivAt_of_eventual_section
    chartFace5_0 p.1 (chartFace5Section0 p.1)
      (differentiableAt_chartFace5_0 p)
      (differentiableAt_chartFace5Section0 p)
      (chartFace5Section0_at p)
      (eventually_chartFace5_0_section p)

/-! ## Coarea and transport back to the Pfaffian hypersurface -/

theorem chartFace5At_mem (i : Fin 6) (x : Coord8) (hx : x ∈ u6ChartSet) :
    chartFace5At i x ∈ u5Set := by
  let p : U6Chart := ⟨x, hx⟩
  change IsU5 (chartFace5At i p.1)
  rw [chartFace5At_restrict i p]
  exact (face5At i (chartToU6 p)).2

theorem chartFace5At_hasSurjectiveComplexFDerivAt
    (i : Fin 6) (p : U6Chart) :
    HasSurjectiveComplexFDerivAt (chartFace5At i) p.1 := by
  fin_cases i
  · exact chartFace5_0_hasSurjectiveComplexFDerivAt p
  · exact chartFace5_1_hasSurjectiveComplexFDerivAt p
  · exact chartFace5_2_hasSurjectiveComplexFDerivAt p
  · exact chartFace5_3_hasSurjectiveComplexFDerivAt p
  · exact chartFace5_4_hasSurjectiveComplexFDerivAt p
  · exact chartFace5_5_hasSurjectiveComplexFDerivAt p

def chartFace5Map (i : Fin 6) (p : U6Chart) : U5 :=
  ⟨chartFace5At i p.1, chartFace5At_mem i p.1 p.2⟩

/-- Coarea applied only after all six rational rank computations have been
checked in Lean. -/
theorem chartFace5Map_quasiMeasurePreserving (i : Fin 6) :
    Measure.QuasiMeasurePreserving (chartFace5Map i)
      measureU6Chart measureU5 := by
  have h := quasiMeasurePreserving_normalizedOpenGaussian_of_submersion
    coord8Gaussian coord5Gaussian
    coord8GaussianPresentation coord5GaussianPresentation
    u6ChartSet isOpen_u6ChartSet u6ChartSet_nonempty
    u5Set isOpen_u5Set u5Set_nonempty
    (chartFace5At i)
    (chartFace5At_mem i)
    (by
      intro x hx
      exact chartFace5At_hasSurjectiveComplexFDerivAt i ⟨x, hx⟩)
  change Measure.QuasiMeasurePreserving
    (fun x : U6Chart =>
      ⟨chartFace5At i x.1, chartFace5At_mem i x.1 x.2⟩)
    (normalizedOpenMeasure coord8Gaussian u6ChartSet
      isOpen_u6ChartSet u6ChartSet_nonempty)
    (normalizedOpenMeasure coord5Gaussian u5Set
      isOpen_u5Set u5Set_nonempty)
  exact h

theorem u6ToChart_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving u6ToChart measureU6 measureU6Chart := by
  refine ⟨continuous_u6ToChart.measurable, ?_⟩
  rw [measureU6, Measure.map_map continuous_u6ToChart.measurable
    continuous_chartToU6.measurable]
  have hcomp : u6ToChart ∘ chartToU6 = id := by
    funext p
    exact u6ChartEquiv.left_inv p
  rw [hcomp, Measure.map_id]

theorem chartFace5Map_comp_u6ToChart (i : Fin 6) :
    chartFace5Map i ∘ u6ToChart = face5At i := by
  funext q
  apply Subtype.ext
  change chartFace5At i (u6ToChart q).1 = (face5At i q).1
  rw [chartFace5At_restrict i (u6ToChart q)]
  have hright : chartToU6 (u6ToChart q) = q := u6ChartEquiv.right_inv q
  rw [hright]

theorem face5At_quasiMeasurePreserving (i : Fin 6) :
    Measure.QuasiMeasurePreserving (face5At i) measureU6 measureU5 := by
  have h := (chartFace5Map_quasiMeasurePreserving i).comp
    u6ToChart_quasiMeasurePreserving
  rw [chartFace5Map_comp_u6ToChart i] at h
  exact h

/-- The concrete six-face nonsingularity package used by the measurable and
bounded Pfaffian complexes. -/
theorem concreteFace5QuasiMeasurePreserving :
    Face5QuasiMeasurePreserving measureU5 measureU6 where
  face0 := face5At_quasiMeasurePreserving 0
  face1 := face5At_quasiMeasurePreserving 1
  face2 := face5At_quasiMeasurePreserving 2
  face3 := face5At_quasiMeasurePreserving 3
  face4 := face5At_quasiMeasurePreserving 4
  face5 := face5At_quasiMeasurePreserving 5

end
end Pfaffian
end Sp4
