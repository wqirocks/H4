import Sp4.Chains.TwoCone
import Sp4.Pfaffian.Certificates

namespace Sp4
namespace Pfaffian

noncomputable section

open Filter Topology
open scoped Topology

/-- The four-block period on the fixed line `B = 3`. -/
def fixedPeriod (A : ℂ) : ℂ := fixedQ1 A + fixedQ2 A + fixedQ3 A + fixedQ4 A

def poleH1 (A : ℂ) : ℂ :=
  poleS1 A /
    (750 * (A + 2) ^ 2 * (A ^ 2 - 8) * (3 * A ^ 2 + 4) ^ 2 *
      (9 * A ^ 2 - 8))

def poleH2 (A : ℂ) : ℂ :=
  poleS2 A /
    (90 * (2 * A - 1) ^ 2 * (8 * A + 9) ^ 2 * (9 * A + 10) ^ 2 *
      (9 * A ^ 2 - 8) * (10 * A ^ 2 - 9))

/-- The continuous extension of `(A-2)` times the period after subtracting
its second-order principal part. -/
def poleRemainderExtension (A : ℂ) : ℂ :=
  poleH1 A + poleH2 A + (A - 2) * fixedQ3 A + (A - 2) * fixedQ4 A

theorem poleH1_continuousAt_two : ContinuousAt poleH1 2 := by
  unfold poleH1 poleS1
  fun_prop (disch := norm_num)

theorem poleH2_continuousAt_two : ContinuousAt poleH2 2 := by
  unfold poleH2 poleS2
  fun_prop (disch := norm_num)

theorem poleRemainderExtension_continuousAt_two :
    ContinuousAt poleRemainderExtension 2 := by
  unfold poleRemainderExtension
  exact (((poleH1_continuousAt_two.add poleH2_continuousAt_two).add
    ((continuousAt_id.sub continuousAt_const).mul fixedQ3_continuousAt_two)).add
      ((continuousAt_id.sub continuousAt_const).mul fixedQ4_continuousAt_two))

theorem fixedPeriod_remainder_eq (A : ℂ)
    (hA2 : A - 2 ≠ 0) (hAp2 : A + 2 ≠ 0) (h8 : A ^ 2 - 8 ≠ 0)
    (h34 : 3 * A ^ 2 + 4 ≠ 0) (h38 : 3 * A ^ 2 + 8 ≠ 0)
    (h98 : 9 * A ^ 2 - 8 ≠ 0) (h21 : 2 * A - 1 ≠ 0)
    (h89 : 8 * A + 9 ≠ 0) (h910 : 9 * A + 10 ≠ 0)
    (h109 : 10 * A ^ 2 - 9 ≠ 0) (h9A : 9 * A ^ 2 - A - 9 ≠ 0) :
    (A - 2) * (fixedPeriod A - 22 / (45 * (A - 2) ^ 2)) =
      poleRemainderExtension A := by
  have hq1 := fixedQ1_eq_closed A hA2 hAp2 h8 h34 h38 h98
  have hq2 := fixedQ2_eq_closed A hA2 h21 h89 h910 h98 h109 h9A
  have hp1 := fixedQ1_principal_part A hA2 hAp2 h8 h34 h98
  have hp2 := fixedQ2_principal_part A hA2 h21 h89 h910 h98 h109
  rw [← hq1] at hp1
  rw [← hq2] at hp2
  have hp1' : (A - 2) ^ 2 * fixedQ1 A + 1 / 10 = (A - 2) * poleH1 A := by
    simpa [poleH1, div_eq_mul_inv, mul_assoc] using hp1
  have hp2' : (A - 2) ^ 2 * fixedQ2 A - 53 / 90 = (A - 2) * poleH2 A := by
    simpa [poleH2, div_eq_mul_inv, mul_assoc] using hp2
  have hprincipal :
      (A - 2) ^ 2 * (fixedQ1 A + fixedQ2 A) - 22 / 45 =
        (A - 2) * (poleH1 A + poleH2 A) := by
    linear_combination hp1' + hp2'
  unfold fixedPeriod poleRemainderExtension
  apply mul_left_cancel₀ hA2
  calc
    (A - 2) * ((A - 2) *
        (fixedQ1 A + fixedQ2 A + fixedQ3 A + fixedQ4 A -
          22 / (45 * (A - 2) ^ 2))) =
        ((A - 2) ^ 2 * (fixedQ1 A + fixedQ2 A) - 22 / 45) +
          (A - 2) ^ 2 * (fixedQ3 A + fixedQ4 A) := by
            field_simp [hA2]
            ring
    _ = (A - 2) * (poleH1 A + poleH2 A) +
          (A - 2) ^ 2 * (fixedQ3 A + fixedQ4 A) := by rw [hprincipal]
    _ = (A - 2) *
        (poleH1 A + poleH2 A + (A - 2) * fixedQ3 A +
          (A - 2) * fixedQ4 A) := by ring

private theorem eventually_ne_zero_at_two (f : ℂ → ℂ)
    (hf : ContinuousAt f 2) (h2 : f 2 ≠ 0) :
    ∀ᶠ A in 𝓝[≠] (2 : ℂ), f A ≠ 0 :=
  (hf.eventually_ne h2).filter_mono inf_le_left

theorem eventually_fixedPeriod_remainder_eq :
    ∀ᶠ A in 𝓝[≠] (2 : ℂ),
      (A - 2) * (fixedPeriod A - 22 / (45 * (A - 2) ^ 2)) =
        poleRemainderExtension A := by
  have hA2 : ∀ᶠ A in 𝓝[≠] (2 : ℂ), A - 2 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with A hA
    exact sub_ne_zero.mpr hA
  have hAp2 := eventually_ne_zero_at_two (fun A : ℂ => A + 2) (by fun_prop) (by norm_num)
  have h8 := eventually_ne_zero_at_two (fun A : ℂ => A ^ 2 - 8) (by fun_prop) (by norm_num)
  have h34 := eventually_ne_zero_at_two (fun A : ℂ => 3 * A ^ 2 + 4) (by fun_prop) (by norm_num)
  have h38 := eventually_ne_zero_at_two (fun A : ℂ => 3 * A ^ 2 + 8) (by fun_prop) (by norm_num)
  have h98 := eventually_ne_zero_at_two (fun A : ℂ => 9 * A ^ 2 - 8) (by fun_prop) (by norm_num)
  have h21 := eventually_ne_zero_at_two (fun A : ℂ => 2 * A - 1) (by fun_prop) (by norm_num)
  have h89 := eventually_ne_zero_at_two (fun A : ℂ => 8 * A + 9) (by fun_prop) (by norm_num)
  have h910 := eventually_ne_zero_at_two (fun A : ℂ => 9 * A + 10) (by fun_prop) (by norm_num)
  have h109 := eventually_ne_zero_at_two (fun A : ℂ => 10 * A ^ 2 - 9) (by fun_prop) (by norm_num)
  have h9A := eventually_ne_zero_at_two (fun A : ℂ => 9 * A ^ 2 - A - 9)
    (by fun_prop) (by norm_num)
  filter_upwards [hA2, hAp2, h8, h34, h38, h98, h21, h89, h910, h109, h9A]
    with A hA2 hAp2 h8 h34 h38 h98 h21 h89 h910 h109 h9A
  exact fixedPeriod_remainder_eq A hA2 hAp2 h8 h34 h38 h98 h21 h89 h910 h109 h9A

theorem poleRemainderExtension_locally_bounded :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧
      ∀ A : ℂ, ‖A - 2‖ < δ → ‖poleRemainderExtension A‖ ≤ M := by
  let M : ℝ := ‖poleRemainderExtension 2‖ + 1
  have hM : 0 < M := by
    dsimp [M]
    positivity
  have hev : ∀ᶠ A in 𝓝 (2 : ℂ),
      dist (poleRemainderExtension A) (poleRemainderExtension 2) < 1 :=
    poleRemainderExtension_continuousAt_two
      (Metric.ball_mem_nhds _ (by norm_num))
  rcases Metric.eventually_nhds_iff.mp hev with ⟨δ, hδ, hball⟩
  refine ⟨δ, M, hδ, hM, fun A hA => ?_⟩
  have hclose := hball (show dist A (2 : ℂ) < δ by simpa [dist_eq_norm] using hA)
  apply le_of_lt
  calc
    ‖poleRemainderExtension A‖ =
        ‖(poleRemainderExtension A - poleRemainderExtension 2) +
          poleRemainderExtension 2‖ := by ring_nf
    _ ≤ ‖poleRemainderExtension A - poleRemainderExtension 2‖ +
        ‖poleRemainderExtension 2‖ := norm_add_le _ _
    _ < 1 + ‖poleRemainderExtension 2‖ := by
      simpa [dist_eq_norm] using add_lt_add_right hclose ‖poleRemainderExtension 2‖
    _ = M := by simp [M, add_comm]

/-- Fully quantified analytic pole estimate.  Genericity of the associated
finite cycle is added separately, so this statement has no hidden domain
assumption. -/
theorem fixedPeriod_quantified_pole :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧
      ∀ A : ℂ, 0 < ‖A - 2‖ → ‖A - 2‖ < δ →
        ‖fixedPeriod A - 22 / (45 * (A - 2) ^ 2)‖ ≤ M / ‖A - 2‖ := by
  obtain ⟨δb, M, hδb, hM, hb⟩ := poleRemainderExtension_locally_bounded
  rcases Metric.mem_nhdsWithin_iff.mp eventually_fixedPeriod_remainder_eq with
    ⟨δe, hδe, heq⟩
  let δ := min δb δe
  have hδ : 0 < δ := lt_min hδb hδe
  refine ⟨δ, M, hδ, hM, fun A hpos hlt => ?_⟩
  have hltb : ‖A - 2‖ < δb := hlt.trans_le (min_le_left _ _)
  have hlte : ‖A - 2‖ < δe := hlt.trans_le (min_le_right _ _)
  have hne : A ≠ 2 := sub_ne_zero.mp (norm_pos_iff.mp hpos)
  have hEq : (A - 2) * (fixedPeriod A - 22 / (45 * (A - 2) ^ 2)) =
      poleRemainderExtension A := by
    apply heq
    constructor
    · simpa [Metric.mem_ball, dist_eq_norm] using hlte
    · simpa using hne
  apply (le_div_iff₀ hpos).2
  rw [mul_comm, ← norm_mul, hEq]
  exact hb A hltb

theorem exists_pole_direction (ell : ℂ →ₗ[ℝ] ℝ) (hell : ell ≠ 0) :
    ∃ η : ℂ, η ≠ 0 ∧ ell (1 / η ^ 2) ≠ 0 := by
  by_cases h1 : ell 1 ≠ 0
  · exact ⟨1, one_ne_zero, by simpa using h1⟩
  have h1z : ell 1 = 0 := not_ne_iff.mp h1
  have hI : ell Complex.I ≠ 0 := by
    intro hIz
    apply hell
    ext z
    have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
      apply Complex.ext <;> simp
    rw [hz, map_add, map_smul, map_smul, h1z, hIz]
    simp
  let η : ℂ := 1 + Complex.I
  have hη : η ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp [η] at hi
  have hval : (1 / η ^ 2 : ℂ) = (-1 / 2 : ℝ) • Complex.I := by
    apply Complex.ext <;> norm_num [η, Complex.div_re, Complex.div_im,
      Complex.normSq_apply, pow_two]
  refine ⟨η, hη, ?_⟩
  rw [hval, map_smul]
  exact smul_ne_zero (by norm_num) hI

theorem realLinearMap_norm_le (ell : ℂ →ₗ[ℝ] ℝ) (z : ℂ) :
    |ell z| ≤ ‖LinearMap.toContinuousLinearMap ell‖ * ‖z‖ := by
  simpa [Real.norm_eq_abs] using (LinearMap.toContinuousLinearMap ell).le_opNorm z

/-- After multiplication by the square of the local parameter, the fixed-line
period has the nonzero limit `22 / 45` on the punctured neighborhood of `2`. -/
theorem fixedPeriod_scaled_tendsto :
    Tendsto (fun A : ℂ => (A - 2) ^ 2 * fixedPeriod A)
      (𝓝[≠] (2 : ℂ)) (𝓝 (22 / 45 : ℂ)) := by
  have hs : Tendsto (fun A : ℂ => A - 2)
      (𝓝[≠] (2 : ℂ)) (𝓝 0) := by
    simpa using
      ((show ContinuousAt (fun A : ℂ => A - 2) 2 by fun_prop).mono_left
        (show 𝓝[≠] (2 : ℂ) ≤ 𝓝 (2 : ℂ) from inf_le_left))
  have hext : Tendsto poleRemainderExtension
      (𝓝[≠] (2 : ℂ)) (𝓝 (poleRemainderExtension 2)) :=
    poleRemainderExtension_continuousAt_two.mono_left inf_le_left
  have hmodel : Tendsto
      (fun A : ℂ => (A - 2) * poleRemainderExtension A + 22 / 45)
      (𝓝[≠] (2 : ℂ)) (𝓝 (22 / 45 : ℂ)) := by
    convert (hs.mul hext).add tendsto_const_nhds using 1 <;> norm_num
  apply hmodel.congr'
  filter_upwards [eventually_fixedPeriod_remainder_eq, self_mem_nhdsWithin]
    with A hEq hA
  have hA' : A ≠ 2 := by simpa using hA
  have hsA : A - 2 ≠ 0 := sub_ne_zero.mpr hA'
  rw [← hEq]
  field_simp [hsA]
  ring

/-- A real ray approaching `2` through the nonzero complex direction `η`. -/
def poleRay (η : ℂ) (r : ℝ) : ℂ := 2 + (r : ℂ) * η

theorem poleRay_tendsto (η : ℂ) (hη : η ≠ 0) :
    Tendsto (poleRay η) (𝓝[>] (0 : ℝ)) (𝓝[≠] (2 : ℂ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hr : Tendsto (fun r : ℝ => (r : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using
        ((show ContinuousAt (fun r : ℝ => (r : ℂ)) 0 by fun_prop).mono_left
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left))
    change Tendsto (fun r : ℝ => (2 : ℂ) + (r : ℂ) * η)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℂ))
    convert tendsto_const_nhds.add (hr.mul_const η) using 1 <;> norm_num
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    simp [poleRay, hr0, hη]

theorem poleRay_scaled_identity (η : ℂ) (hη : η ≠ 0) (r : ℝ) (z : ℂ) :
    (1 / η ^ 2) * ((poleRay η r - 2) ^ 2 * z) = (r ^ 2 : ℝ) • z := by
  change (1 / η ^ 2) * (((2 : ℂ) + (r : ℂ) * η - 2) ^ 2 * z) =
    ((r ^ 2 : ℝ) : ℂ) * z
  field_simp [hη]
  push_cast
  ring

theorem realComponent_scaled_along_poleRay_tendsto
    (ell : ℂ →ₗ[ℝ] ℝ) (η : ℂ) (hη : η ≠ 0) :
    Tendsto (fun r : ℝ => r ^ 2 * ell (fixedPeriod (poleRay η r)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (ell ((1 / η ^ 2) * (22 / 45 : ℂ)))) := by
  have hp := fixedPeriod_scaled_tendsto.comp (poleRay_tendsto η hη)
  let E : ℂ →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ell
  have hmap : ContinuousAt (fun z : ℂ => E ((1 / η ^ 2) * z))
      (22 / 45 : ℂ) := by
    fun_prop
  have hlim : Tendsto
      ((fun z : ℂ => E ((1 / η ^ 2) * z)) ∘
        (fun r : ℝ => (poleRay η r - 2) ^ 2 * fixedPeriod (poleRay η r)))
      (𝓝[>] (0 : ℝ))
      (𝓝 (E ((1 / η ^ 2) * (22 / 45 : ℂ)))) :=
    Filter.Tendsto.comp hmap hp
  apply hlim.congr'
  filter_upwards with r
  change ell ((1 / η ^ 2) *
      ((poleRay η r - 2) ^ 2 * fixedPeriod (poleRay η r))) =
    r ^ 2 * ell (fixedPeriod (poleRay η r))
  rw [poleRay_scaled_identity η hη r]
  rw [map_smul]
  rfl

theorem realComponent_pole_limit_ne_zero
    (ell : ℂ →ₗ[ℝ] ℝ) (η : ℂ)
    (hdir : ell (1 / η ^ 2) ≠ 0) :
    ell ((1 / η ^ 2) * (22 / 45 : ℂ)) ≠ 0 := by
  have hscalar : (1 / η ^ 2) * (22 / 45 : ℂ) =
      (22 / 45 : ℝ) • (1 / η ^ 2) := by
    norm_num [smul_eq_mul]
    ring
  rw [hscalar, map_smul]
  exact mul_ne_zero (by norm_num) hdir

/-- Every nonzero real-linear scalar component of the fixed-line period is
unbounded in every punctured neighborhood of the pole. -/
theorem realComponent_not_locally_bounded
    (ell : ℂ →ₗ[ℝ] ℝ) (hell : ell ≠ 0) :
    ¬ ∃ C : ℝ, ∀ᶠ A in 𝓝[≠] (2 : ℂ), |ell (fixedPeriod A)| ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨η, hη, hdir⟩ := exists_pole_direction ell hell
  have hlim := realComponent_scaled_along_poleRay_tendsto ell η hη
  have hlim_ne : ell ((1 / η ^ 2) * (22 / 45 : ℂ)) ≠ 0 :=
    realComponent_pole_limit_ne_zero ell η hdir
  have hbpath : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      |ell (fixedPeriod (poleRay η r))| ≤ C :=
    (poleRay_tendsto η hη).eventually hC
  have hle : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ‖r ^ 2 * ell (fixedPeriod (poleRay η r))‖ ≤ r ^ 2 * |C| := by
    filter_upwards [hbpath] with r hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg r)]
    exact mul_le_mul_of_nonneg_left (hr.trans (le_abs_self C)) (sq_nonneg r)
  have hr0 : Tendsto (fun r : ℝ => r) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    exact tendsto_id.mono_left inf_le_left
  have hmajorant : Tendsto (fun r : ℝ => r ^ 2 * |C|)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert (hr0.pow 2).mul_const |C| using 1 <;> simp
  have hnormzero : Tendsto
      (fun r : ℝ => ‖r ^ 2 * ell (fixedPeriod (poleRay η r))‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hle hmajorant
  have hzero : Tendsto
      (fun r : ℝ => r ^ 2 * ell (fixedPeriod (poleRay η r)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnormzero
  exact hlim_ne (tendsto_nhds_unique hlim hzero)

/-- The eight elementary correspondences occurring along the paper's fixed
line all have nonzero discriminant. -/
structure FixedLineAdmissible (A : ℂ) : Prop where
  edge_one : deltaU (A ^ 2) 3 ≠ 0
  edge_two : deltaU (-3 * A ^ 2) 3 ≠ 0
  edge_three : deltaU (-1 / 9) A ≠ 0
  edge_four : deltaU (A / 9) A ≠ 0
  edge_five : deltaU (-(1 / A ^ 2)) (Complex.I / 3) ≠ 0
  edge_six : deltaU (Complex.I / (3 * A ^ 2)) (Complex.I / 3) ≠ 0
  edge_seven : deltaU 9 (Complex.I / A) ≠ 0
  edge_eight : deltaU (-9 * Complex.I / A) (Complex.I / A) ≠ 0

/-- The fixed-line certificate supplies exactly the eight hypotheses used by
the general period cycle. -/
def FixedLineAdmissible.toPeriodCycleAdmissible {A : ℂ}
    (h : FixedLineAdmissible A) : OrbitChain.PeriodCycleAdmissible A 3 where
  edge_one := h.edge_one
  edge_two := by
    convert h.edge_two using 1 <;> ring
  edge_three := by
    convert h.edge_three using 1 <;> norm_num
  edge_four := by
    convert h.edge_four using 1 <;> norm_num
  edge_five := h.edge_five
  edge_six := by
    convert h.edge_six using 1 <;> ring
  edge_seven := by
    convert h.edge_seven using 1 <;> norm_num
  edge_eight := by
    rw [show (3 : ℂ) ^ 2 = 9 by norm_num]
    simpa [neg_div, mul_assoc] using h.edge_eight

/-- On the fixed line, the chain-level period is the rational function whose
pole is computed below. -/
theorem periodCycleValue_fixedLine (A : ℂ) (h : FixedLineAdmissible A) :
    OrbitChain.periodCycleValue A 3 h.toPeriodCycleAdmissible = fixedPeriod A := by
  rw [OrbitChain.periodCycleValue_eq]
  norm_num [fixedPeriod, fixedQ1, fixedQ2, fixedQ3, fixedQ4]

/-- The fixed-line cycle is a genuine cycle of quotient mass at most sixteen. -/
theorem fixedLine_periodCycle_certificate (A : ℂ) (h : FixedLineAdmissible A) :
    OrbitChain.boundary ℝ 4
        (OrbitChain.periodCycle A 3 h.toPeriodCycleAdmissible) = 0 ∧
      OrbitChain.quotientL1
        (OrbitChain.periodCycle A 3 h.toPeriodCycleAdmissible) ≤ 16 := by
  exact ⟨OrbitChain.boundary_periodCycle A 3 _,
    OrbitChain.quotientL1_periodCycle_le_sixteen A 3 _⟩

theorem eventually_fixedLineAdmissible :
    ∀ᶠ A in 𝓝[≠] (2 : ℂ), FixedLineAdmissible A := by
  have hA2 : ∀ᶠ A in 𝓝[≠] (2 : ℂ), A - 2 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with A hA
    exact sub_ne_zero.mpr (by simpa using hA)
  have hg1 := eventually_ne_zero_at_two
    (fun A : ℂ => A ^ 2 * (A + 2) * (A ^ 2 - 8) * (3 * A ^ 2 + 8))
    (by fun_prop) (by norm_num)
  have he1 : ∀ᶠ A in 𝓝[≠] (2 : ℂ), deltaU (A ^ 2) 3 ≠ 0 := by
    filter_upwards [hA2, hg1] with A hsub hg
    rw [fixed_discriminant_one]
    apply mul_ne_zero fixed_constant_one_ne
    rw [show fixedP1 A = (A - 2) *
        (A ^ 2 * (A + 2) * (A ^ 2 - 8) * (3 * A ^ 2 + 8)) by
      unfold fixedP1
      ring]
    exact mul_ne_zero hsub hg
  have he2 := eventually_ne_zero_at_two
    (fun A : ℂ => deltaU (-3 * A ^ 2) 3)
    (by unfold deltaU; fun_prop) (by
      rw [fixed_discriminant_two]
      exact mul_ne_zero fixed_constant_two_ne (by norm_num [fixedP2]))
  have hg3 := eventually_ne_zero_at_two
    (fun A : ℂ => A * (2 * A - 1) * (9 * A + 10) *
      (9 * A ^ 2 - 8) * (9 * A ^ 2 - A - 9))
    (by fun_prop) (by norm_num)
  have he3 : ∀ᶠ A in 𝓝[≠] (2 : ℂ), deltaU (-1 / 9) A ≠ 0 := by
    filter_upwards [hA2, hg3] with A hsub hg
    rw [fixed_discriminant_three]
    apply mul_ne_zero fixed_constant_three_ne
    rw [show fixedP3 A = (A - 2) *
        (A * (2 * A - 1) * (9 * A + 10) *
          (9 * A ^ 2 - 8) * (9 * A ^ 2 - A - 9)) by
      unfold fixedP3
      ring]
    exact mul_ne_zero hsub hg
  have hg4 := eventually_ne_zero_at_two
    (fun A : ℂ => A ^ 2 * (2 * A - 1) * (8 * A + 9) *
      (10 * A ^ 2 - 9) * (9 * A ^ 2 - A - 9))
    (by fun_prop) (by norm_num)
  have he4 : ∀ᶠ A in 𝓝[≠] (2 : ℂ), deltaU (A / 9) A ≠ 0 := by
    filter_upwards [hA2, hg4] with A hsub hg
    rw [fixed_discriminant_four]
    apply mul_ne_zero fixed_constant_four_ne
    rw [show fixedP4 A = (A - 2) *
        (A ^ 2 * (2 * A - 1) * (8 * A + 9) *
          (10 * A ^ 2 - 9) * (9 * A ^ 2 - A - 9)) by
      unfold fixedP4
      ring]
    exact mul_ne_zero hsub hg
  have he5 := eventually_ne_zero_at_two
    (fun A : ℂ => deltaU (-(1 / A ^ 2)) (Complex.I / 3))
    (by unfold deltaU; fun_prop (disch := norm_num)) fixedEdge5_two_ne
  have he6 := eventually_ne_zero_at_two
    (fun A : ℂ => deltaU (Complex.I / (3 * A ^ 2)) (Complex.I / 3))
    (by unfold deltaU; fun_prop (disch := norm_num)) fixedEdge6_two_ne
  have he7 := eventually_ne_zero_at_two
    (fun A : ℂ => deltaU 9 (Complex.I / A))
    (by unfold deltaU; fun_prop (disch := norm_num)) fixedEdge7_two_ne
  have he8 := eventually_ne_zero_at_two
    (fun A : ℂ => deltaU (-9 * Complex.I / A) (Complex.I / A))
    (by unfold deltaU; fun_prop (disch := norm_num)) fixedEdge8_two_ne
  filter_upwards [he1, he2, he3, he4, he5, he6, he7, he8]
    with A h1 h2 h3 h4 h5 h6 h7 h8
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem fixedLineAdmissible_near_two :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ A : ℂ, 0 < ‖A - 2‖ → ‖A - 2‖ < δ → FixedLineAdmissible A := by
  rcases Metric.mem_nhdsWithin_iff.mp eventually_fixedLineAdmissible with
    ⟨δ, hδ, hsubset⟩
  refine ⟨δ, hδ, fun A hpos hlt => ?_⟩
  apply hsubset
  constructor
  · simpa [Metric.mem_ball, dist_eq_norm] using hlt
  · have hA : A ≠ 2 := sub_ne_zero.mp (norm_pos_iff.mp hpos)
    simpa using hA

/-- The quantified pole estimate and all eight admissibility conditions hold
simultaneously on one punctured ball. -/
theorem fixedPeriod_quantified_pole_admissible :
    ∃ δ M : ℝ, 0 < δ ∧ 0 < M ∧
      ∀ A : ℂ, 0 < ‖A - 2‖ → ‖A - 2‖ < δ →
        FixedLineAdmissible A ∧
          ‖fixedPeriod A - 22 / (45 * (A - 2) ^ 2)‖ ≤ M / ‖A - 2‖ := by
  obtain ⟨δp, M, hδp, hM, hp⟩ := fixedPeriod_quantified_pole
  obtain ⟨δg, hδg, hg⟩ := fixedLineAdmissible_near_two
  let δ := min δp δg
  have hδ : 0 < δ := lt_min hδp hδg
  refine ⟨δ, M, hδ, hM, fun A hpos hlt => ?_⟩
  have hltp : ‖A - 2‖ < δp := hlt.trans_le (min_le_left _ _)
  have hltg : ‖A - 2‖ < δg := hlt.trans_le (min_le_right _ _)
  exact ⟨hg A hpos hltg, hp A hpos hltp⟩

theorem realComponent_unbounded_near_two
    (ell : ℂ →ₗ[ℝ] ℝ) (hell : ell ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (C : ℝ) :
    ∃ A : ℂ, 0 < ‖A - 2‖ ∧ ‖A - 2‖ < δ ∧
      C < |ell (fixedPeriod A)| := by
  by_contra h
  push_neg at h
  apply realComponent_not_locally_bounded ell hell
  refine ⟨C, ?_⟩
  have hballEv : ∀ᶠ A in 𝓝[≠] (2 : ℂ), A ∈ Metric.ball (2 : ℂ) δ :=
    eventually_nhdsWithin_of_eventually_nhds (Metric.ball_mem_nhds _ hδ)
  filter_upwards [hballEv, self_mem_nhdsWithin]
    with A hball hA
  have hne : A ≠ 2 := by simpa using hA
  have hpos : 0 < ‖A - 2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hlt : ‖A - 2‖ < δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hball
  exact h A hpos hlt

/-- Unbounded values can be chosen while every edge of the fixed-line cycle
remains admissible. -/
theorem realComponent_unbounded_on_admissible_fixedLine
    (ell : ℂ →ₗ[ℝ] ℝ) (hell : ell ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) (C : ℝ) :
    ∃ A : ℂ, 0 < ‖A - 2‖ ∧ ‖A - 2‖ < δ ∧
      FixedLineAdmissible A ∧ C < |ell (fixedPeriod A)| := by
  obtain ⟨δg, hδg, hg⟩ := fixedLineAdmissible_near_two
  have hmin : 0 < min δ δg := lt_min hδ hδg
  obtain ⟨A, hpos, hlt, hlarge⟩ :=
    realComponent_unbounded_near_two ell hell hmin C
  refine ⟨A, hpos, hlt.trans_le (min_le_left _ _), ?_, hlarge⟩
  exact hg A hpos (hlt.trans_le (min_le_right _ _))

end
end Pfaffian
end Sp4
