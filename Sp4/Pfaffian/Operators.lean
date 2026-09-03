import Sp4.Basic.FinTuple
import Sp4.Measure.L0
import Sp4.Pfaffian.Coordinates

/-!
# Pointwise Pfaffian coboundary operators

The almost-everywhere operators will later be induced from these total maps after
nonsingularity has been proved.  Keeping the pointwise layer independent prevents any
use of an almost-everywhere identity on a positive-codimension trace.
-/

namespace Sp4

namespace Pfaffian

noncomputable section

/-- The pointwise five-term coboundary on the normalized four-point locus. -/
def D {A : Type*} [AddGroup A] (f : U4 → A) (q : U5) : A :=
  f (face4_0 q) - f (face4_1 q) + f (face4_2 q) - f (face4_3 q) + f (face4_4 q)

@[simp]
theorem D_apply {A : Type*} [AddGroup A] (f : U4 → A) (q : U5) :
    D f q =
      f (face4_0 q) - f (face4_1 q) + f (face4_2 q) - f (face4_3 q) +
        f (face4_4 q) := rfl

theorem D_zero {A : Type*} [AddGroup A] : D (fun _ : U4 => (0 : A)) = 0 := by
  funext q
  simp [D]

theorem D_add {A : Type*} [AddCommGroup A] (f g : U4 → A) :
    D (f + g) = D f + D g := by
  funext q
  simp [D]
  abel

theorem D_neg {A : Type*} [AddCommGroup A] (f : U4 → A) : D (-f) = -D f := by
  funext q
  simp [D]
  abel

theorem D_sub {A : Type*} [AddCommGroup A] (f g : U4 → A) :
    D (f - g) = D f - D g := by
  funext q
  simp [D]
  abel

/-! The continuous layer is kept pointwise.  It is later combined with a full-support
measure to turn an essential `L^∞` bound into an everywhere bound. -/

@[continuity, fun_prop]
theorem continuous_face4_0 : Continuous face4_0 := by
  apply Continuous.subtype_mk
  apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
  apply Continuous.prodMk
  · change Continuous fun q : U5 => q.1.u * q.1.x / (q.1.v * q.1.w)
    exact ((continuous_coord5_u.comp continuous_subtype_val).mul
      (continuous_coord5_x.comp continuous_subtype_val)).div₀
        ((continuous_coord5_v.comp continuous_subtype_val).mul
          (continuous_coord5_w.comp continuous_subtype_val))
        (fun q => mul_ne_zero q.2.v_ne q.2.w_ne)
  · change Continuous fun q : U5 => q.1.y / (q.1.v * q.1.w)
    exact (continuous_coord5_y.comp continuous_subtype_val).div₀
      ((continuous_coord5_v.comp continuous_subtype_val).mul
        (continuous_coord5_w.comp continuous_subtype_val))
      (fun q => mul_ne_zero q.2.v_ne q.2.w_ne)

@[continuity, fun_prop]
theorem continuous_face4_1 : Continuous face4_1 := by
  apply Continuous.subtype_mk
  apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
  apply Continuous.prodMk
  · change Continuous fun q : U5 => q.1.x / q.1.w
    exact (continuous_coord5_x.comp continuous_subtype_val).div₀
      (continuous_coord5_w.comp continuous_subtype_val) (fun q => q.2.w_ne)
  · change Continuous fun q : U5 => q.1.y / q.1.w
    exact (continuous_coord5_y.comp continuous_subtype_val).div₀
      (continuous_coord5_w.comp continuous_subtype_val) (fun q => q.2.w_ne)

@[continuity, fun_prop]
theorem continuous_face4_2 : Continuous face4_2 := by
  apply Continuous.subtype_mk
  apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
  apply Continuous.prodMk
  · change Continuous fun q : U5 => q.1.v / q.1.u
    exact (continuous_coord5_v.comp continuous_subtype_val).div₀
      (continuous_coord5_u.comp continuous_subtype_val) (fun q => q.2.u_ne)
  · change Continuous fun q : U5 => q.1.y / q.1.u
    exact (continuous_coord5_y.comp continuous_subtype_val).div₀
      (continuous_coord5_u.comp continuous_subtype_val) (fun q => q.2.u_ne)

@[continuity, fun_prop]
theorem continuous_face4_3 : Continuous face4_3 := by
  apply Continuous.subtype_mk
  apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
  exact Continuous.prodMk
    (continuous_coord5_v.comp continuous_subtype_val)
    (continuous_coord5_x.comp continuous_subtype_val)

@[continuity, fun_prop]
theorem continuous_face4_4 : Continuous face4_4 := by
  apply Continuous.subtype_mk
  apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
  exact Continuous.prodMk
    (continuous_coord5_u.comp continuous_subtype_val)
    (continuous_coord5_w.comp continuous_subtype_val)

theorem continuous_D {f : U4 → ℝ} (hf : Continuous f) : Continuous (D f) :=
  ((((hf.comp continuous_face4_0).sub (hf.comp continuous_face4_1)).add
    (hf.comp continuous_face4_2)).sub (hf.comp continuous_face4_3)).add
      (hf.comp continuous_face4_4)

/-- The pointwise six-term coboundary on the normalized five-point locus. -/
def E {A : Type*} [AddGroup A] (F : U5 → A) (q : U6) : A :=
  F (face5_0 q) - F (face5_1 q) + F (face5_2 q) - F (face5_3 q) +
    F (face5_4 q) - F (face5_5 q)

@[simp]
theorem E_apply {A : Type*} [AddGroup A] (F : U5 → A) (q : U6) :
    E F q =
      F (face5_0 q) - F (face5_1 q) + F (face5_2 q) - F (face5_3 q) +
        F (face5_4 q) - F (face5_5 q) := rfl

theorem E_zero {A : Type*} [AddGroup A] : E (fun _ : U5 => (0 : A)) = 0 := by
  funext q
  simp [E]

theorem E_add {A : Type*} [AddCommGroup A] (F H : U5 → A) :
    E (F + H) = E F + E H := by
  funext q
  simp [E]
  abel

theorem E_neg {A : Type*} [AddCommGroup A] (F : U5 → A) : E (-F) = -E F := by
  funext q
  simp [E]
  abel

theorem E_sub {A : Type*} [AddCommGroup A] (F H : U5 → A) :
    E (F - H) = E F - E H := by
  funext q
  simp [E]
  abel

/-! ## Consecutive coboundaries

The fifteen rewrites below are precisely the `i < j` instances of the generic tuple
identity `FinTuple.delete_delete_swap`, transported through normalized Gram
coordinates.  After those rewrites the proof is purely the cancellation of opposite
simplicial signs.
-/

/-- Pointwise simplicial cancellation: the six-term operator annihilates the image of
the five-term operator. -/
theorem E_D_apply {A : Type*} [AddCommGroup A] (f : U4 → A) (q : U6) :
    E (D f) q = 0 := by
  simp only [E_apply, D_apply]
  rw [face4_0_face5_1, face4_0_face5_2, face4_0_face5_3, face4_0_face5_4,
    face4_0_face5_5, face4_1_face5_2, face4_1_face5_3, face4_1_face5_4,
    face4_1_face5_5, face4_2_face5_3, face4_2_face5_4, face4_2_face5_5,
    face4_3_face5_4, face4_3_face5_5, face4_4_face5_5]
  abel

/-- Functional form of `E ∘ D = 0`. -/
theorem E_D {A : Type*} [AddCommGroup A] (f : U4 → A) : E (D f) = 0 := by
  funext q
  exact E_D_apply f q

/-! ## Almost-everywhere operators

The hypotheses below name exactly the nonsingularity facts needed to pull an
a.e.-class through a face.  Concrete smooth measures will instantiate them later.
-/

open MeasureTheory

/-- A single indexed family for the five normalized four-point faces. -/
def face4At : Fin 5 → U5 → U4
  | 0 => face4_0
  | 1 => face4_1
  | 2 => face4_2
  | 3 => face4_3
  | 4 => face4_4

/-- A single indexed family for the six normalized five-point faces. -/
def face5At : Fin 6 → U6 → U5
  | 0 => face5_0
  | 1 => face5_1
  | 2 => face5_2
  | 3 => face5_3
  | 4 => face5_4
  | 5 => face5_5

/-- The alternating simplicial coefficient. -/
def faceSign (i : ℕ) : ℝ := (-1 : ℝ) ^ i

theorem D_eq_face_sum (f : U4 → ℝ) (q : U5) :
    D f q = ∑ i : Fin 5, faceSign i * f (face4At i q) := by
  simp [D, faceSign, face4At, Fin.sum_univ_succ]
  ring

theorem E_eq_face_sum (f : U5 → ℝ) (q : U6) :
    E f q = ∑ i : Fin 6, faceSign i * f (face5At i q) := by
  simp [E, faceSign, face5At, Fin.sum_univ_succ]
  ring

/-- Nonsingularity of all five maps entering `D`. -/
structure Face4QuasiMeasurePreserving (μ4 : Measure U4) (μ5 : Measure U5) : Prop where
  face0 : Measure.QuasiMeasurePreserving face4_0 μ5 μ4
  face1 : Measure.QuasiMeasurePreserving face4_1 μ5 μ4
  face2 : Measure.QuasiMeasurePreserving face4_2 μ5 μ4
  face3 : Measure.QuasiMeasurePreserving face4_3 μ5 μ4
  face4 : Measure.QuasiMeasurePreserving face4_4 μ5 μ4

/-- Nonsingularity of all six maps entering `E`. -/
structure Face5QuasiMeasurePreserving (μ5 : Measure U5) (μ6 : Measure U6) : Prop where
  face0 : Measure.QuasiMeasurePreserving face5_0 μ6 μ5
  face1 : Measure.QuasiMeasurePreserving face5_1 μ6 μ5
  face2 : Measure.QuasiMeasurePreserving face5_2 μ6 μ5
  face3 : Measure.QuasiMeasurePreserving face5_3 μ6 μ5
  face4 : Measure.QuasiMeasurePreserving face5_4 μ6 μ5
  face5 : Measure.QuasiMeasurePreserving face5_5 μ6 μ5

theorem Face4QuasiMeasurePreserving.at {μ4 : Measure U4} {μ5 : Measure U5}
    (h : Face4QuasiMeasurePreserving μ4 μ5) (i : Fin 5) :
    Measure.QuasiMeasurePreserving (face4At i) μ5 μ4 := by
  fin_cases i
  · simpa [face4At] using h.face0
  · simpa [face4At] using h.face1
  · simpa [face4At] using h.face2
  · simpa [face4At] using h.face3
  · simpa [face4At] using h.face4

theorem Face5QuasiMeasurePreserving.at {μ5 : Measure U5} {μ6 : Measure U6}
    (h : Face5QuasiMeasurePreserving μ5 μ6) (i : Fin 6) :
    Measure.QuasiMeasurePreserving (face5At i) μ6 μ5 := by
  fin_cases i
  · simpa [face5At] using h.face0
  · simpa [face5At] using h.face1
  · simpa [face5At] using h.face2
  · simpa [face5At] using h.face3
  · simpa [face5At] using h.face4
  · simpa [face5At] using h.face5

variable {μ4 : Measure U4} {μ5 : Measure U5} {μ6 : Measure U6}

/-- The five-term Pfaffian differential on finite measurable a.e.-classes. -/
noncomputable def D0 (h : Face4QuasiMeasurePreserving μ4 μ5) :
    L0 U4 μ4 →ₗ[ℝ] L0 U5 μ5 :=
  L0.weightedPullbackₗ face4At h.at (fun i => faceSign i)

/-- The six-term Pfaffian differential on finite measurable a.e.-classes. -/
noncomputable def E0 (h : Face5QuasiMeasurePreserving μ5 μ6) :
    L0 U5 μ5 →ₗ[ℝ] L0 U6 μ6 :=
  L0.weightedPullbackₗ face5At h.at (fun i => faceSign i)

theorem coeFn_D0 (h : Face4QuasiMeasurePreserving μ4 μ5) (f : L0 U4 μ4) :
    (D0 h f : U5 → ℝ) =ᵐ[μ5] D f := by
  exact (L0.coeFn_weightedPullbackₗ face4At h.at (fun i => faceSign i) f).trans
    (Filter.Eventually.of_forall fun q => (D_eq_face_sum f q).symm)

theorem coeFn_E0 (h : Face5QuasiMeasurePreserving μ5 μ6) (f : L0 U5 μ5) :
    (E0 h f : U6 → ℝ) =ᵐ[μ6] E f := by
  exact (L0.coeFn_weightedPullbackₗ face5At h.at (fun i => faceSign i) f).trans
    (Filter.Eventually.of_forall fun q => (E_eq_face_sum f q).symm)

theorem D_ae_congr (h : Face4QuasiMeasurePreserving μ4 μ5)
    {f g : U4 → ℝ} (hfg : f =ᵐ[μ4] g) : D f =ᵐ[μ5] D g := by
  have hall : ∀ᵐ q ∂μ5, ∀ i : Fin 5,
      f (face4At i q) = g (face4At i q) :=
    Filter.eventually_all.2 fun i => (h.at i).ae hfg
  filter_upwards [hall] with q hq
  rw [D_eq_face_sum, D_eq_face_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hq i]

theorem E_ae_congr (h : Face5QuasiMeasurePreserving μ5 μ6)
    {f g : U5 → ℝ} (hfg : f =ᵐ[μ5] g) : E f =ᵐ[μ6] E g := by
  have hall : ∀ᵐ q ∂μ6, ∀ i : Fin 6,
      f (face5At i q) = g (face5At i q) :=
    Filter.eventually_all.2 fun i => (h.at i).ae hfg
  filter_upwards [hall] with q hq
  rw [E_eq_face_sum, E_eq_face_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hq i]

/-- The a.e. operators still satisfy the simplicial identity.  The proof pulls the
a.e. representative statement through each nonsingular second face before applying
the pointwise cancellation theorem. -/
theorem E0_D0 (h4 : Face4QuasiMeasurePreserving μ4 μ5)
    (h5 : Face5QuasiMeasurePreserving μ5 μ6) (f : L0 U4 μ4) :
    E0 h5 (D0 h4 f) = 0 := by
  apply AEEqFun.ext
  have hfaces : ∀ᵐ q ∂μ6, ∀ i : Fin 6,
      (D0 h4 f) (face5At i q) = D f (face5At i q) :=
    Filter.eventually_all.2 fun i => h5.at i |>.ae (coeFn_D0 h4 f)
  filter_upwards [coeFn_E0 h5 (D0 h4 f), hfaces,
    (AEEqFun.coeFn_zero :
      ((0 : L0 U6 μ6) : U6 → ℝ) =ᵐ[μ6] (0 : U6 → ℝ))] with q hE hD hzero
  rw [hE, E_eq_face_sum]
  simp_rw [hD]
  rw [← E_eq_face_sum, E_D_apply]
  exact hzero.symm

/-- The five-term Pfaffian differential on `L^∞`. -/
noncomputable def Dinfₗ (h : Face4QuasiMeasurePreserving μ4 μ5) :
    Linfty U4 μ4 →ₗ[ℝ] Linfty U5 μ5 :=
  Linfty.weightedPullbackₗ face4At h.at (fun i => faceSign i)

/-- The six-term Pfaffian differential on `L^∞`. -/
noncomputable def Einfₗ (h : Face5QuasiMeasurePreserving μ5 μ6) :
    Linfty U5 μ5 →ₗ[ℝ] Linfty U6 μ6 :=
  Linfty.weightedPullbackₗ face5At h.at (fun i => faceSign i)

theorem norm_Dinfₗ_le (h : Face4QuasiMeasurePreserving μ4 μ5)
    (f : Linfty U4 μ4) : ‖Dinfₗ h f‖ ≤ 5 * ‖f‖ := by
  simpa [Dinfₗ, faceSign] using
    Linfty.norm_weightedPullbackₗ_le face4At h.at (fun i => faceSign i) f

theorem norm_Einfₗ_le (h : Face5QuasiMeasurePreserving μ5 μ6)
    (f : Linfty U5 μ5) : ‖Einfₗ h f‖ ≤ 6 * ‖f‖ := by
  simpa [Einfₗ, faceSign] using
    Linfty.norm_weightedPullbackₗ_le face5At h.at (fun i => faceSign i) f

/-- `D` as a bounded linear operator of norm at most five. -/
noncomputable def Dinf (h : Face4QuasiMeasurePreserving μ4 μ5) :
    Linfty U4 μ4 →L[ℝ] Linfty U5 μ5 :=
  (Dinfₗ h).mkContinuous 5 (norm_Dinfₗ_le h)

/-- `E` as a bounded linear operator of norm at most six. -/
noncomputable def Einf (h : Face5QuasiMeasurePreserving μ5 μ6) :
    Linfty U5 μ5 →L[ℝ] Linfty U6 μ6 :=
  (Einfₗ h).mkContinuous 6 (norm_Einfₗ_le h)

theorem norm_Dinf_le (h : Face4QuasiMeasurePreserving μ4 μ5) :
    ‖Dinf h‖ ≤ 5 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) (norm_Dinfₗ_le h)

theorem norm_Einf_le (h : Face5QuasiMeasurePreserving μ5 μ6) :
    ‖Einf h‖ ≤ 6 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) (norm_Einfₗ_le h)

theorem coe_Dinfₗ (h : Face4QuasiMeasurePreserving μ4 μ5) (f : Linfty U4 μ4) :
    (Dinfₗ h f : L0 U5 μ5) = D0 h f.1 :=
  Linfty.coe_weightedPullbackₗ face4At h.at (fun i => faceSign i) f

theorem coe_Einfₗ (h : Face5QuasiMeasurePreserving μ5 μ6) (f : Linfty U5 μ5) :
    (Einfₗ h f : L0 U6 μ6) = E0 h f.1 :=
  Linfty.coe_weightedPullbackₗ face5At h.at (fun i => faceSign i) f

theorem Einf_Dinf (h4 : Face4QuasiMeasurePreserving μ4 μ5)
    (h5 : Face5QuasiMeasurePreserving μ5 μ6) (f : Linfty U4 μ4) :
    Einf h5 (Dinf h4 f) = 0 := by
  apply Subtype.ext
  change (Einfₗ h5 (Dinfₗ h4 f) : L0 U6 μ6) = 0
  rw [coe_Einfₗ, coe_Dinfₗ]
  exact E0_D0 h4 h5 f.1

end

end Pfaffian

end Sp4
