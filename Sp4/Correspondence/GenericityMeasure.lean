import Sp4.Cohomology.ExternalInputs
import Sp4.Correspondence.Genericity
import Sp4.Measure.GaussianLebesgue
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Measure-theoretic genericity for correspondence words

This file upgrades the residual fully-generic locus constructed in
`Sp4.Correspondence.Genericity` to a conull measurable locus.  The proof uses
the concrete Gaussian chart measure, the analytic zero-set theorem recorded in
`Sp4.Cohomology.ExternalInputs`, and the coarea null-set consequence recorded
there.  In particular, no new article-specific theorem is assumed here.
-/

open MeasureTheory ProbabilityTheory
open Sp4

theorem standardComplexGaussianPi_zeroSet
    {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f Set.univ)
    (hnontrivial : ∃ x, f x ≠ 0) :
    standardComplexGaussianPi n {x | f x = 0} = 0 := by
  let ev : (Unit → (Fin n → ℂ)) →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.proj (R := ℂ)
      (φ := fun _ : Unit => Fin n → ℂ) Unit.unit
  have hfev : AnalyticOnNhd ℂ (f ∘ ev) Set.univ := by
    exact hf.comp (ev.analyticOnNhd Set.univ) (Set.mapsTo_univ _ _)
  have hnon : ∃ z : Unit → (Fin n → ℂ), (f ∘ ev) z ≠ 0 := by
    obtain ⟨x, hx⟩ := hnontrivial
    exact ⟨fun _ => x, hx⟩
  have hzero :=
    measure_zero_zeroSet_of_nontrivial_complex_analytic_piGaussian
      (fun _ : Unit => n) (f ∘ ev) hfev hnon
  have hmp := measurePreserving_funUnique
    (standardComplexGaussianPi n) Unit
  rw [← hmp.map_eq]
  rw [Measure.map_apply_of_aemeasurable hmp.measurable.aemeasurable
    (isClosed_eq hf.continuous continuous_const).measurableSet]
  simpa [ev, Function.comp_def, standardComplexGaussianPi] using hzero

namespace Sp4.Pfaffian

local instance : FiniteDimensional ℂ Coord4 :=
  LinearEquiv.finiteDimensional coord4LinearEquivProd.symm

noncomputable def coord4XContinuousLinearMap : Coord4 →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).comp
    coord4ContinuousLinearEquivFun.toContinuousLinearMap

noncomputable def coord4YContinuousLinearMap : Coord4 →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).comp
    coord4ContinuousLinearEquivFun.toContinuousLinearMap

@[fun_prop]
theorem analyticAt_coord4_x (q : Coord4) :
    AnalyticAt ℂ (fun p : Coord4 => p.x) q := by
  rw [show (fun p : Coord4 => p.x) = coord4XContinuousLinearMap by
    funext p
    simp [coord4XContinuousLinearMap, coord4ContinuousLinearEquivFun,
      coord4LinearIsometryEquivProd, coord4LinearEquivProd, coord4EquivProd]]
  exact coord4XContinuousLinearMap.analyticOnNhd Set.univ q (Set.mem_univ q)

@[fun_prop]
theorem analyticAt_coord4_y (q : Coord4) :
    AnalyticAt ℂ (fun p : Coord4 => p.y) q := by
  rw [show (fun p : Coord4 => p.y) = coord4YContinuousLinearMap by
    funext p
    simp [coord4YContinuousLinearMap, coord4ContinuousLinearEquivFun,
      coord4LinearIsometryEquivProd, coord4LinearEquivProd, coord4EquivProd]]
  exact coord4YContinuousLinearMap.analyticOnNhd Set.univ q (Set.mem_univ q)

noncomputable def coord4Lebesgue : Measure Coord4 :=
  Measure.map coord4ContinuousLinearEquivFun.symm
    (volume : Measure (Fin 2 → ℂ))

instance : Measure.IsAddHaarMeasure coord4Lebesgue := by
  dsimp [coord4Lebesgue]
  infer_instance

theorem coord4Gaussian_absolutelyContinuous_coord4Lebesgue :
    coord4Gaussian ≪ coord4Lebesgue := by
  have h := standardComplexGaussianPi_two_absolutelyContinuous_volume.map
    coord4ContinuousLinearEquivFun.symm.continuous.measurable
  simpa [coord4Gaussian, coord4Lebesgue] using h

theorem coord4Lebesgue_absolutelyContinuous_coord4Gaussian :
    coord4Lebesgue ≪ coord4Gaussian := by
  have h := volume_absolutelyContinuous_standardComplexGaussianPi_two.map
    coord4ContinuousLinearEquivFun.symm.continuous.measurable
  simpa [coord4Gaussian, coord4Lebesgue] using h

theorem coord4Gaussian_zeroSet
    (f : Coord4 → ℂ) (hf : AnalyticOnNhd ℂ f Set.univ)
    (hnontrivial : ∃ x, f x ≠ 0) :
    coord4Gaussian {x | f x = 0} = 0 := by
  let e : (Fin 2 → ℂ) →L[ℂ] Coord4 :=
    coord4ContinuousLinearEquivFun.symm.toContinuousLinearMap
  have hfe : AnalyticOnNhd ℂ (f ∘ e) Set.univ :=
    hf.comp (e.analyticOnNhd Set.univ) (Set.mapsTo_univ _ _)
  have hnon : ∃ z : Fin 2 → ℂ, (f ∘ e) z ≠ 0 := by
    obtain ⟨x, hx⟩ := hnontrivial
    exact ⟨coord4ContinuousLinearEquivFun x, by simpa [e] using hx⟩
  have hzero := standardComplexGaussianPi_zeroSet (f ∘ e) hfe hnon
  rw [coord4Gaussian, Measure.map_apply_of_aemeasurable
    coord4ContinuousLinearEquivFun.symm.continuous.measurable.aemeasurable
    (isClosed_eq hf.continuous continuous_const).measurableSet]
  simpa [e, Function.comp_def] using hzero

theorem normalizedCoord4Gaussian_image_null
    (s : Set Coord4) (hs : IsOpen s) (hne : s.Nonempty)
    (f : Coord4 → Coord4) (hfs : ∀ x, x ∈ s → f x ∈ s)
    (hf : DifferentiableOn ℂ f s)
    {t : Set s} (ht : MeasurableSet t)
    (himage : MeasurableSet
      ((fun x : s => (⟨f x.1, hfs x.1 x.2⟩ : s)) '' t))
    (hnull : normalizedOpenMeasure coord4Gaussian s hs hne t = 0) :
    normalizedOpenMeasure coord4Gaussian s hs hne
      ((fun x : s => (⟨f x.1, hfs x.1 x.2⟩ : s)) '' t) = 0 := by
  let fS : s → s := fun x => ⟨f x.1, hfs x.1 x.2⟩
  have htAmbient : MeasurableSet (Subtype.val '' t : Set Coord4) :=
    (MeasurableEmbedding.subtype_coe hs.measurableSet).measurableSet_image' ht
  have htNullGaussian : coord4Gaussian (Subtype.val '' t) = 0 :=
    (Sp4.normalizedOpenMeasure_eq_zero_iff_image coord4Gaussian s hs hne ht).mp hnull
  have htNullLebesgue : coord4Lebesgue (Subtype.val '' t) = 0 :=
    coord4Lebesgue_absolutelyContinuous_coord4Gaussian htNullGaussian
  have hsub : Subtype.val '' t ⊆ s := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hdiffR : DifferentiableOn ℝ f (Subtype.val '' t) :=
    (hf.mono hsub).restrictScalars ℝ
  have himageLebesgue :
      coord4Lebesgue (f '' (Subtype.val '' t)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      coord4Lebesgue hdiffR htNullLebesgue
  have himageGaussian :
      coord4Gaussian (f '' (Subtype.val '' t)) = 0 :=
    coord4Gaussian_absolutelyContinuous_coord4Lebesgue himageLebesgue
  apply (Sp4.normalizedOpenMeasure_eq_zero_iff_image coord4Gaussian s hs hne himage).mpr
  have heq : Subtype.val '' (fS '' t) = f '' (Subtype.val '' t) := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨fS x, ⟨x, hx, rfl⟩, rfl⟩
  rw [heq]
  exact himageGaussian

def sourceAmbientProd (q : ℂ × ℂ) : ℂ × ℂ := (-q.1, -(q.2 ^ 2))

def targetAmbientProd (q : ℂ × ℂ) : ℂ × ℂ := (q.1 * q.2, -(q.2 ^ 2))

theorem sourceAmbientProd_submersion (p : ℂ × ℂ) (hp : p.2 ≠ 0) :
    HasSurjectiveComplexFDerivAt sourceAmbientProd p := by
  have hdiff : DifferentiableAt ℂ sourceAmbientProd p := by
    unfold sourceAmbientProd
    fun_prop
  refine ⟨hdiff, ?_⟩
  intro z
  refine ⟨(-z.1, -z.2 / (2 * p.2)), ?_⟩
  have hfd := (hasFDerivAt_fst (𝕜 := ℂ) (p := p)).neg.prodMk
    ((hasFDerivAt_snd (𝕜 := ℂ) (p := p)).pow 2).neg
  have heq := hfd.fderiv
  change fderiv ℂ sourceAmbientProd p = _ at heq
  rw [heq]
  apply Prod.ext
  · simp
  · simp
    field_simp [hp]

theorem targetAmbientProd_submersion (p : ℂ × ℂ) (hp : p.2 ≠ 0) :
    HasSurjectiveComplexFDerivAt targetAmbientProd p := by
  have hdiff : DifferentiableAt ℂ targetAmbientProd p := by
    unfold targetAmbientProd
    fun_prop
  refine ⟨hdiff, ?_⟩
  intro z
  let hy : ℂ := -z.2 / (2 * p.2)
  let hx : ℂ := (z.1 - p.1 * hy) / p.2
  refine ⟨(hx, hy), ?_⟩
  have hfd := ((hasFDerivAt_fst (𝕜 := ℂ) (p := p)).mul
      (hasFDerivAt_snd (𝕜 := ℂ) (p := p))).prodMk
    ((hasFDerivAt_snd (𝕜 := ℂ) (p := p)).pow 2).neg
  have heq := hfd.fderiv
  change fderiv ℂ targetAmbientProd p = _ at heq
  rw [heq]
  apply Prod.ext
  · simp
    dsimp [hx]
    field_simp [hp]
    ring
  · simp
    change -(2 * p.2 * hy) = z.2
    dsimp [hy]
    field_simp [hp]

theorem sourceUCoord_eq_conjugated_sourceAmbientProd :
    sourceUCoord =
      coord4LinearIsometryEquivProd.symm ∘ sourceAmbientProd ∘
        coord4LinearIsometryEquivProd := by
  funext q
  apply coord4LinearIsometryEquivProd.injective
  simp [sourceUCoord, sourceAmbientProd, Function.comp_def,
    coord4LinearIsometryEquivProd, coord4LinearEquivProd, coord4EquivProd]

theorem targetUCoord_eq_conjugated_targetAmbientProd :
    targetUCoord =
      coord4LinearIsometryEquivProd.symm ∘ targetAmbientProd ∘
        coord4LinearIsometryEquivProd := by
  funext q
  apply coord4LinearIsometryEquivProd.injective
  simp [targetUCoord, targetAmbientProd, Function.comp_def,
    coord4LinearIsometryEquivProd, coord4LinearEquivProd, coord4EquivProd]

theorem sourceUCoord_submersion (p : Coord4) (hp : p.y ≠ 0) :
    HasSurjectiveComplexFDerivAt sourceUCoord p := by
  rw [sourceUCoord_eq_conjugated_sourceAmbientProd]
  have hm := sourceAmbientProd_submersion
    (coord4LinearIsometryEquivProd p) hp
  have hr : DifferentiableAt ℂ
      (sourceAmbientProd ∘ coord4LinearIsometryEquivProd) p :=
    hm.1.comp p coord4LinearIsometryEquivProd.differentiableAt
  refine ⟨coord4LinearIsometryEquivProd.symm.differentiableAt.comp p hr, ?_⟩
  rw [fderiv_comp p coord4LinearIsometryEquivProd.symm.differentiableAt hr,
    fderiv_comp p hm.1 coord4LinearIsometryEquivProd.differentiableAt,
    coord4LinearIsometryEquivProd.symm.hasFDerivAt.fderiv,
    coord4LinearIsometryEquivProd.hasFDerivAt.fderiv]
  exact coord4LinearIsometryEquivProd.symm.surjective.comp
    (hm.2.comp coord4LinearIsometryEquivProd.surjective)

theorem targetUCoord_submersion (p : Coord4) (hp : p.y ≠ 0) :
    HasSurjectiveComplexFDerivAt targetUCoord p := by
  rw [targetUCoord_eq_conjugated_targetAmbientProd]
  have hm := targetAmbientProd_submersion
    (coord4LinearIsometryEquivProd p) hp
  have hr : DifferentiableAt ℂ
      (targetAmbientProd ∘ coord4LinearIsometryEquivProd) p :=
    hm.1.comp p coord4LinearIsometryEquivProd.differentiableAt
  refine ⟨coord4LinearIsometryEquivProd.symm.differentiableAt.comp p hr, ?_⟩
  rw [fderiv_comp p coord4LinearIsometryEquivProd.symm.differentiableAt hr,
    fderiv_comp p hm.1 coord4LinearIsometryEquivProd.differentiableAt,
    coord4LinearIsometryEquivProd.symm.hasFDerivAt.fderiv,
    coord4LinearIsometryEquivProd.hasFDerivAt.fderiv]
  exact coord4LinearIsometryEquivProd.symm.surjective.comp
    (hm.2.comp coord4LinearIsometryEquivProd.surjective)

def torusSet : Set Coord4 := {q | IsTorusPoint q}

theorem isOpen_torusSet : IsOpen torusSet := by
  rw [show torusSet = {q : Coord4 | q.x ≠ 0} ∩
      {q : Coord4 | q.y ≠ 0} by
    ext q
    constructor
    · intro h
      exact ⟨h.x_ne, h.y_ne⟩
    · rintro ⟨hx, hy⟩
      exact ⟨hx, hy⟩]
  exact (isOpen_ne_fun continuous_coord4_x continuous_const).inter
    (isOpen_ne_fun continuous_coord4_y continuous_const)

theorem torusSet_nonempty : torusSet.Nonempty := by
  exact ⟨⟨1, 1⟩, ⟨one_ne_zero, one_ne_zero⟩⟩

noncomputable def measureTorus : Measure TorusPoint :=
  normalizedOpenMeasure coord4Gaussian torusSet
    isOpen_torusSet torusSet_nonempty

instance : IsProbabilityMeasure measureTorus :=
  normalizedOpenMeasure_isProbability coord4Gaussian torusSet
    isOpen_torusSet torusSet_nonempty

instance : Measure.IsOpenPosMeasure measureTorus :=
  normalizedOpenMeasure_isOpenPos coord4Gaussian torusSet
    isOpen_torusSet torusSet_nonempty

theorem stateBad_measure_zero : measureTorus stateBad = 0 := by
  apply (Sp4.normalizedOpenMeasure_eq_zero_iff_image coord4Gaussian torusSet
    isOpen_torusSet torusSet_nonempty
    stateBad_closed_nowhereDense.1.measurableSet).mpr
  apply measure_mono_null (t := {q : Coord4 | delta4 q = 0})
  · rintro _ ⟨q, hq, rfl⟩
    exact hq
  · apply coord4Gaussian_zeroSet delta4
    · intro q hq
      unfold delta4
      fun_prop
    · exact ⟨⟨1, 1⟩, by simp [delta4]⟩

theorem edgeBad_measure_zero : measureTorus edgeBad = 0 := by
  apply (Sp4.normalizedOpenMeasure_eq_zero_iff_image coord4Gaussian torusSet
    isOpen_torusSet torusSet_nonempty
    edgeBad_closed_nowhereDense.1.measurableSet).mpr
  apply measure_mono_null (t := {q : Coord4 | deltaU q.x q.y = 0})
  · rintro _ ⟨q, hq, rfl⟩
    exact hq
  · apply coord4Gaussian_zeroSet (fun q : Coord4 => deltaU q.x q.y)
    · intro q hq
      dsimp [deltaU]
      fun_prop
    · exact ⟨⟨2, 3⟩, by norm_num [deltaU]⟩

theorem sourceU_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving sourceU
      measureTorus measureTorus := by
  change Measure.QuasiMeasurePreserving
    (fun q : {x : Coord4 // x ∈ torusSet} =>
      (⟨sourceUCoord q.1, sourceUCoord_mem q⟩ :
        {x : Coord4 // x ∈ torusSet}))
    (normalizedOpenMeasure coord4Gaussian torusSet
      isOpen_torusSet torusSet_nonempty)
    (normalizedOpenMeasure coord4Gaussian torusSet
      isOpen_torusSet torusSet_nonempty)
  have h := quasiMeasurePreserving_normalizedOpenGaussian_of_submersion
    coord4Gaussian coord4Gaussian coord4GaussianPresentation
    coord4GaussianPresentation torusSet isOpen_torusSet
    torusSet_nonempty torusSet isOpen_torusSet
    torusSet_nonempty sourceUCoord
    (fun x hx => sourceUCoord_mem ⟨x, hx⟩)
    (fun x hx => sourceUCoord_submersion x hx.y_ne)
  convert h using 1

theorem targetU_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving targetU
      measureTorus measureTorus := by
  change Measure.QuasiMeasurePreserving
    (fun q : {x : Coord4 // x ∈ torusSet} =>
      (⟨targetUCoord q.1, targetUCoord_mem q⟩ :
        {x : Coord4 // x ∈ torusSet}))
    (normalizedOpenMeasure coord4Gaussian torusSet
      isOpen_torusSet torusSet_nonempty)
    (normalizedOpenMeasure coord4Gaussian torusSet
      isOpen_torusSet torusSet_nonempty)
  have h := quasiMeasurePreserving_normalizedOpenGaussian_of_submersion
    coord4Gaussian coord4Gaussian coord4GaussianPresentation
    coord4GaussianPresentation torusSet isOpen_torusSet
    torusSet_nonempty torusSet isOpen_torusSet
    torusSet_nonempty targetUCoord
    (fun x hx => targetUCoord_mem ⟨x, hx⟩)
    (fun x hx => targetUCoord_submersion x hx.y_ne)
  convert h using 1

theorem torus_image_null
    (f : Coord4 → Coord4) (hfs : ∀ x, x ∈ torusSet → f x ∈ torusSet)
    (hf : DifferentiableOn ℂ f torusSet)
    {s : Set TorusPoint} (hs : MeasurableSet s)
    (himage : MeasurableSet
      ((fun q : TorusPoint =>
        (⟨f q.1, hfs q.1 q.2⟩ : TorusPoint)) '' s))
    (hnull : measureTorus s = 0) :
    measureTorus
      ((fun q : TorusPoint =>
        (⟨f q.1, hfs q.1 q.2⟩ : TorusPoint)) '' s) = 0 := by
  exact normalizedCoord4Gaussian_image_null torusSet isOpen_torusSet
    torusSet_nonempty f hfs hf hs himage hnull

theorem sourceU_image_null {s : Set TorusPoint} (hs : MeasurableSet s)
    (himage : MeasurableSet (sourceU '' s))
    (hnull : measureTorus s = 0) :
    measureTorus (sourceU '' s) = 0 := by
  have h := torus_image_null sourceUCoord
    (fun x hx => sourceUCoord_mem ⟨x, hx⟩)
    (fun x hx => (sourceUCoord_submersion x hx.y_ne).1.differentiableWithinAt)
    hs himage hnull
  have hmap : sourceU = fun q : TorusPoint =>
      (⟨sourceUCoord q.1, sourceUCoord_mem q⟩ : TorusPoint) := rfl
  rw [hmap]
  exact h

theorem targetU_image_null {s : Set TorusPoint} (hs : MeasurableSet s)
    (himage : MeasurableSet (targetU '' s))
    (hnull : measureTorus s = 0) :
    measureTorus (targetU '' s) = 0 := by
  have h := torus_image_null targetUCoord
    (fun x hx => targetUCoord_mem ⟨x, hx⟩)
    (fun x hx => (targetUCoord_submersion x hx.y_ne).1.differentiableWithinAt)
    hs himage hnull
  have hmap : targetU = fun q : TorusPoint =>
      (⟨targetUCoord q.1, targetUCoord_mem q⟩ : TorusPoint) := rfl
  rw [hmap]
  exact h

theorem cyclicCoord_differentiableOn :
    DifferentiableOn ℂ cyclicCoord torusSet := by
  intro x hx
  change IsTorusPoint x at hx
  have hy : x.y ≠ 0 := hx.y_ne
  apply (differentiableAt_coord4_mk
    (f := fun q : Coord4 => -1 / q.y)
    (g := fun q : Coord4 => -q.x / q.y) (a := x)
      (by fun_prop (disch := assumption))
      (by fun_prop (disch := assumption))).differentiableWithinAt

theorem cyclicSqCoord_differentiableOn :
    DifferentiableOn ℂ cyclicSqCoord torusSet := by
  intro x hx
  change IsTorusPoint x at hx
  have hx0 : x.x ≠ 0 := hx.x_ne
  apply (differentiableAt_coord4_mk
    (f := fun q : Coord4 => q.y / q.x)
    (g := fun q : Coord4 => -1 / q.x) (a := x)
      (by fun_prop (disch := assumption))
      (by fun_prop (disch := assumption))).differentiableWithinAt

theorem rhoCoord_differentiableOn :
    DifferentiableOn ℂ rhoCoord torusSet := by
  intro x hx
  exact (differentiableAt_coord4_mk (a := x) (by fun_prop)
    (by fun_prop)).differentiableWithinAt

theorem torusCyclic_image_null {s : Set TorusPoint} (hs : MeasurableSet s)
    (himage : MeasurableSet (torusCyclic '' s))
    (hnull : measureTorus s = 0) :
    measureTorus (torusCyclic '' s) = 0 := by
  have h := torus_image_null cyclicCoord
    (fun x hx => cyclicCoord_torus_mem ⟨x, hx⟩)
    cyclicCoord_differentiableOn hs himage hnull
  have hmap : torusCyclic = fun q : TorusPoint =>
      (⟨cyclicCoord q.1, cyclicCoord_torus_mem q⟩ : TorusPoint) := rfl
  rw [hmap]
  exact h

theorem torusCyclicInv_image_null {s : Set TorusPoint} (hs : MeasurableSet s)
    (himage : MeasurableSet (torusCyclicInv '' s))
    (hnull : measureTorus s = 0) :
    measureTorus (torusCyclicInv '' s) = 0 := by
  have h := torus_image_null cyclicSqCoord
    (fun x hx => cyclicSqCoord_torus_mem ⟨x, hx⟩)
    cyclicSqCoord_differentiableOn hs himage hnull
  have hmap : torusCyclicInv = fun q : TorusPoint =>
      (⟨cyclicSqCoord q.1, cyclicSqCoord_torus_mem q⟩ : TorusPoint) := rfl
  rw [hmap]
  exact h

theorem torusRho_image_null {s : Set TorusPoint} (hs : MeasurableSet s)
    (himage : MeasurableSet (torusRho '' s))
    (hnull : measureTorus s = 0) :
    measureTorus (torusRho '' s) = 0 := by
  have h := torus_image_null rhoCoord
    (fun x hx => rhoCoord_torus_mem ⟨x, hx⟩)
    rhoCoord_differentiableOn hs himage hnull
  have hmap : torusRho = fun q : TorusPoint =>
      (⟨rhoCoord q.1, rhoCoord_torus_mem q⟩ : TorusPoint) := rfl
  rw [hmap]
  exact h

theorem torusCyclic_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving torusCyclic
      measureTorus measureTorus where
  measurable := torusCyclicHomeomorph.continuous.measurable
  absolutelyContinuous := by
    apply Measure.AbsolutelyContinuous.mk
    intro s hs hnull
    have hmeas : Measurable torusCyclic :=
      torusCyclicHomeomorph.continuous.measurable
    rw [Measure.map_apply hmeas hs]
    have himage : MeasurableSet (torusCyclicInv '' s) :=
      torusCyclicHomeomorph.symm.measurableEmbedding.measurableSet_image' hs
    have hz := torusCyclicInv_image_null hs himage hnull
    rw [show torusCyclic ⁻¹' s = torusCyclicInv '' s by
      ext x
      constructor
      · intro hx
        exact ⟨torusCyclic x, hx, torusCyclicInv_cyclic x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy]
    exact hz

theorem torusCyclicInv_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving torusCyclicInv
      measureTorus measureTorus where
  measurable := torusCyclicHomeomorph.symm.continuous.measurable
  absolutelyContinuous := by
    apply Measure.AbsolutelyContinuous.mk
    intro s hs hnull
    have hmeas : Measurable torusCyclicInv :=
      torusCyclicHomeomorph.symm.continuous.measurable
    rw [Measure.map_apply hmeas hs]
    have himage : MeasurableSet (torusCyclic '' s) :=
      torusCyclicHomeomorph.measurableEmbedding.measurableSet_image' hs
    have hz := torusCyclic_image_null hs himage hnull
    rw [show torusCyclicInv ⁻¹' s = torusCyclic '' s by
      ext x
      constructor
      · intro hx
        exact ⟨torusCyclicInv x, hx, torusCyclic_cyclicInv x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy]
    exact hz

theorem torusRho_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving torusRho
      measureTorus measureTorus where
  measurable := torusRhoHomeomorph.continuous.measurable
  absolutelyContinuous := by
    apply Measure.AbsolutelyContinuous.mk
    intro s hs hnull
    have hmeas : Measurable torusRho :=
      torusRhoHomeomorph.continuous.measurable
    rw [Measure.map_apply hmeas hs]
    have himage : MeasurableSet (torusRho '' s) :=
      torusRhoHomeomorph.measurableEmbedding.measurableSet_image' hs
    have hz := torusRho_image_null hs himage hnull
    rw [show torusRho ⁻¹' s = torusRho '' s by
      ext x
      constructor
      · intro hx
        exact ⟨torusRho x, hx, torusRho_rho x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy]
    exact hz

theorem wordBadEnvelope_measure_zero (word : List CorrLetter) :
    measureTorus (wordBadEnvelope word) = 0 := by
  induction word with
  | nil => exact stateBad_measure_zero
  | cons letter word ih =>
      cases letter with
      | U =>
          have hpre : measureTorus (targetU ⁻¹' wordBadEnvelope word) = 0 :=
            targetU_quasiMeasurePreserving.preimage_null ih
          have hinner : measureTorus
              (edgeBad ∪ targetU ⁻¹' wordBadEnvelope word) = 0 :=
            measure_union_null edgeBad_measure_zero hpre
          have hinnerMeas : MeasurableSet
              (edgeBad ∪ targetU ⁻¹' wordBadEnvelope word) :=
            (edgeBad_closed_nowhereDense.1.union
              ((wordBadEnvelope_closed_nowhereDense word).1.preimage
                targetU_isOpenQuotientMap.continuous)).measurableSet
          have himageMeas : MeasurableSet
              (sourceU '' (edgeBad ∪ targetU ⁻¹' wordBadEnvelope word)) := by
            simpa only [wordBadEnvelope] using
              (wordBadEnvelope_closed_nowhereDense (.U :: word)).1.measurableSet
          simpa only [wordBadEnvelope] using
            sourceU_image_null hinnerMeas himageMeas hinner
      | UInv =>
          have hpre : measureTorus (sourceU ⁻¹' wordBadEnvelope word) = 0 :=
            sourceU_quasiMeasurePreserving.preimage_null ih
          have hinner : measureTorus
              (edgeBad ∪ sourceU ⁻¹' wordBadEnvelope word) = 0 :=
            measure_union_null edgeBad_measure_zero hpre
          have hinnerMeas : MeasurableSet
              (edgeBad ∪ sourceU ⁻¹' wordBadEnvelope word) :=
            (edgeBad_closed_nowhereDense.1.union
              ((wordBadEnvelope_closed_nowhereDense word).1.preimage
                sourceU_isOpenQuotientMap.continuous)).measurableSet
          have himageMeas : MeasurableSet
              (targetU '' (edgeBad ∪ sourceU ⁻¹' wordBadEnvelope word)) := by
            simpa only [wordBadEnvelope] using
              (wordBadEnvelope_closed_nowhereDense (.UInv :: word)).1.measurableSet
          simpa only [wordBadEnvelope] using
            targetU_image_null hinnerMeas himageMeas hinner
      | C =>
          have hpre : measureTorus
              (torusCyclic ⁻¹' wordBadEnvelope word) = 0 :=
            torusCyclic_quasiMeasurePreserving.preimage_null ih
          simpa only [wordBadEnvelope] using
            measure_union_null stateBad_measure_zero hpre
      | CInv =>
          have hpre : measureTorus
              (torusCyclicInv ⁻¹' wordBadEnvelope word) = 0 :=
            torusCyclicInv_quasiMeasurePreserving.preimage_null ih
          simpa only [wordBadEnvelope] using
            measure_union_null stateBad_measure_zero hpre
      | rho =>
          have hpre : measureTorus
              (torusRho ⁻¹' wordBadEnvelope word) = 0 :=
            torusRho_quasiMeasurePreserving.preimage_null ih
          simpa only [wordBadEnvelope] using
            measure_union_null stateBad_measure_zero hpre

theorem fullyGenericEdgeBad_measure_zero :
    measureTorus fullyGenericEdgeBad = 0 := by
  apply measure_iUnion_null
  intro n
  exact (sourceU_quasiMeasurePreserving.iterate n).preimage_null edgeBad_measure_zero

theorem fullyGenericWordBad_measure_zero :
    measureTorus fullyGenericWordBad = 0 := by
  apply measure_iUnion_null
  intro n
  apply measure_iUnion_null
  intro word
  exact (sourceU_quasiMeasurePreserving.iterate n).preimage_null
    (wordBadEnvelope_measure_zero word)

theorem fullyGenericBad_measure_zero :
    measureTorus fullyGenericBad = 0 :=
  measure_union_null fullyGenericEdgeBad_measure_zero
    fullyGenericWordBad_measure_zero

theorem fullyGeneric_ae_torus :
    ∀ᵐ q ∂measureTorus, FullyGeneric q := by
  exact (measure_eq_zero_iff_ae_notMem.mp
    fullyGenericBad_measure_zero).mono fun q hq =>
      fullyGenericBad_compl_subset hq

/-! ## A measurable, conull, forward-invariant fully-generic core -/

theorem measurableSet_fullyGenericEdgeBad :
    MeasurableSet fullyGenericEdgeBad := by
  apply MeasurableSet.iUnion
  intro n
  exact edgeBad_closed_nowhereDense.1.measurableSet.preimage
    (sourceU_iterate_isOpenQuotientMap n).continuous.measurable

theorem measurableSet_fullyGenericWordBad :
    MeasurableSet fullyGenericWordBad := by
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro word
  exact (wordBadEnvelope_closed_nowhereDense word).1.measurableSet.preimage
    (sourceU_iterate_isOpenQuotientMap n).continuous.measurable

theorem measurableSet_fullyGenericBad : MeasurableSet fullyGenericBad :=
  measurableSet_fullyGenericEdgeBad.union measurableSet_fullyGenericWordBad

/-- The explicit measurable core used whenever both topology and measure are
needed.  It is slightly smaller than the extensional predicate `FullyGeneric`
because the closed word envelopes were deliberately chosen uniformly. -/
def fullyGenericCore : Set TorusPoint := fullyGenericBadᶜ

theorem measurableSet_fullyGenericCore : MeasurableSet fullyGenericCore :=
  measurableSet_fullyGenericBad.compl

theorem fullyGenericCore_compl_measure_zero :
    measureTorus fullyGenericCoreᶜ = 0 := by
  simpa [fullyGenericCore] using fullyGenericBad_measure_zero

theorem fullyGenericCore_subset :
    fullyGenericCore ⊆ {q : TorusPoint | FullyGeneric q} :=
  fullyGenericBad_compl_subset

theorem fullyGenericCore_dense : Dense fullyGenericCore := by
  simpa [fullyGenericCore] using
    (dense_of_mem_residual fullyGenericBad_isMeagre)

theorem fullyGenericCore_forward {q : TorusPoint}
    (hq : q ∈ fullyGenericCore) : sourceU q ∈ fullyGenericCore := by
  change q ∉ fullyGenericBad at hq
  change sourceU q ∉ fullyGenericBad
  intro hbad
  apply hq
  rcases hbad with hedge | hword
  · left
    rcases Set.mem_iUnion.mp hedge with ⟨n, hn⟩
    exact Set.mem_iUnion_of_mem (n + 1) (by
      simpa [Function.iterate_succ_apply] using hn)
  · right
    rcases Set.mem_iUnion.mp hword with ⟨n, hn⟩
    rcases Set.mem_iUnion.mp hn with ⟨word, hword⟩
    exact Set.mem_iUnion_of_mem (n + 1)
      (Set.mem_iUnion_of_mem word (by
        simpa [Function.iterate_succ_apply] using hword))

theorem continuous_u4ToTorusPoint : Continuous U4.toTorusPoint := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

/-- Null sets for the normalized torus measure remain null after restriction
to the article's four-point chart. -/
theorem measureU4_preimage_zero_of_measureTorus_zero
    {s : Set TorusPoint} (hs : MeasurableSet s)
    (hzero : measureTorus s = 0) :
    measureU4 (U4.toTorusPoint ⁻¹' s) = 0 := by
  have hambient : coord4Gaussian (Subtype.val '' s) = 0 :=
    (Sp4.normalizedOpenMeasure_eq_zero_iff_image coord4Gaussian torusSet
      isOpen_torusSet torusSet_nonempty hs).mp hzero
  have hpre : MeasurableSet (U4.toTorusPoint ⁻¹' s) :=
    hs.preimage continuous_u4ToTorusPoint.measurable
  apply (Sp4.normalizedOpenMeasure_eq_zero_iff_image coord4Gaussian u4Set
    isOpen_u4Set u4Set_nonempty hpre).mpr
  apply measure_mono_null (t := Subtype.val '' s)
  · rintro _ ⟨q, hq, rfl⟩
    have hqu4 : IsU4 q.1 := q.2
    exact ⟨⟨q.1, ⟨hqu4.x_ne, hqu4.y_ne⟩⟩, hq, rfl⟩
  · exact hambient

/-- The measurable fully-generic core in the actual `U4` chart. -/
def fullyGenericCoreU4 : Set U4 := U4.toTorusPoint ⁻¹' fullyGenericCore

theorem measurableSet_fullyGenericCoreU4 :
    MeasurableSet fullyGenericCoreU4 :=
  measurableSet_fullyGenericCore.preimage continuous_u4ToTorusPoint.measurable

theorem fullyGenericCoreU4_compl_measure_zero :
    measureU4 fullyGenericCoreU4ᶜ = 0 := by
  have h := measureU4_preimage_zero_of_measureTorus_zero
    measurableSet_fullyGenericBad fullyGenericBad_measure_zero
  simpa [fullyGenericCoreU4, fullyGenericCore] using h

theorem fullyGenericCoreU4_dense : Dense fullyGenericCoreU4 := by
  exact fullyGenericCore_dense.preimage u4ToTorus_isOpenEmbedding.isOpenMap

theorem fullyGenericCoreU4_subset :
    fullyGenericCoreU4 ⊆ {q : U4 | FullyGeneric q.toTorusPoint} := by
  intro q hq
  exact fullyGenericCore_subset hq

/-- The exact almost-everywhere statement on the probability space used by the
measurable-resolution part of the formalization. -/
theorem fullyGeneric_ae :
    ∀ᵐ q ∂measureU4, FullyGeneric q.toTorusPoint := by
  exact (measure_eq_zero_iff_ae_notMem.mp
    fullyGenericCoreU4_compl_measure_zero).mono fun q hq =>
      fullyGenericCoreU4_subset (by simpa using hq)

end Sp4.Pfaffian
