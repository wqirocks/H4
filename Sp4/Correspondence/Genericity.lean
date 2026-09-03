import Sp4.Correspondence.Word

/-!
# Topological genericity of all finite correspondence lifts

This file proves the density part of the fully-generic package directly from
the explicit double covers.  No algebraic-geometric dimension interface is
used: the elementary bad loci are zero sets of nonzero analytic polynomials,
and bad loci for words are propagated through the two quotient maps.
-/

namespace Sp4
namespace Pfaffian

noncomputable section

open Filter
open scoped Topology

abbrev ComplexNonzero := {z : ℂ // z ≠ 0}

def torusNonzeroProdEquiv : TorusPoint ≃ ComplexNonzero × ComplexNonzero where
  toFun q := (⟨q.1.x, q.2.x_ne⟩, ⟨q.1.y, q.2.y_ne⟩)
  invFun q := ⟨⟨q.1.1, q.2.1⟩, ⟨q.1.2, q.2.2⟩⟩
  left_inv q := by apply Subtype.ext; rfl
  right_inv q := by rcases q with ⟨x, y⟩; rfl

def torusNonzeroProdHomeomorph :
    TorusPoint ≃ₜ ComplexNonzero × ComplexNonzero where
  toEquiv := torusNonzeroProdEquiv
  continuous_toFun := by
    apply Continuous.prodMk
    · exact (continuous_coord4_x.comp continuous_subtype_val).subtype_mk _
    · exact (continuous_coord4_y.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
    exact Continuous.prodMk
      (continuous_subtype_val.comp continuous_fst)
      (continuous_subtype_val.comp continuous_snd)

def complexNonzeroNegHomeomorph : ComplexNonzero ≃ₜ ComplexNonzero where
  toFun z := ⟨-z.1, neg_ne_zero.mpr z.2⟩
  invFun z := ⟨-z.1, neg_ne_zero.mpr z.2⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  continuous_toFun := (continuous_neg.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_neg.comp continuous_subtype_val).subtype_mk _

def sourceProd (q : ComplexNonzero × ComplexNonzero) :
    ComplexNonzero × ComplexNonzero :=
  (complexNonzeroNegHomeomorph q.1,
    complexNonzeroNegHomeomorph
      ⟨q.2.1 ^ 2, pow_ne_zero 2 q.2.2⟩)

theorem sourceProd_isOpenQuotientMap : IsOpenQuotientMap sourceProd := by
  have hpow : IsOpenQuotientMap
      (fun z : ComplexNonzero =>
        (⟨z.1 ^ 2, pow_ne_zero 2 z.2⟩ : ComplexNonzero)) := by
    simpa only using Complex.isOpenQuotientMap_pow_compl_zero 2
  have hneg := complexNonzeroNegHomeomorph.isOpenQuotientMap
  have hsecond := hneg.comp hpow
  convert hneg.prodMap hsecond using 1
  funext q
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    rfl

theorem sourceU_isOpenQuotientMap : IsOpenQuotientMap sourceU := by
  have h := torusNonzeroProdHomeomorph.symm.isOpenQuotientMap.comp
    (sourceProd_isOpenQuotientMap.comp
      torusNonzeroProdHomeomorph.isOpenQuotientMap)
  convert h using 1
  funext q
  apply Subtype.ext
  apply Coord4.ext <;> rfl

def targetTwist (q : TorusPoint) : TorusPoint :=
  ⟨⟨-(q.1.x * q.1.y), q.1.y⟩,
    ⟨neg_ne_zero.mpr (mul_ne_zero q.2.x_ne q.2.y_ne), q.2.y_ne⟩⟩

def targetUntwist (q : TorusPoint) : TorusPoint :=
  ⟨⟨-(q.1.x / q.1.y), q.1.y⟩,
    ⟨neg_ne_zero.mpr (div_ne_zero q.2.x_ne q.2.y_ne), q.2.y_ne⟩⟩

def targetTwistHomeomorph : TorusPoint ≃ₜ TorusPoint where
  toFun := targetTwist
  invFun := targetUntwist
  left_inv q := by
    apply Subtype.ext
    apply Coord4.ext
    · change -(-(q.1.x * q.1.y) / q.1.y) = q.1.x
      field_simp [q.2.y_ne]
    · rfl
  right_inv q := by
    apply Subtype.ext
    apply Coord4.ext
    · change -(-(q.1.x / q.1.y) * q.1.y) = q.1.x
      field_simp [q.2.y_ne]
    · rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
    apply Continuous.prodMk
    · change Continuous fun q : TorusPoint => -(q.1.x * q.1.y)
      fun_prop
    · change Continuous fun q : TorusPoint => q.1.y
      fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
    apply Continuous.prodMk
    · change Continuous fun q : TorusPoint => -(q.1.x / q.1.y)
      exact continuous_neg.comp
        ((continuous_coord4_x.comp continuous_subtype_val).div₀
          (continuous_coord4_y.comp continuous_subtype_val)
          (fun q => q.2.y_ne))
    · change Continuous fun q : TorusPoint => q.1.y
      fun_prop

theorem sourceU_targetTwist (q : TorusPoint) :
    sourceU (targetTwist q) = targetU q := by
  apply Subtype.ext
  apply Coord4.ext <;> simp [sourceU, sourceUCoord, targetU, targetUCoord,
    targetTwist]

theorem targetU_isOpenQuotientMap : IsOpenQuotientMap targetU := by
  have h := sourceU_isOpenQuotientMap.comp
    targetTwistHomeomorph.isOpenQuotientMap
  convert h using 1
  funext q
  exact (sourceU_targetTwist q).symm

def sourceDeck (q : TorusPoint) : TorusPoint :=
  ⟨⟨q.1.x, -q.1.y⟩, ⟨q.2.x_ne, neg_ne_zero.mpr q.2.y_ne⟩⟩

def targetDeck (q : TorusPoint) : TorusPoint :=
  ⟨⟨-q.1.x, -q.1.y⟩,
    ⟨neg_ne_zero.mpr q.2.x_ne, neg_ne_zero.mpr q.2.y_ne⟩⟩

def sourceDeckHomeomorph : TorusPoint ≃ₜ TorusPoint where
  toFun := sourceDeck
  invFun := sourceDeck
  left_inv q := by apply Subtype.ext; apply Coord4.ext <;> simp [sourceDeck]
  right_inv q := by apply Subtype.ext; apply Coord4.ext <;> simp [sourceDeck]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
    apply Continuous.prodMk <;> fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
    apply Continuous.prodMk <;> fun_prop

def targetDeckHomeomorph : TorusPoint ≃ₜ TorusPoint where
  toFun := targetDeck
  invFun := targetDeck
  left_inv q := by apply Subtype.ext; apply Coord4.ext <;> simp [targetDeck]
  right_inv q := by apply Subtype.ext; apply Coord4.ext <;> simp [targetDeck]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
    apply Continuous.prodMk <;> fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
    apply Continuous.prodMk <;> fun_prop

theorem sourceU_eq_sourceU_iff (p q : TorusPoint) :
    sourceU q = sourceU p ↔ q = p ∨ q = sourceDeck p := by
  constructor
  · intro h
    have hx := congrArg (fun r : TorusPoint => r.1.x) h
    have hy := congrArg (fun r : TorusPoint => r.1.y) h
    change -q.1.x = -p.1.x at hx
    change -(q.1.y ^ 2) = -(p.1.y ^ 2) at hy
    have hsq : q.1.y ^ 2 = p.1.y ^ 2 := by linear_combination -hy
    rcases eq_or_eq_neg_of_sq_eq_sq q.1.y p.1.y hsq with hsame | hneg
    · left
      apply Subtype.ext
      apply Coord4.ext
      · linear_combination -hx
      · exact hsame
    · right
      apply Subtype.ext
      apply Coord4.ext
      · change q.1.x = p.1.x
        linear_combination -hx
      · exact hneg
  · rintro (rfl | rfl)
    · rfl
    · apply Subtype.ext
      apply Coord4.ext <;> simp [sourceU, sourceUCoord, sourceDeck]

theorem targetU_eq_targetU_iff (p q : TorusPoint) :
    targetU q = targetU p ↔ q = p ∨ q = targetDeck p := by
  constructor
  · intro h
    have hx := congrArg (fun r : TorusPoint => r.1.x) h
    have hy := congrArg (fun r : TorusPoint => r.1.y) h
    change q.1.x * q.1.y = p.1.x * p.1.y at hx
    change -(q.1.y ^ 2) = -(p.1.y ^ 2) at hy
    have hsq : q.1.y ^ 2 = p.1.y ^ 2 := by linear_combination -hy
    rcases eq_or_eq_neg_of_sq_eq_sq q.1.y p.1.y hsq with hsame | hneg
    · left
      apply Subtype.ext
      apply Coord4.ext
      · rw [hsame] at hx
        exact (mul_right_cancel₀ p.2.y_ne hx)
      · exact hsame
    · right
      apply Subtype.ext
      apply Coord4.ext
      · change q.1.x = -p.1.x
        rw [hneg] at hx
        apply (mul_right_cancel₀ p.2.y_ne)
        linear_combination -hx
      · exact hneg
  · rintro (rfl | rfl)
    · rfl
    · apply Subtype.ext
      apply Coord4.ext <;> simp [targetU, targetUCoord, targetDeck] <;> ring

/-! ## Analytic base bad loci -/

def deltaPair (q : ℂ × ℂ) : ℂ := 1 - q.1 + q.2

def deltaUPair (q : ℂ × ℂ) : ℂ := deltaU q.1 q.2

theorem analyticOnNhd_deltaPair :
    AnalyticOnNhd ℂ deltaPair Set.univ := by
  intro q _
  have hx : AnalyticAt ℂ (fun q : ℂ × ℂ => q.1) q := analyticAt_fst
  have hy : AnalyticAt ℂ (fun q : ℂ × ℂ => q.2) q := analyticAt_snd
  change AnalyticAt ℂ (fun q : ℂ × ℂ => 1 - q.1 + q.2) q
  exact (analyticAt_const.sub hx).add hy

theorem analyticOnNhd_deltaUPair :
    AnalyticOnNhd ℂ deltaUPair Set.univ := by
  intro q _
  have hx : AnalyticAt ℂ (fun q : ℂ × ℂ => q.1) q := analyticAt_fst
  have hy : AnalyticAt ℂ (fun q : ℂ × ℂ => q.2) q := analyticAt_snd
  have hc (c : ℂ) : AnalyticAt ℂ (fun _ : ℂ × ℂ => c) q := analyticAt_const
  have hxy := hx.mul hy
  have h1 := hy.sub (hc 2)
  have h2 := (hc 2).mul hy |>.sub (hc 1)
  have h3 := hx.sub hy |>.sub (hc 1)
  have h4 := hx.sub (hy.pow 2) |>.add (hc 1)
  have h5 := (hc 1).sub (hx.mul hy) |>.sub (hy.pow 2)
  change AnalyticAt ℂ (fun q : ℂ × ℂ =>
    q.1 * q.2 * (q.2 - 2) * (2 * q.2 - 1) * (q.1 - q.2 - 1) *
      (q.1 - q.2 ^ 2 + 1) * (1 - q.1 * q.2 - q.2 ^ 2)) q
  exact (((((hxy.mul h1).mul h2).mul h3).mul h4).mul h5)

theorem analytic_zeroSet_closed_nowhereDense
    (g : (ℂ × ℂ) → ℂ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (hne : ∃ q, g q ≠ 0) :
    IsClosed {q | g q = 0} ∧ IsNowhereDense {q | g q = 0} := by
  have hclosed : IsClosed {q | g q = 0} :=
    isClosed_eq hg.continuous continuous_const
  refine ⟨hclosed, hclosed.isNowhereDense_iff.mpr ?_⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  have hevent : g =ᶠ[𝓝 q] 0 := by
    filter_upwards [isOpen_interior.mem_nhds hq] with x hx
    simpa using interior_subset hx
  have hall : g = 0 := hg.eq_of_eventuallyEq analyticOnNhd_const hevent
  obtain ⟨w, hw⟩ := hne
  exact hw (congrFun hall w)

theorem deltaPair_zero_closed_nowhereDense :
    IsClosed {q | deltaPair q = 0} ∧ IsNowhereDense {q | deltaPair q = 0} := by
  apply analytic_zeroSet_closed_nowhereDense deltaPair analyticOnNhd_deltaPair
  exact ⟨(0, 0), by norm_num [deltaPair]⟩

theorem deltaUPair_zero_closed_nowhereDense :
    IsClosed {q | deltaUPair q = 0} ∧ IsNowhereDense {q | deltaUPair q = 0} := by
  apply analytic_zeroSet_closed_nowhereDense deltaUPair analyticOnNhd_deltaUPair
  exact ⟨(2, 3), by norm_num [deltaUPair, deltaU]⟩

def torusPairMap (q : TorusPoint) : ℂ × ℂ := (q.1.x, q.1.y)

theorem torusPairMap_isOpenEmbedding : Topology.IsOpenEmbedding torusPairMap := by
  have hval : Topology.IsOpenEmbedding ((↑) : ComplexNonzero → ℂ) :=
    isOpen_ne.isOpenEmbedding_subtypeVal
  have hprod := hval.prodMap hval
  have h := hprod.comp torusNonzeroProdHomeomorph.isOpenEmbedding
  convert h using 1
  funext q
  rfl

theorem closed_nowhereDense_preimage_isOpenEmbedding
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {g : X → Y} (hg : Topology.IsOpenEmbedding g) {s : Set Y}
    (hs : IsClosed s ∧ IsNowhereDense s) :
    IsClosed (g ⁻¹' s) ∧ IsNowhereDense (g ⁻¹' s) := by
  have hclosed : IsClosed (g ⁻¹' s) := hs.1.preimage hg.continuous
  have hdense : Dense (g ⁻¹' sᶜ) :=
    (isClosed_isNowhereDense_iff_compl.mp hs).2.preimage hg.isOpenMap
  refine isClosed_isNowhereDense_iff_compl.mpr ⟨?_, ?_⟩
  · simpa only [Set.preimage_compl] using hclosed.isOpen_compl
  · simpa only [Set.preimage_compl] using hdense

def stateBad : Set TorusPoint := {q | delta4 q.1 = 0}

def edgeBad : Set TorusPoint := {q | deltaU q.1.x q.1.y = 0}

theorem stateBad_closed_nowhereDense :
    IsClosed stateBad ∧ IsNowhereDense stateBad := by
  have h := closed_nowhereDense_preimage_isOpenEmbedding
    torusPairMap_isOpenEmbedding deltaPair_zero_closed_nowhereDense
  simpa [stateBad, deltaPair, torusPairMap, delta4] using h

theorem edgeBad_closed_nowhereDense :
    IsClosed edgeBad ∧ IsNowhereDense edgeBad := by
  have h := closed_nowhereDense_preimage_isOpenEmbedding
    torusPairMap_isOpenEmbedding deltaUPair_zero_closed_nowhereDense
  simpa [edgeBad, deltaUPair, torusPairMap] using h

/-! ## Elementary propagation lemmas -/

theorem closed_nowhereDense_union {X : Type*} [TopologicalSpace X]
    {s t : Set X} (hs : IsClosed s ∧ IsNowhereDense s)
    (ht : IsClosed t ∧ IsNowhereDense t) :
    IsClosed (s ∪ t) ∧ IsNowhereDense (s ∪ t) := by
  have hs' := isClosed_isNowhereDense_iff_compl.mp hs
  have ht' := isClosed_isNowhereDense_iff_compl.mp ht
  apply isClosed_isNowhereDense_iff_compl.mpr
  have hcompl : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := by ext x; simp
  rw [hcompl]
  exact ⟨hs'.1.inter ht'.1,
    hs'.2.inter_of_isOpen_left ht'.2 hs'.1⟩

theorem closed_nowhereDense_preimage_continuous_open
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {g : X → Y} (hc : Continuous g) (ho : IsOpenMap g) {s : Set Y}
    (hs : IsClosed s ∧ IsNowhereDense s) :
    IsClosed (g ⁻¹' s) ∧ IsNowhereDense (g ⁻¹' s) := by
  have hclosed : IsClosed (g ⁻¹' s) := hs.1.preimage hc
  have hdense : Dense (g ⁻¹' sᶜ) :=
    (isClosed_isNowhereDense_iff_compl.mp hs).2.preimage ho
  apply isClosed_isNowhereDense_iff_compl.mpr
  exact ⟨by simpa only [Set.preimage_compl] using hclosed.isOpen_compl,
    by simpa only [Set.preimage_compl] using hdense⟩

/-- A closed nowhere-dense set remains so after passing through a two-sheeted
open quotient whose fibers are an identity/deck-transformation pair. -/
theorem closed_nowhereDense_image_doubleCover
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsOpenQuotientMap f) (τ : X ≃ₜ X)
    (hfiber : ∀ p q, f q = f p ↔ q = p ∨ q = τ p)
    {s : Set X} (hs : IsClosed s ∧ IsNowhereDense s) :
    IsClosed (f '' s) ∧ IsNowhereDense (f '' s) := by
  have hpre : f ⁻¹' (f '' s) = s ∪ τ '' s := by
    ext x
    constructor
    · rintro ⟨y, hy, hfy⟩
      rcases (hfiber y x).mp hfy.symm with rfl | hx
      · exact Or.inl hy
      · exact Or.inr ⟨y, hy, hx.symm⟩
    · rintro (hx | ⟨y, hy, rfl⟩)
      · exact ⟨x, hx, rfl⟩
      · exact ⟨y, hy, ((hfiber y (τ y)).mpr (Or.inr rfl)).symm⟩
  have hτ : IsClosed (τ '' s) ∧ IsNowhereDense (τ '' s) :=
    ⟨τ.isClosed_image.mpr hs.1, τ.isInducing.isNowhereDense_image hs.2⟩
  have hsat : IsClosed (s ∪ τ '' s) ∧ IsNowhereDense (s ∪ τ '' s) :=
    closed_nowhereDense_union hs hτ
  have himage : IsClosed (f '' s) :=
    hf.isQuotientMap.isCoinducing.isClosed_preimage.mp (hpre.symm ▸ hsat.1)
  have hdensePre : Dense (f ⁻¹' (f '' s)ᶜ) := by
    rw [Set.preimage_compl, hpre]
    exact (isClosed_isNowhereDense_iff_compl.mp hsat).2
  have hdense : Dense (f '' s)ᶜ := hf.dense_preimage_iff.mp hdensePre
  exact isClosed_isNowhereDense_iff_compl.mpr
    ⟨himage.isOpen_compl, hdense⟩

/-! ## The deterministic correspondence letters are homeomorphisms -/

def torusCyclicHomeomorph : TorusPoint ≃ₜ TorusPoint where
  toFun := torusCyclic
  invFun := torusCyclicInv
  left_inv := torusCyclicInv_cyclic
  right_inv := torusCyclic_cyclicInv
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
    apply Continuous.prodMk
    · change Continuous fun q : TorusPoint => -1 / q.1.y
      exact continuous_const.div₀
        (continuous_coord4_y.comp continuous_subtype_val)
        (fun q => q.2.y_ne)
    · change Continuous fun q : TorusPoint => -q.1.x / q.1.y
      exact (continuous_neg.comp
        (continuous_coord4_x.comp continuous_subtype_val)).div₀
          (continuous_coord4_y.comp continuous_subtype_val)
          (fun q => q.2.y_ne)
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
    apply Continuous.prodMk
    · change Continuous fun q : TorusPoint => q.1.y / q.1.x
      exact (continuous_coord4_y.comp continuous_subtype_val).div₀
        (continuous_coord4_x.comp continuous_subtype_val)
        (fun q => q.2.x_ne)
    · change Continuous fun q : TorusPoint => -1 / q.1.x
      exact continuous_const.div₀
        (continuous_coord4_x.comp continuous_subtype_val)
        (fun q => q.2.x_ne)

def torusRhoHomeomorph : TorusPoint ≃ₜ TorusPoint where
  toFun := torusRho
  invFun := torusRho
  left_inv := torusRho_rho
  right_inv := torusRho_rho
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
    apply Continuous.prodMk <;> fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
    apply Continuous.prodMk <;> fun_prop

/-! ## A closed nowhere-dense envelope for every finite word -/

/-- This recursively defined set contains every initial state admitting at
least one inadmissible lift of the indicated word.  For a `U`-letter we retain
both branches by taking the image under the appropriate double cover. -/
def wordBadEnvelope : List CorrLetter → Set TorusPoint
  | [] => stateBad
  | .U :: word =>
      sourceU '' (edgeBad ∪ targetU ⁻¹' wordBadEnvelope word)
  | .UInv :: word =>
      targetU '' (edgeBad ∪ sourceU ⁻¹' wordBadEnvelope word)
  | .C :: word =>
      stateBad ∪ torusCyclic ⁻¹' wordBadEnvelope word
  | .CInv :: word =>
      stateBad ∪ torusCyclicInv ⁻¹' wordBadEnvelope word
  | .rho :: word =>
      stateBad ∪ torusRho ⁻¹' wordBadEnvelope word

theorem wordBadEnvelope_closed_nowhereDense (word : List CorrLetter) :
    IsClosed (wordBadEnvelope word) ∧
      IsNowhereDense (wordBadEnvelope word) := by
  induction word with
  | nil => exact stateBad_closed_nowhereDense
  | cons letter word ih =>
      cases letter with
      | U =>
          apply closed_nowhereDense_image_doubleCover
            sourceU_isOpenQuotientMap sourceDeckHomeomorph
          · intro p q
            change sourceU q = sourceU p ↔
              q = p ∨ q = sourceDeck p
            exact sourceU_eq_sourceU_iff p q
          · exact closed_nowhereDense_union edgeBad_closed_nowhereDense
              (closed_nowhereDense_preimage_continuous_open
                targetU_isOpenQuotientMap.continuous
                targetU_isOpenQuotientMap.isOpenMap ih)
      | UInv =>
          apply closed_nowhereDense_image_doubleCover
            targetU_isOpenQuotientMap targetDeckHomeomorph
          · intro p q
            change targetU q = targetU p ↔
              q = p ∨ q = targetDeck p
            exact targetU_eq_targetU_iff p q
          · exact closed_nowhereDense_union edgeBad_closed_nowhereDense
              (closed_nowhereDense_preimage_continuous_open
                sourceU_isOpenQuotientMap.continuous
                sourceU_isOpenQuotientMap.isOpenMap ih)
      | C =>
          exact closed_nowhereDense_union stateBad_closed_nowhereDense
            (closed_nowhereDense_preimage_continuous_open
              torusCyclicHomeomorph.continuous
              torusCyclicHomeomorph.isOpenMap ih)
      | CInv =>
          exact closed_nowhereDense_union stateBad_closed_nowhereDense
            (closed_nowhereDense_preimage_continuous_open
              torusCyclicHomeomorph.symm.continuous
              torusCyclicHomeomorph.symm.isOpenMap ih)
      | rho =>
          exact closed_nowhereDense_union stateBad_closed_nowhereDense
            (closed_nowhereDense_preimage_continuous_open
              torusRhoHomeomorph.continuous
              torusRhoHomeomorph.isOpenMap ih)

theorem wordBadSource_subset_wordBadEnvelope (word : List CorrLetter) :
    wordBadSource word ⊆ wordBadEnvelope word := by
  intro x hx
  induction word generalizing x with
  | nil =>
      rcases hx with ⟨y, e, he⟩
      cases e with
      | nil q =>
          simpa [wordBadEnvelope, stateBad, WordLift.Admissible,
            TorusPoint.IsGeneric] using he
  | cons letter word ih =>
      rcases hx with ⟨z, e, he⟩
      cases e with
      | cons head tail =>
          cases head with
          | U p =>
              refine ⟨p, ?_, rfl⟩
              by_cases hp : EdgeAdmissible p
              · right
                exact ih ⟨z, tail, fun ht => he ⟨hp, ht⟩⟩
              · left
                simpa [edgeBad, EdgeAdmissible] using hp
          | UInv p =>
              refine ⟨p, ?_, rfl⟩
              by_cases hp : EdgeAdmissible p
              · right
                exact ih ⟨z, tail, fun ht => he ⟨hp, ht⟩⟩
              · left
                simpa [edgeBad, EdgeAdmissible] using hp
          | C _ =>
              by_cases hq : TorusPoint.IsGeneric x
              · right
                exact ih ⟨z, tail, fun ht => he ⟨hq, ht⟩⟩
              · left
                simpa [stateBad, TorusPoint.IsGeneric] using hq
          | CInv _ =>
              by_cases hq : TorusPoint.IsGeneric x
              · right
                exact ih ⟨z, tail, fun ht => he ⟨hq, ht⟩⟩
              · left
                simpa [stateBad, TorusPoint.IsGeneric] using hq
          | rho _ =>
              by_cases hq : TorusPoint.IsGeneric x
              · right
                exact ih ⟨z, tail, fun ht => he ⟨hq, ht⟩⟩
              · left
                simpa [stateBad, TorusPoint.IsGeneric] using hq

theorem wordBadSource_nowhereDense (word : List CorrLetter) :
    IsNowhereDense (wordBadSource word) :=
  IsNowhereDense.mono (wordBadSource_subset_wordBadEnvelope word)
    (wordBadEnvelope_closed_nowhereDense word).2

/-! ## The residual fully-generic locus -/

theorem sourceU_iterate_isOpenQuotientMap (n : ℕ) :
    IsOpenQuotientMap (sourceU^[n]) := by
  induction n with
  | zero => simpa only [Function.iterate_zero] using
      (IsOpenQuotientMap.id : IsOpenQuotientMap (id : TorusPoint → TorusPoint))
  | succ n ih =>
      simpa only [Function.iterate_succ] using
        ih.comp sourceU_isOpenQuotientMap

def fullyGenericEdgeBad : Set TorusPoint :=
  ⋃ n : ℕ, (sourceU^[n]) ⁻¹' edgeBad

def fullyGenericWordBad : Set TorusPoint :=
  ⋃ n : ℕ, ⋃ word : List CorrLetter,
    (sourceU^[n]) ⁻¹' wordBadEnvelope word

def fullyGenericBad : Set TorusPoint :=
  fullyGenericEdgeBad ∪ fullyGenericWordBad

theorem fullyGenericEdgeBad_isMeagre : IsMeagre fullyGenericEdgeBad := by
  apply isMeagre_iUnion
  intro n
  exact (closed_nowhereDense_preimage_continuous_open
    (sourceU_iterate_isOpenQuotientMap n).continuous
    (sourceU_iterate_isOpenQuotientMap n).isOpenMap
    edgeBad_closed_nowhereDense).2.isMeagre

theorem fullyGenericWordBad_isMeagre : IsMeagre fullyGenericWordBad := by
  apply isMeagre_iUnion
  intro n
  apply isMeagre_iUnion
  intro word
  exact (closed_nowhereDense_preimage_continuous_open
    (sourceU_iterate_isOpenQuotientMap n).continuous
    (sourceU_iterate_isOpenQuotientMap n).isOpenMap
    (wordBadEnvelope_closed_nowhereDense word)).2.isMeagre

theorem fullyGenericBad_isMeagre : IsMeagre fullyGenericBad :=
  fullyGenericEdgeBad_isMeagre.union fullyGenericWordBad_isMeagre

theorem fullyGenericBad_compl_subset :
    fullyGenericBadᶜ ⊆ {x : TorusPoint | FullyGeneric x} := by
  intro x hx
  intro n
  constructor
  · have hn : (sourceU^[n]) x ∉ edgeBad := by
      intro hbad
      apply hx
      left
      exact Set.mem_iUnion_of_mem n hbad
    simpa [edgeBad, EdgeAdmissible] using hn
  · intro word y e
    apply every_lift_admissible_of_not_mem_wordBadSource word
      ((sourceU^[n]) x)
    intro hbad
    have henv : (sourceU^[n]) x ∈ wordBadEnvelope word :=
      wordBadSource_subset_wordBadEnvelope word hbad
    apply hx
    right
    exact Set.mem_iUnion_of_mem n (Set.mem_iUnion_of_mem word henv)

instance torusPointBaireSpace : BaireSpace TorusPoint :=
  torusPairMap_isOpenEmbedding.baireSpace

theorem fullyGeneric_dense_torus :
    Dense {x : TorusPoint | FullyGeneric x} := by
  apply (dense_of_mem_residual fullyGenericBad_isMeagre).mono
  exact fullyGenericBad_compl_subset

def genericTorusSet : Set TorusPoint := {q | q.IsGeneric}

theorem genericTorusSet_isOpen : IsOpen genericTorusSet := by
  have heq : genericTorusSet = stateBadᶜ := by
    ext q
    simp [genericTorusSet, stateBad, TorusPoint.IsGeneric]
  rw [heq]
  exact stateBad_closed_nowhereDense.1.isOpen_compl

def u4GenericTorusHomeomorph : U4 ≃ₜ {q : TorusPoint // q ∈ genericTorusSet} where
  toFun q := ⟨q.toTorusPoint, q.2.delta_ne⟩
  invFun q := q.1.toU4 q.2
  left_inv q := by apply Subtype.ext; rfl
  right_inv q := by apply Subtype.ext; rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

theorem u4ToTorus_isOpenEmbedding :
    Topology.IsOpenEmbedding U4.toTorusPoint := by
  have hval : Topology.IsOpenEmbedding
      ((↑) : {q : TorusPoint // q ∈ genericTorusSet} → TorusPoint) :=
    genericTorusSet_isOpen.isOpenEmbedding_subtypeVal
  have h := hval.comp u4GenericTorusHomeomorph.isOpenEmbedding
  convert h using 1
  funext q
  rfl

/-- The exact density statement consumed by the compact-return argument. -/
theorem fullyGeneric_dense :
    Dense {q : U4 | FullyGeneric q.toTorusPoint} := by
  change Dense (U4.toTorusPoint ⁻¹'
    {x : TorusPoint | FullyGeneric x})
  exact fullyGeneric_dense_torus.preimage
    u4ToTorus_isOpenEmbedding.isOpenMap

end
end Pfaffian
end Sp4
