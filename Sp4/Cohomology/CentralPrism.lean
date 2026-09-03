import Sp4.Cohomology.MeasurableRows
import Mathlib.Topology.ContinuousMap.Algebra

/-!
# The central-element prism on homogeneous continuous cochains

This file proves the simplicial cancellation used in the central-element
annihilation argument.  The combinatorial part is first stated for arbitrary
real modules.  It is then restricted to continuous equivariant homogeneous
cochains.
-/

namespace Sp4
namespace CentralPrism

open scoped BigOperators

noncomputable section

universe uJ uV

section Combinatorics

variable {J : Type uJ} {V : Type uV}
  [AddCommGroup V] [Module ℝ V]

/-- Apply left multiplication by `z` in every coordinate. -/
def leftTuple [Mul J] (z : J) {n : ℕ} (x : FinTuple J n) : FinTuple J n :=
  fun i ↦ z * x i

@[simp]
theorem leftTuple_cons [Mul J] (z a : J) {n : ℕ} (x : FinTuple J n) :
    leftTuple z (Fin.cons a x) = Fin.cons (z * a) (leftTuple z x) := by
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl

@[simp]
theorem delete_leftTuple [Mul J] (z : J) {n : ℕ}
    (i : Fin (n + 1)) (x : FinTuple J (n + 1)) :
    FinTuple.delete i (leftTuple z x) =
      leftTuple z (FinTuple.delete i x) := by
  rfl

/-- The pointwise homogeneous deletion differential on tuples with `n`
coordinates. -/
def coboundaryEval {n : ℕ} (c : FinTuple J n → V) :
    FinTuple J (n + 1) → V :=
  fun x ↦ ∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val • c (FinTuple.delete i x)

/-- Expanding the alternating deletion sum after adjoining a first entry. -/
theorem coboundaryEval_cons {n : ℕ} (c : FinTuple J (n + 1) → V)
    (a : J) (x : FinTuple J (n + 1)) :
    coboundaryEval c (Fin.cons a x) =
      c x - coboundaryEval (fun y : FinTuple J n ↦ c (Fin.cons a y)) x := by
  rw [coboundaryEval, Fin.sum_univ_succ]
  simp only [MeasurableRows.delete_cons_zero, MeasurableRows.delete_cons_succ,
    Fin.val_zero, Fin.val_succ, pow_zero, one_smul]
  rw [coboundaryEval]
  have hterm (i : Fin (n + 1)) :
      (-1 : ℝ) ^ (i.val + 1) •
          c (Fin.cons a (FinTuple.delete i x)) =
        -((-1 : ℝ) ^ i.val •
          c (Fin.cons a (FinTuple.delete i x))) := by
    rw [pow_succ, mul_smul]
    simp
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib]
  abel

theorem coboundaryEval_add {n : ℕ} (c d : FinTuple J n → V)
    (x : FinTuple J (n + 1)) :
    coboundaryEval (fun y ↦ c y + d y) x =
      coboundaryEval c x + coboundaryEval d x := by
  simp only [coboundaryEval, smul_add, Finset.sum_add_distrib]

theorem coboundaryEval_sub {n : ℕ} (c d : FinTuple J n → V)
    (x : FinTuple J (n + 1)) :
    coboundaryEval (fun y ↦ c y - d y) x =
      coboundaryEval c x - coboundaryEval d x := by
  simp only [coboundaryEval, smul_sub, Finset.sum_sub_distrib]

theorem coboundaryEval_leftTuple [Mul J] (z : J) {n : ℕ}
    (c : FinTuple J n → V) (x : FinTuple J (n + 1)) :
    coboundaryEval (fun y ↦ c (leftTuple z y)) x =
      coboundaryEval c (leftTuple z x) := by
  simp only [coboundaryEval, delete_leftTuple]

/-- The homogeneous deletion differential squares to zero in every degree. -/
theorem coboundaryEval_sq {n : ℕ} (c : FinTuple J n → V)
    (x : FinTuple J (n + 2)) :
    coboundaryEval (coboundaryEval c) x = 0 := by
  simp only [coboundaryEval, Finset.smul_sum]
  rw [← Fintype.sum_prod_type']
  let swapPair : Fin (n + 2) × Fin (n + 1) →
      Fin (n + 2) × Fin (n + 1) :=
    fun p ↦ (p.1.succAbove p.2, p.2.predAbove p.1)
  classical
  apply Finset.sum_involution (s := Finset.univ)
    (fun p _ ↦ swapPair p)
  · rintro ⟨j, i⟩ _
    have hsign := Fin.neg_one_pow_succAbove_add_predAbove
      (R := ℝ) j i
    rw [FinTuple.delete_delete_swap x i j]
    dsimp [swapPair]
    rw [← mul_smul, ← mul_smul, ← pow_add, ← pow_add, hsign]
    simp
  · intro p _ _ hp
    exact Fin.succAbove_ne p.1 p.2 (congrArg Prod.fst hp)
  · simp
  · rintro ⟨j, i⟩ _
    apply Prod.ext
    · exact Fin.succAbove_succAbove_predAbove j i
    · exact Fin.predAbove_predAbove_succAbove j i

/-- The `i`-th simplex in the prism from the identity to simultaneous left
multiplication by `z`. -/
def prismTuple [Mul J] (z : J) : {n : ℕ} →
    Fin n → FinTuple J n → FinTuple J (n + 1)
  | 0, i, _ => Fin.elim0 i
  | n + 1, i, x =>
      Fin.cases
        (Fin.cons (x 0) (Fin.cons (z * x 0) (leftTuple z (Fin.tail x))))
        (fun j ↦ Fin.cons (x 0) (prismTuple z j (Fin.tail x))) i

@[simp]
theorem prismTuple_zero [Mul J] (z : J) {n : ℕ}
    (a : J) (x : FinTuple J n) :
    prismTuple z (0 : Fin (n + 1)) (Fin.cons a x) =
      Fin.cons a (Fin.cons (z * a) (leftTuple z x)) := by
  rfl

@[simp]
theorem prismTuple_succ [Mul J] (z : J) {n : ℕ}
    (i : Fin n) (a : J) (x : FinTuple J n) :
    prismTuple z i.succ (Fin.cons a x) =
      Fin.cons a (prismTuple z i x) := by
  rfl

/-- Alternating sum of the prism simplices. -/
def prismEval [Mul J] (z : J) {n : ℕ}
    (c : FinTuple J (n + 1) → V) : FinTuple J n → V :=
  fun x ↦ ∑ i : Fin n, (-1 : ℝ) ^ i.val • c (prismTuple z i x)

@[simp]
theorem prismEval_zero [Mul J] (z : J)
    (c : FinTuple J 1 → V) (x : FinTuple J 0) :
    prismEval z c x = 0 := by
  simp [prismEval]

/-- Recursive expansion of the prism after adjoining a first entry. -/
theorem prismEval_cons [Mul J] (z : J) {n : ℕ}
    (c : FinTuple J (n + 2) → V) (a : J) (x : FinTuple J n) :
    prismEval z c (Fin.cons a x) =
      c (Fin.cons a (Fin.cons (z * a) (leftTuple z x))) -
        prismEval z (fun y : FinTuple J (n + 1) ↦ c (Fin.cons a y)) x := by
  rw [prismEval, Fin.sum_univ_succ]
  simp only [prismTuple_zero, prismTuple_succ, Fin.val_zero, Fin.val_succ,
    pow_zero, one_smul]
  rw [prismEval]
  have hterm (i : Fin n) :
      (-1 : ℝ) ^ (i.val + 1) • c (Fin.cons a (prismTuple z i x)) =
        -((-1 : ℝ) ^ i.val • c (Fin.cons a (prismTuple z i x))) := by
    rw [pow_succ, mul_smul]
    simp
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib]
  abel

theorem prismEval_add [Mul J] (z : J) {n : ℕ}
    (c d : FinTuple J (n + 1) → V) (x : FinTuple J n) :
    prismEval z (fun y ↦ c y + d y) x =
      prismEval z c x + prismEval z d x := by
  simp only [prismEval, smul_add, Finset.sum_add_distrib]

theorem prismEval_sub [Mul J] (z : J) {n : ℕ}
    (c d : FinTuple J (n + 1) → V) (x : FinTuple J n) :
    prismEval z (fun y ↦ c y - d y) x =
      prismEval z c x - prismEval z d x := by
  simp only [prismEval, smul_sub, Finset.sum_sub_distrib]

/-- The finite simplicial cancellation underlying the central-element prism. -/
theorem coboundary_prism_add_prism_coboundary [Mul J] (z : J) :
    ∀ (q : ℕ) (c : FinTuple J (q + 1) → V)
      (x : FinTuple J (q + 1)),
      coboundaryEval (prismEval z c) x +
          prismEval z (coboundaryEval c) x =
        c (leftTuple z x) - c x := by
  intro q
  induction q with
  | zero =>
      intro c x
      rw [← Fin.cons_self_tail x]
      simp [coboundaryEval, prismEval, prismTuple,
        Fin.sum_univ_succ]
      have hdel :
          FinTuple.delete (1 : Fin 2)
              (Fin.cons (x 0)
                (Fin.cons (z * x 0) (leftTuple z (Fin.tail x)))) =
            Fin.cons (x 0) (Fin.tail x) := by
        funext i
        fin_cases i
        rfl
      rw [hdel, Fin.cons_self_tail]
      rw [show leftTuple z x =
          Fin.cons (z * x 0) (leftTuple z (Fin.tail x)) by
        funext i
        fin_cases i
        rfl]
      rw [sub_eq_add_neg]
  | succ n ih =>
      intro c x
      rw [← Fin.cons_self_tail x]
      let a : J := x 0
      let xs : FinTuple J (n + 1) := Fin.tail x
      let c₀ : FinTuple J (n + 1) → V := fun y ↦ c (Fin.cons a y)
      let c₁ : FinTuple J n → V := fun y ↦
        c (Fin.cons a (Fin.cons (z * a) y))
      have hih := ih c₀ xs
      rw [coboundaryEval_cons, prismEval_cons]
      rw [show (fun y : FinTuple J n ↦
          prismEval z c (Fin.cons a y)) =
          fun y ↦
            c₁ (leftTuple z y) - prismEval z c₀ y by
        funext y
        exact prismEval_cons z c a y]
      rw [coboundaryEval_sub]
      rw [coboundaryEval_leftTuple]
      rw [coboundaryEval_cons c a]
      rw [coboundaryEval_cons c₀ (z * a)]
      rw [show (fun y : FinTuple J (n + 2) ↦
          coboundaryEval c (Fin.cons a y)) =
          fun y ↦ c y - coboundaryEval c₀ y by
        funext y
        exact coboundaryEval_cons c a y]
      rw [prismEval_sub]
      rw [show (fun y : FinTuple J n ↦ c₀ (Fin.cons (z * a) y)) = c₁ by
        rfl]
      rw [leftTuple_cons]
      change _ = c (Fin.cons (z * a) (leftTuple z xs)) - c (Fin.cons a xs)
      change
        prismEval z c xs -
            (coboundaryEval c₁ (leftTuple z xs) -
              coboundaryEval (prismEval z c₀) xs) +
          ((c (Fin.cons (z * a) (leftTuple z xs)) -
                (c₀ (leftTuple z xs) -
                  coboundaryEval c₁ (leftTuple z xs))) -
            (prismEval z c xs -
              prismEval z (coboundaryEval c₀) xs)) = _
      have hd : coboundaryEval (prismEval z c₀) xs =
          (c₀ (leftTuple z xs) - c₀ xs) -
            prismEval z (coboundaryEval c₀) xs :=
        eq_sub_of_add_eq hih
      rw [hd]
      abel

end Combinatorics

section ContinuousCochains

variable {J : Type uJ} {V : Type uV}
  [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
  [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [Module ℝ V] [ContinuousConstSMul ℝ V]
  [DistribMulAction J V] [SMulCommClass J ℝ V]
  [ContinuousConstSMul J V]

/-- Continuous homogeneous cochains with exactly `n` group coordinates. -/
abbrev ContinuousCochain (n : ℕ) := C(FinTuple J n, V)

/-- Coordinate deletion as a continuous map. -/
def deleteContinuous (n : ℕ) (i : Fin (n + 1)) :
    C(FinTuple J (n + 1), FinTuple J n) :=
  ⟨FinTuple.delete i,
    continuous_pi fun j ↦ continuous_apply (i.succAbove j)⟩

/-- One deletion face on continuous homogeneous cochains. -/
def continuousFace (n : ℕ) (i : Fin (n + 1)) :
    ContinuousCochain (J := J) (V := V) n →ₗ[ℝ]
      ContinuousCochain (J := J) (V := V) (n + 1) where
  toFun c := c.comp (deleteContinuous n i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The continuous homogeneous deletion differential. -/
def continuousCoboundary (n : ℕ) :
    ContinuousCochain (J := J) (V := V) n →ₗ[ℝ]
      ContinuousCochain (J := J) (V := V) (n + 1) :=
  ∑ i : Fin (n + 1), (-1 : ℝ) ^ i.val • continuousFace n i

@[simp]
theorem continuousCoboundary_apply (n : ℕ)
    (c : ContinuousCochain (J := J) (V := V) n)
    (x : FinTuple J (n + 1)) :
    continuousCoboundary n c x = coboundaryEval c x := by
  simp [continuousCoboundary, continuousFace, coboundaryEval,
    deleteContinuous]

theorem continuousCoboundary_sq (n : ℕ)
    (c : ContinuousCochain (J := J) (V := V) n) :
    continuousCoboundary (n + 1) (continuousCoboundary n c) = 0 := by
  apply ContinuousMap.ext
  intro x
  simp only [continuousCoboundary_apply, ContinuousMap.zero_apply]
  rw [show (⇑(continuousCoboundary n c)) = coboundaryEval c by
    funext y
    exact continuousCoboundary_apply n c y]
  exact coboundaryEval_sq c x

/-- Every simplex in the prism varies continuously with its input tuple. -/
theorem continuous_prismTuple (z : J) :
    ∀ {n : ℕ} (i : Fin n), Continuous (prismTuple z i)
  | 0, i => Fin.elim0 i
  | n + 1, i => by
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · apply continuous_pi
        intro k
        refine Fin.cases (continuous_apply 0) (fun k ↦ ?_) k
        refine Fin.cases
          (continuous_const.mul (continuous_apply 0))
          (fun k ↦ continuous_const.mul (continuous_apply k.succ)) k
      · apply continuous_pi
        intro k
        refine Fin.cases (continuous_apply 0) (fun k ↦ ?_) k
        have htail : Continuous
            (Fin.tail : FinTuple J (n + 1) → FinTuple J n) :=
          continuous_pi fun t ↦ continuous_apply t.succ
        change Continuous fun a : FinTuple J (n + 1) ↦
          prismTuple z j (Fin.tail a) k
        exact (continuous_apply k).comp
          ((continuous_prismTuple z j).comp htail)

/-- A prism simplex as a continuous map. -/
def prismContinuous (z : J) {n : ℕ} (i : Fin n) :
    C(FinTuple J n, FinTuple J (n + 1)) :=
  ⟨prismTuple z i, continuous_prismTuple z i⟩

/-- Pullback along one prism simplex. -/
def continuousPrismFace (z : J) (n : ℕ) (i : Fin n) :
    ContinuousCochain (J := J) (V := V) (n + 1) →ₗ[ℝ]
      ContinuousCochain (J := J) (V := V) n where
  toFun c := c.comp (prismContinuous z i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The alternating continuous prism operator. -/
def continuousPrism (z : J) (n : ℕ) :
    ContinuousCochain (J := J) (V := V) (n + 1) →ₗ[ℝ]
      ContinuousCochain (J := J) (V := V) n :=
  ∑ i : Fin n, (-1 : ℝ) ^ i.val • continuousPrismFace z n i

@[simp]
theorem continuousPrism_apply (z : J) (n : ℕ)
    (c : ContinuousCochain (J := J) (V := V) (n + 1))
    (x : FinTuple J n) :
    continuousPrism z n c x = prismEval z c x := by
  simp [continuousPrism, continuousPrismFace, prismEval,
    prismContinuous]

/-- The prism identity on continuous homogeneous cochains. -/
theorem continuous_prism_identity (z : J) (q : ℕ)
    (c : ContinuousCochain (J := J) (V := V) (q + 1)) :
    continuousCoboundary q (continuousPrism z q c) +
        continuousPrism z (q + 1) (continuousCoboundary (q + 1) c) =
      ⟨fun x ↦ c (leftTuple z x) - c x,
        ((c.continuous.comp
          (continuous_pi fun i ↦ continuous_const.mul (continuous_apply i))).sub
            c.continuous)⟩ := by
  apply ContinuousMap.ext
  intro x
  simp only [ContinuousMap.add_apply, continuousCoboundary_apply,
    continuousPrism_apply]
  rw [show (⇑(continuousPrism z q c)) = prismEval z c by
    funext y
    exact continuousPrism_apply z q c y]
  rw [show (⇑(continuousCoboundary (q + 1) c)) = coboundaryEval c by
    funext y
    exact continuousCoboundary_apply (q + 1) c y]
  exact coboundary_prism_add_prism_coboundary z q c x

/-! ## Equivariant cochains -/

/-- Continuous cochains equivariant for diagonal left translation. -/
def EquivariantCochains (n : ℕ) :
    Submodule ℝ (ContinuousCochain (J := J) (V := V) n) where
  carrier := {c | ∀ (g : J) (x : FinTuple J n),
    c (leftTuple g x) = g • c x}
  zero_mem' := by simp
  add_mem' := by
    intro c d hc hd g x
    simp only [ContinuousMap.add_apply, hc g x, hd g x, smul_add]
  smul_mem' := by
    intro r c hc g x
    simp only [ContinuousMap.smul_apply, hc g x]
    exact (smul_comm g r (c x)).symm

/-- The deletion differential restricted to equivariant cochains. -/
def equivariantCoboundary (n : ℕ) :
    EquivariantCochains (J := J) (V := V) n →ₗ[ℝ]
      EquivariantCochains (J := J) (V := V) (n + 1) where
  toFun c := ⟨continuousCoboundary n c.1, by
    intro g x
    simp only [continuousCoboundary_apply]
    rw [← coboundaryEval_leftTuple]
    simp only [coboundaryEval]
    simp_rw [c.2 g]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (smul_comm g ((-1 : ℝ) ^ i.val)
      (c.1 (FinTuple.delete i x))).symm⟩
  map_add' _ _ := by
    apply Subtype.ext
    exact map_add (continuousCoboundary n) _ _
  map_smul' _ _ := by
    apply Subtype.ext
    exact map_smul (continuousCoboundary n) _ _

@[simp]
theorem equivariantCoboundary_coe (n : ℕ)
    (c : EquivariantCochains (J := J) (V := V) n) :
    (equivariantCoboundary n c).1 = continuousCoboundary n c.1 :=
  rfl

theorem equivariantCoboundary_sq (n : ℕ)
    (c : EquivariantCochains (J := J) (V := V) n) :
    equivariantCoboundary (n + 1) (equivariantCoboundary n c) = 0 := by
  apply Subtype.ext
  exact continuousCoboundary_sq n c.1

/-- Centrality in the form needed by the prism tuple calculation. -/
def IsCentral (z : J) : Prop := ∀ g : J, z * g = g * z

/-- A central prism simplex commutes with diagonal left translation. -/
theorem prismTuple_leftTuple {z : J} (hz : IsCentral z) :
    ∀ {n : ℕ} (i : Fin n) (g : J) (x : FinTuple J n),
      prismTuple z i (leftTuple g x) =
        leftTuple g (prismTuple z i x)
  | 0, i, _, _ => Fin.elim0 i
  | n + 1, i, g, x => by
      rw [← Fin.cons_self_tail x, leftTuple_cons]
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · funext k
        refine Fin.cases ?_ (fun k ↦ ?_) k
        · rfl
        · refine Fin.cases ?_ (fun k ↦ ?_) k
          · simp only [prismTuple_zero, leftTuple_cons, Fin.cons_zero,
              Fin.cons_succ, Fin.tail_cons]
            rw [← mul_assoc, hz g, mul_assoc]
          · simp only [prismTuple_zero, leftTuple_cons, Fin.cons_succ,
              Fin.tail_cons]
            change z * (g * Fin.tail x k) = g * (z * Fin.tail x k)
            rw [← mul_assoc, hz g, mul_assoc]
      · simp only [prismTuple_succ, leftTuple_cons, Fin.tail_cons]
        congr 1
        exact prismTuple_leftTuple hz j g (Fin.tail x)

/-- The prism restricts to equivariant cochains when `z` is central. -/
def equivariantPrism {z : J} (hz : IsCentral z) (n : ℕ) :
    EquivariantCochains (J := J) (V := V) (n + 1) →ₗ[ℝ]
      EquivariantCochains (J := J) (V := V) n where
  toFun c := ⟨continuousPrism z n c.1, by
    intro g x
    simp only [continuousPrism_apply, prismEval]
    simp_rw [prismTuple_leftTuple hz, c.2 g]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (smul_comm g ((-1 : ℝ) ^ i.val)
      (c.1 (prismTuple z i x))).symm⟩
  map_add' _ _ := by
    apply Subtype.ext
    exact map_add (continuousPrism z n) _ _
  map_smul' _ _ := by
    apply Subtype.ext
    exact map_smul (continuousPrism z n) _ _

/-- Pointwise application of a continuous linear coefficient map. -/
def mapCoefficients (A : V →L[ℝ] V) (n : ℕ) :
    ContinuousCochain (J := J) (V := V) n →ₗ[ℝ]
      ContinuousCochain (J := J) (V := V) n where
  toFun c := ⟨fun x ↦ A (c x), A.continuous.comp c.continuous⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
theorem mapCoefficients_apply (A : V →L[ℝ] V) (n : ℕ)
    (c : ContinuousCochain (J := J) (V := V) n) (x : FinTuple J n) :
    mapCoefficients A n c x = A (c x) :=
  rfl

theorem mapCoefficients_coboundary (A : V →L[ℝ] V) (n : ℕ)
    (c : ContinuousCochain (J := J) (V := V) n) :
    mapCoefficients A (n + 1) (continuousCoboundary n c) =
      continuousCoboundary n (mapCoefficients A n c) := by
  apply ContinuousMap.ext
  intro x
  simp only [mapCoefficients_apply, continuousCoboundary_apply,
    coboundaryEval, map_sum, map_smul]

/-- The coefficient endomorphism `v ↦ z • v - v`. -/
def centralDifference (z : J) : V →ₗ[ℝ] V where
  toFun v := z • v - v
  map_add' _ _ := by
    simp only [smul_add]
    abel
  map_smul' r v := by
    rw [smul_sub, smul_comm z r]
    simp only [RingHom.id_apply]

theorem centralDifference_commutes {z : J} (hz : IsCentral z)
    (g : J) (v : V) :
    centralDifference z (g • v) = g • centralDifference z v := by
  simp only [centralDifference, LinearMap.coe_mk, AddHom.coe_mk,
    smul_sub, smul_smul]
  rw [hz g]

/-- If `z-1` is a continuous linear automorphism on coefficients, its inverse
is automatically equivariant because `z` is central. -/
theorem centralDifference_symm_commutes {z : J} (hz : IsCentral z)
    (A : V ≃L[ℝ] V) (hA : A.toLinearMap = centralDifference z)
    (g : J) (v : V) :
    A.symm (g • v) = g • A.symm v := by
  apply A.injective
  rw [A.apply_symm_apply]
  change g • v = A.toLinearMap (g • A.symm v)
  rw [hA, centralDifference_commutes hz, ← hA]
  simp

/-- Coefficientwise application of `(z-1)⁻¹` preserves equivariance. -/
def inverseDifferenceCochain {z : J} (hz : IsCentral z)
    (A : V ≃L[ℝ] V) (hA : A.toLinearMap = centralDifference z)
    (n : ℕ) :
    EquivariantCochains (J := J) (V := V) n →ₗ[ℝ]
      EquivariantCochains (J := J) (V := V) n where
  toFun c := ⟨mapCoefficients A.symm.toContinuousLinearMap n c.1, by
    intro g x
    simp only [mapCoefficients_apply, c.2 g]
    exact centralDifference_symm_commutes hz A hA g (c.1 x)⟩
  map_add' _ _ := by
    apply Subtype.ext
    exact map_add (mapCoefficients A.symm.toContinuousLinearMap n) _ _
  map_smul' _ _ := by
    apply Subtype.ext
    exact map_smul (mapCoefficients A.symm.toContinuousLinearMap n) _ _

/-- **Central-element annihilation, cochain form.**  In every degree, a
continuous equivariant cocycle has the displayed continuous equivariant
primitive whenever `z-1` is a continuous coefficient automorphism. -/
theorem exists_equivariant_primitive_of_central_difference
    {z : J} (hz : IsCentral z)
    (A : V ≃L[ℝ] V) (hA : A.toLinearMap = centralDifference z)
    (q : ℕ) (c : EquivariantCochains (J := J) (V := V) (q + 1))
    (hc : equivariantCoboundary (q + 1) c = 0) :
    ∃ b : EquivariantCochains (J := J) (V := V) q,
      equivariantCoboundary q b = c := by
  let c' := inverseDifferenceCochain hz A hA (q + 1) c
  let b := equivariantPrism hz q c'
  refine ⟨b, ?_⟩
  apply Subtype.ext
  have hc' : continuousCoboundary (q + 1) c'.1 = 0 := by
    change continuousCoboundary (q + 1)
      (mapCoefficients A.symm.toContinuousLinearMap (q + 1) c.1) = 0
    rw [← mapCoefficients_coboundary]
    have hcco : continuousCoboundary (q + 1) c.1 = 0 := by
      exact congrArg Subtype.val hc
    rw [hcco, map_zero]
  have hpr := continuous_prism_identity z q c'.1
  rw [hc', map_zero, add_zero] at hpr
  rw [equivariantCoboundary_coe]
  change continuousCoboundary q (continuousPrism z q c'.1) = c.1
  rw [hpr]
  apply ContinuousMap.ext
  intro x
  change c'.1 (leftTuple z x) - c'.1 x = c.1 x
  rw [c'.2 z x]
  change centralDifference z (A.symm (c.1 x)) = c.1 x
  rw [← hA]
  exact A.apply_symm_apply (c.1 x)

/-! ## The cohomology quotient -/

/-- Degree-`q` continuous homogeneous equivariant cocycles. -/
def ContinuousCocycles (q : ℕ) :
    Submodule ℝ (EquivariantCochains (J := J) (V := V) (q + 1)) :=
  LinearMap.ker (equivariantCoboundary (q + 1))

instance continuousCocyclesAddCommGroup (q : ℕ) :
    AddCommGroup (ContinuousCocycles (J := J) (V := V) q) := by
  exact @Submodule.addCommGroup ℝ
    (EquivariantCochains (J := J) (V := V) (q + 1)) inferInstance
    inferInstance inferInstance (ContinuousCocycles (J := J) (V := V) q)

/-- A degree-`q` coboundary, regarded as a cocycle. -/
def boundaryToContinuousCocycles (q : ℕ) :
    EquivariantCochains (J := J) (V := V) q →ₗ[ℝ]
      ContinuousCocycles (J := J) (V := V) q :=
  (equivariantCoboundary q).codRestrict
    (ContinuousCocycles (J := J) (V := V) q)
    (fun b ↦ equivariantCoboundary_sq q b)

/-- Degree-`q` continuous homogeneous equivariant boundaries. -/
def ContinuousBoundaries (q : ℕ) :
    Submodule ℝ (ContinuousCocycles (J := J) (V := V) q) :=
  LinearMap.range (boundaryToContinuousCocycles q)

/-- Continuous cohomology in the homogeneous continuous-cochain model. -/
abbrev ContinuousCohomology (q : ℕ) :=
  (ContinuousCocycles (J := J) (V := V) q : Type _) ⧸
    ContinuousBoundaries (J := J) (V := V) q

/-- **Central-element annihilation.**  If a central element acts with
`z - 1` a continuous linear automorphism on the coefficient module, then its
continuous cohomology vanishes in every degree. -/
theorem continuousCohomology_eq_zero_of_central_difference
    {z : J} (hz : IsCentral z)
    (A : V ≃L[ℝ] V) (hA : A.toLinearMap = centralDifference z)
    (q : ℕ) (a : ContinuousCohomology (J := J) (V := V) q) :
    a = 0 := by
  obtain ⟨c, rfl⟩ :=
    (ContinuousBoundaries (J := J) (V := V) q).mkQ_surjective a
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change c ∈ LinearMap.range (boundaryToContinuousCocycles q)
  obtain ⟨b, hb⟩ :=
    exists_equivariant_primitive_of_central_difference hz A hA q c.1 c.2
  refine ⟨b, ?_⟩
  apply Subtype.ext
  exact hb

end ContinuousCochains

end
end CentralPrism
end Sp4
