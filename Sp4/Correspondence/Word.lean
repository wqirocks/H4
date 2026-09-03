import Sp4.Pfaffian.Certificates

/-!
# Finite correspondence words and lifts

This file builds the elementary two-valued correspondence on the complex
two-torus with all denominator and genericity conditions carried by subtypes.
-/

namespace Sp4
namespace Pfaffian

noncomputable section

open scoped Matrix

/-- A point of `(ℂˣ)²`, represented without choosing unit structures. -/
structure IsTorusPoint (q : Coord4) : Prop where
  x_ne : q.x ≠ 0
  y_ne : q.y ≠ 0

abbrev TorusPoint := {q : Coord4 // IsTorusPoint q}

def U4.toTorusPoint (q : U4) : TorusPoint :=
  ⟨q.1, ⟨q.2.x_ne, q.2.y_ne⟩⟩

def TorusPoint.IsGeneric (q : TorusPoint) : Prop := delta4 q.1 ≠ 0

def TorusPoint.toU4 (q : TorusPoint) (hq : q.IsGeneric) : U4 :=
  ⟨q.1, ⟨q.2.x_ne, q.2.y_ne, hq⟩⟩

@[simp]
theorem TorusPoint.toU4_toTorusPoint (q : U4) :
    (q.toTorusPoint.toU4 q.2.delta_ne) = q := by
  rfl

/-- Source and target of the elementary degree-two correspondence. -/
def sourceUCoord (p : Coord4) : Coord4 := ⟨-p.x, -(p.y ^ 2)⟩
def targetUCoord (p : Coord4) : Coord4 := ⟨p.x * p.y, -(p.y ^ 2)⟩

theorem sourceUCoord_mem (p : TorusPoint) : IsTorusPoint (sourceUCoord p.1) := by
  exact ⟨neg_ne_zero.mpr p.2.x_ne, neg_ne_zero.mpr (pow_ne_zero 2 p.2.y_ne)⟩

theorem targetUCoord_mem (p : TorusPoint) : IsTorusPoint (targetUCoord p.1) := by
  exact ⟨mul_ne_zero p.2.x_ne p.2.y_ne,
    neg_ne_zero.mpr (pow_ne_zero 2 p.2.y_ne)⟩

def sourceU (p : TorusPoint) : TorusPoint := ⟨sourceUCoord p.1, sourceUCoord_mem p⟩
def targetU (p : TorusPoint) : TorusPoint := ⟨targetUCoord p.1, targetUCoord_mem p⟩

private theorem exists_nonzero_sq_eq_neg (y : ℂ) (hy : y ≠ 0) :
    ∃ b : ℂ, b ≠ 0 ∧ b ^ 2 = -y := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (-y) (by norm_num : 0 < 2)
  have hbpow : b ^ 2 ≠ 0 := by
    rw [hb]
    exact neg_ne_zero.mpr hy
  exact ⟨b, fun hb0 => hbpow (by simp [hb0]), hb⟩

def sourceLift (q : TorusPoint) (b : ℂ) (hb : b ≠ 0) : TorusPoint :=
  ⟨⟨-q.1.x, b⟩, ⟨neg_ne_zero.mpr q.2.x_ne, hb⟩⟩

def targetLift (q : TorusPoint) (b : ℂ) (hb : b ≠ 0) : TorusPoint :=
  ⟨⟨q.1.x / b, b⟩, ⟨div_ne_zero q.2.x_ne hb, hb⟩⟩

theorem sourceU_sourceLift (q : TorusPoint) (b : ℂ) (hb : b ≠ 0)
    (hroot : b ^ 2 = -q.1.y) : sourceU (sourceLift q b hb) = q := by
  apply Subtype.ext
  apply Coord4.ext
  · simp [sourceU, sourceUCoord, sourceLift]
  · change -(b ^ 2) = q.1.y
    rw [hroot]
    simp

theorem targetU_targetLift (q : TorusPoint) (b : ℂ) (hb : b ≠ 0)
    (hroot : b ^ 2 = -q.1.y) : targetU (targetLift q b hb) = q := by
  apply Subtype.ext
  apply Coord4.ext
  · change q.1.x / b * b = q.1.x
    field_simp [hb]
  · change -(b ^ 2) = q.1.y
    rw [hroot]
    simp

theorem sourceLift_ne_neg (q : TorusPoint) (b : ℂ) (hb : b ≠ 0) :
    sourceLift q b hb ≠ sourceLift q (-b) (neg_ne_zero.mpr hb) := by
  intro h
  have hy := congrArg (fun p : TorusPoint => p.1.y) h
  change b = -b at hy
  apply hb
  linear_combination (1 / 2 : ℂ) * hy

theorem targetLift_ne_neg (q : TorusPoint) (b : ℂ) (hb : b ≠ 0) :
    targetLift q b hb ≠ targetLift q (-b) (neg_ne_zero.mpr hb) := by
  intro h
  have hy := congrArg (fun p : TorusPoint => p.1.y) h
  change b = -b at hy
  apply hb
  linear_combination (1 / 2 : ℂ) * hy

/-- Every source fiber consists of exactly the two square-root lifts. -/
theorem sourceU_fiber_two (q : TorusPoint) :
    ∃ p₁ p₂ : TorusPoint, p₁ ≠ p₂ ∧ sourceU p₁ = q ∧ sourceU p₂ = q ∧
      ∀ p : TorusPoint, sourceU p = q → p = p₁ ∨ p = p₂ := by
  obtain ⟨b, hb, hroot⟩ := exists_nonzero_sq_eq_neg q.1.y q.2.y_ne
  let p₁ := sourceLift q b hb
  let p₂ := sourceLift q (-b) (neg_ne_zero.mpr hb)
  refine ⟨p₁, p₂, sourceLift_ne_neg q b hb,
    sourceU_sourceLift q b hb hroot, ?_, ?_⟩
  · apply sourceU_sourceLift
    simpa using hroot
  · intro p hp
    have hx := congrArg (fun z : TorusPoint => z.1.x) hp
    have hy := congrArg (fun z : TorusPoint => z.1.y) hp
    change -p.1.x = q.1.x at hx
    change -(p.1.y ^ 2) = q.1.y at hy
    have hxs : p.1.x = -q.1.x := by linear_combination -hx
    have hys : p.1.y ^ 2 = b ^ 2 := by linear_combination -hy - hroot
    rcases eq_or_eq_neg_of_sq_eq_sq p.1.y b hys with hpb | hpb
    · left
      apply Subtype.ext
      apply Coord4.ext
      · exact hxs
      · exact hpb
    · right
      apply Subtype.ext
      apply Coord4.ext
      · exact hxs
      · exact hpb

/-- Every target fiber consists of exactly the two square-root lifts. -/
theorem targetU_fiber_two (q : TorusPoint) :
    ∃ p₁ p₂ : TorusPoint, p₁ ≠ p₂ ∧ targetU p₁ = q ∧ targetU p₂ = q ∧
      ∀ p : TorusPoint, targetU p = q → p = p₁ ∨ p = p₂ := by
  obtain ⟨b, hb, hroot⟩ := exists_nonzero_sq_eq_neg q.1.y q.2.y_ne
  let p₁ := targetLift q b hb
  let p₂ := targetLift q (-b) (neg_ne_zero.mpr hb)
  refine ⟨p₁, p₂, targetLift_ne_neg q b hb,
    targetU_targetLift q b hb hroot, ?_, ?_⟩
  · apply targetU_targetLift
    simpa using hroot
  · intro p hp
    have hx := congrArg (fun z : TorusPoint => z.1.x) hp
    have hy := congrArg (fun z : TorusPoint => z.1.y) hp
    change p.1.x * p.1.y = q.1.x at hx
    change -(p.1.y ^ 2) = q.1.y at hy
    have hys : p.1.y ^ 2 = b ^ 2 := by linear_combination -hy - hroot
    rcases eq_or_eq_neg_of_sq_eq_sq p.1.y b hys with hpb | hpb
    · left
      apply Subtype.ext
      apply Coord4.ext
      · change p.1.x = q.1.x / b
        apply (eq_div_iff hb).2
        simpa [hpb] using hx
      · exact hpb
    · right
      apply Subtype.ext
      apply Coord4.ext
      · change p.1.x = q.1.x / (-b)
        apply (eq_div_iff (neg_ne_zero.mpr hb)).2
        simpa [hpb] using hx
      · exact hpb

theorem sourceU_surjective : Function.Surjective sourceU := by
  intro q
  obtain ⟨p, _, _, hp, _, _⟩ := sourceU_fiber_two q
  exact ⟨p, hp⟩

theorem targetU_surjective : Function.Surjective targetU := by
  intro q
  obtain ⟨p, _, _, hp, _, _⟩ := targetU_fiber_two q
  exact ⟨p, hp⟩

/-- The open part of the elementary correspondence used by the proof. -/
def EdgeAdmissible (p : TorusPoint) : Prop := deltaU p.1.x p.1.y ≠ 0
abbrev UEdge := {p : TorusPoint // EdgeAdmissible p}

structure EdgeFactors (p : UEdge) : Prop where
  b_sub_two_ne : p.1.1.y - 2 ≠ 0
  two_b_sub_one_ne : 2 * p.1.1.y - 1 ≠ 0
  a_sub_b_sub_one_ne : p.1.1.x - p.1.1.y - 1 ≠ 0
  a_sub_b_sq_add_one_ne : p.1.1.x - p.1.1.y ^ 2 + 1 ≠ 0
  one_sub_ab_sub_b_sq_ne : 1 - p.1.1.x * p.1.1.y - p.1.1.y ^ 2 ≠ 0

theorem edgeFactors (p : UEdge) : EdgeFactors p := by
  have h := p.2
  change p.1.1.x * p.1.1.y * (p.1.1.y - 2) * (2 * p.1.1.y - 1) *
    (p.1.1.x - p.1.1.y - 1) * (p.1.1.x - p.1.1.y ^ 2 + 1) *
      (1 - p.1.1.x * p.1.1.y - p.1.1.y ^ 2) ≠ 0 at h
  rcases mul_ne_zero_iff.mp h with ⟨h, hlast⟩
  rcases mul_ne_zero_iff.mp h with ⟨h, hab2⟩
  rcases mul_ne_zero_iff.mp h with ⟨h, hab1⟩
  rcases mul_ne_zero_iff.mp h with ⟨h, h2b⟩
  rcases mul_ne_zero_iff.mp h with ⟨_, hb2⟩
  exact ⟨hb2, h2b, hab1, hab2, hlast⟩

theorem edgeBase_generic (p : UEdge) : p.1.IsGeneric := by
  have hf := (edgeFactors p).a_sub_b_sub_one_ne
  change 1 - p.1.1.x + p.1.1.y ≠ 0
  rw [show 1 - p.1.1.x + p.1.1.y =
    -(p.1.1.x - p.1.1.y - 1) by ring]
  exact neg_ne_zero.mpr hf

theorem edgeSource_generic (p : UEdge) : (sourceU p.1).IsGeneric := by
  change 1 - (-p.1.1.x) + (-(p.1.1.y ^ 2)) ≠ 0
  rw [show 1 - (-p.1.1.x) + (-(p.1.1.y ^ 2)) =
    p.1.1.x - p.1.1.y ^ 2 + 1 by ring]
  exact (edgeFactors p).a_sub_b_sq_add_one_ne

theorem edgeTarget_generic (p : UEdge) : (targetU p.1).IsGeneric := by
  change 1 - p.1.1.x * p.1.1.y + (-(p.1.1.y ^ 2)) ≠ 0
  rw [show 1 - p.1.1.x * p.1.1.y + (-(p.1.1.y ^ 2)) =
    1 - p.1.1.x * p.1.1.y - p.1.1.y ^ 2 by ring]
  exact (edgeFactors p).one_sub_ab_sub_b_sq_ne

def edgeBase (p : UEdge) : U4 := p.1.toU4 (edgeBase_generic p)
def edgeSource (p : UEdge) : U4 := (sourceU p.1).toU4 (edgeSource_generic p)
def edgeTarget (p : UEdge) : U4 := (targetU p.1).toU4 (edgeTarget_generic p)

theorem edgePhi1_mem (p : UEdge) : IsU5 (Phi1Coord p.1.1) := by
  have hf := edgeFactors p
  refine ⟨p.1.2.x_ne, neg_ne_zero.mpr p.1.2.x_ne, p.1.2.y_ne,
    neg_ne_zero.mpr (pow_ne_zero 2 p.1.2.y_ne),
    neg_ne_zero.mpr (mul_ne_zero p.1.2.x_ne p.1.2.y_ne), ?_, ?_, ?_, ?_, ?_⟩
  · rw [p0_Phi1Coord]
    exact mul_ne_zero (mul_ne_zero p.1.2.x_ne p.1.2.y_ne) hf.b_sub_two_ne
  · rw [p1_Phi1Coord]
    exact mul_ne_zero (neg_ne_zero.mpr p.1.2.y_ne) hf.a_sub_b_sub_one_ne
  · rw [p2_Phi1Coord]
    exact mul_ne_zero (neg_ne_zero.mpr p.1.2.x_ne) hf.b_sub_two_ne
  · simpa using hf.a_sub_b_sq_add_one_ne
  · rw [show p4 (Phi1Coord p.1.1) = -(p.1.1.x - p.1.1.y - 1) by
      rw [p4_Phi1Coord]
      ring]
    exact neg_ne_zero.mpr hf.a_sub_b_sub_one_ne

theorem edgePhi2_mem (p : UEdge) : IsU5 (Phi2Coord p.1.1) := by
  have hf := edgeFactors p
  refine ⟨p.1.2.x_ne, mul_ne_zero p.1.2.x_ne p.1.2.y_ne,
    p.1.2.y_ne, neg_ne_zero.mpr (pow_ne_zero 2 p.1.2.y_ne),
    neg_ne_zero.mpr (mul_ne_zero p.1.2.x_ne p.1.2.y_ne), ?_, ?_, ?_, ?_, ?_⟩
  · rw [p0_Phi2Coord]
    exact mul_ne_zero (mul_ne_zero p.1.2.x_ne p.1.2.y_ne) hf.two_b_sub_one_ne
  · rw [p1_Phi2Coord]
    exact mul_ne_zero (neg_ne_zero.mpr p.1.2.y_ne) hf.a_sub_b_sub_one_ne
  · rw [p2_Phi2Coord]
    exact mul_ne_zero (neg_ne_zero.mpr p.1.2.x_ne) hf.two_b_sub_one_ne
  · simpa using hf.one_sub_ab_sub_b_sq_ne
  · rw [show p4 (Phi2Coord p.1.1) = -(p.1.1.x - p.1.1.y - 1) by
      rw [p4_Phi2Coord]
      ring]
    exact neg_ne_zero.mpr hf.a_sub_b_sub_one_ne

def edgeAdm1 (p : UEdge) : Adm1 := ⟨edgeBase p, edgePhi1_mem p⟩
def edgeAdm2 (p : UEdge) : Adm2 := ⟨edgeBase p, edgePhi2_mem p⟩

@[simp]
theorem T1_edgeAdm1 (p : UEdge) : T1 (edgeAdm1 p) = edgeSource p := by
  apply Subtype.ext
  rfl

@[simp]
theorem T2_edgeAdm2 (p : UEdge) : T2 (edgeAdm2 p) = edgeTarget p := by
  apply Subtype.ext
  rfl

/-- The same-level oscillation estimate, proved by subtracting the two exact
defect identities at the common edge parameter. -/
theorem sameLevelOscillation (f : U4 → ℝ) (hf : PointAlt f) (M : ℝ)
    (hD : ∀ q : U5, |D f q| ≤ M) (p : UEdge) :
    |f (edgeSource p) - f (edgeTarget p)| ≤ 2 * M := by
  have h1 := defect_dilation_one f hf (edgeAdm1 p)
  have h2 := defect_dilation_two f hf (edgeAdm2 p)
  have hb1 : base1 (edgeAdm1 p) = edgeBase p := rfl
  have hb2 : base2 (edgeAdm2 p) = edgeBase p := rfl
  rw [hb1, T1_edgeAdm1] at h1
  rw [hb2, T2_edgeAdm2] at h2
  have heq : f (edgeSource p) - f (edgeTarget p) =
      D f (phi2 (edgeAdm2 p)) - D f (phi1 (edgeAdm1 p)) := by
    linarith
  rw [heq]
  calc
    |D f (phi2 (edgeAdm2 p)) - D f (phi1 (edgeAdm1 p))| ≤
        |D f (phi2 (edgeAdm2 p))| + |D f (phi1 (edgeAdm1 p))| := abs_sub _ _
    _ ≤ M + M := add_le_add (hD _) (hD _)
    _ = 2 * M := by ring

theorem sameLevelOscillation_reverse (f : U4 → ℝ) (hf : PointAlt f) (M : ℝ)
    (hD : ∀ q : U5, |D f q| ≤ M) (p : UEdge) :
    |f (edgeTarget p) - f (edgeSource p)| ≤ 2 * M := by
  simpa [abs_sub_comm] using sameLevelOscillation f hf M hD p

/-! ## Graph letters and lifted words -/

theorem cyclicCoord_torus_mem (q : TorusPoint) : IsTorusPoint (cyclicCoord q.1) := by
  exact ⟨div_ne_zero (neg_ne_zero.mpr one_ne_zero) q.2.y_ne,
    div_ne_zero (neg_ne_zero.mpr q.2.x_ne) q.2.y_ne⟩

theorem cyclicSqCoord_torus_mem (q : TorusPoint) : IsTorusPoint (cyclicSqCoord q.1) := by
  exact ⟨div_ne_zero q.2.y_ne q.2.x_ne,
    div_ne_zero (neg_ne_zero.mpr one_ne_zero) q.2.x_ne⟩

theorem rhoCoord_torus_mem (q : TorusPoint) : IsTorusPoint (rhoCoord q.1) := by
  exact ⟨neg_ne_zero.mpr q.2.y_ne, neg_ne_zero.mpr q.2.x_ne⟩

def torusCyclic (q : TorusPoint) : TorusPoint :=
  ⟨cyclicCoord q.1, cyclicCoord_torus_mem q⟩

def torusCyclicInv (q : TorusPoint) : TorusPoint :=
  ⟨cyclicSqCoord q.1, cyclicSqCoord_torus_mem q⟩

def torusRho (q : TorusPoint) : TorusPoint :=
  ⟨rhoCoord q.1, rhoCoord_torus_mem q⟩

@[simp]
theorem torusCyclicInv_cyclic (q : TorusPoint) :
    torusCyclicInv (torusCyclic q) = q := by
  apply Subtype.ext
  apply Coord4.ext <;>
    simp [torusCyclicInv, torusCyclic, cyclicSqCoord, cyclicCoord] <;>
    field_simp [q.2.x_ne, q.2.y_ne]

@[simp]
theorem torusCyclic_cyclicInv (q : TorusPoint) :
    torusCyclic (torusCyclicInv q) = q := by
  apply Subtype.ext
  apply Coord4.ext <;>
    simp [torusCyclicInv, torusCyclic, cyclicSqCoord, cyclicCoord] <;>
    field_simp [q.2.x_ne, q.2.y_ne]

@[simp]
theorem torusRho_rho (q : TorusPoint) : torusRho (torusRho q) = q := by
  apply Subtype.ext
  apply Coord4.ext <;> simp [torusRho, rhoCoord]

theorem torusCyclic_generic_iff (q : TorusPoint) :
    (torusCyclic q).IsGeneric ↔ q.IsGeneric := by
  change delta4 (cyclicCoord q.1) ≠ 0 ↔ delta4 q.1 ≠ 0
  rw [show delta4 (cyclicCoord q.1) = delta4 q.1 / q.1.y by
    dsimp [delta4, cyclicCoord]
    field_simp [q.2.y_ne]
    ring]
  exact div_ne_zero_iff.trans (and_iff_left q.2.y_ne)

theorem torusCyclicInv_generic_iff (q : TorusPoint) :
    (torusCyclicInv q).IsGeneric ↔ q.IsGeneric := by
  change delta4 (cyclicSqCoord q.1) ≠ 0 ↔ delta4 q.1 ≠ 0
  rw [show delta4 (cyclicSqCoord q.1) = -delta4 q.1 / q.1.x by
    dsimp [delta4, cyclicSqCoord]
    field_simp [q.2.x_ne]
    ring]
  simp [q.2.x_ne]

theorem torusRho_generic_iff (q : TorusPoint) :
    (torusRho q).IsGeneric ↔ q.IsGeneric := by
  change delta4 (rhoCoord q.1) ≠ 0 ↔ delta4 q.1 ≠ 0
  rw [show delta4 (rhoCoord q.1) = delta4 q.1 by
    dsimp [delta4, rhoCoord]
    ring]

/-- The list stores letters in execution order: its head acts first. -/
inductive CorrLetter where
  | U
  | UInv
  | C
  | CInv
  | rho
deriving DecidableEq

instance : Fintype CorrLetter where
  elems := {.U, .UInv, .C, .CInv, .rho}
  complete letter := by cases letter <;> simp

/-- One lifted letter.  A `U` letter remembers its square-root parameter. -/
inductive LetterStep : CorrLetter → TorusPoint → TorusPoint → Type
  | U (p : TorusPoint) : LetterStep .U (sourceU p) (targetU p)
  | UInv (p : TorusPoint) : LetterStep .UInv (targetU p) (sourceU p)
  | C (q : TorusPoint) : LetterStep .C q (torusCyclic q)
  | CInv (q : TorusPoint) : LetterStep .CInv q (torusCyclicInv q)
  | rho (q : TorusPoint) : LetterStep .rho q (torusRho q)

def LetterStep.Admissible :
    {letter : CorrLetter} → {x y : TorusPoint} → LetterStep letter x y → Prop
  | .U, _, _, .U p => EdgeAdmissible p
  | .UInv, _, _, .UInv p => EdgeAdmissible p
  | .C, _, _, .C q => q.IsGeneric
  | .CInv, _, _, .CInv q => q.IsGeneric
  | .rho, _, _, .rho q => q.IsGeneric

theorem LetterStep.source_generic {letter : CorrLetter} {x y : TorusPoint}
    (e : LetterStep letter x y) (he : e.Admissible) : x.IsGeneric := by
  cases e with
  | U p => exact edgeSource_generic ⟨p, he⟩
  | UInv p => exact edgeTarget_generic ⟨p, he⟩
  | C q => exact he
  | CInv q => exact he
  | rho q => exact he

theorem LetterStep.target_generic {letter : CorrLetter} {x y : TorusPoint}
    (e : LetterStep letter x y) (he : e.Admissible) : y.IsGeneric := by
  cases e with
  | U p => exact edgeTarget_generic ⟨p, he⟩
  | UInv p => exact edgeSource_generic ⟨p, he⟩
  | C _ => exact (torusCyclic_generic_iff _).2 he
  | CInv _ => exact (torusCyclicInv_generic_iff _).2 he
  | rho _ => exact (torusRho_generic_iff _).2 he

/-- A lift contains every intermediate state and every correspondence branch. -/
inductive WordLift : List CorrLetter → TorusPoint → TorusPoint → Type
  | nil (q : TorusPoint) : WordLift [] q q
  | cons {letter : CorrLetter} {word : List CorrLetter}
      {x y z : TorusPoint} (head : LetterStep letter x y)
      (tail : WordLift word y z) : WordLift (letter :: word) x z

def WordLift.Admissible :
    {word : List CorrLetter} → {x y : TorusPoint} → WordLift word x y → Prop
  | [], _, _, .nil q => q.IsGeneric
  | _ :: _, _, _, .cons head tail => head.Admissible ∧ tail.Admissible

theorem WordLift.initial_generic {word : List CorrLetter} {x y : TorusPoint}
    (e : WordLift word x y) (he : e.Admissible) : x.IsGeneric := by
  cases e with
  | nil q => exact he
  | cons head tail => exact head.source_generic he.1

theorem WordLift.terminal_generic {word : List CorrLetter} {x y : TorusPoint}
    (e : WordLift word x y) (he : e.Admissible) : y.IsGeneric := by
  induction e with
  | nil q => exact he
  | cons head tail ih => exact ih he.2

theorem exists_letterStep (letter : CorrLetter) (x : TorusPoint) :
    ∃ y : TorusPoint, Nonempty (LetterStep letter x y) := by
  cases letter with
  | U =>
      obtain ⟨p, hp⟩ := sourceU_surjective x
      exact ⟨targetU p, ⟨hp ▸ LetterStep.U p⟩⟩
  | UInv =>
      obtain ⟨p, hp⟩ := targetU_surjective x
      exact ⟨sourceU p, ⟨hp ▸ LetterStep.UInv p⟩⟩
  | C => exact ⟨torusCyclic x, ⟨LetterStep.C x⟩⟩
  | CInv => exact ⟨torusCyclicInv x, ⟨LetterStep.CInv x⟩⟩
  | rho => exact ⟨torusRho x, ⟨LetterStep.rho x⟩⟩

theorem exists_wordLift (word : List CorrLetter) (x : TorusPoint) :
    ∃ y : TorusPoint, Nonempty (WordLift word x y) := by
  induction word generalizing x with
  | nil => exact ⟨x, ⟨WordLift.nil x⟩⟩
  | cons letter word ih =>
      obtain ⟨y, ⟨head⟩⟩ := exists_letterStep letter x
      obtain ⟨z, ⟨tail⟩⟩ := ih y
      exact ⟨z, ⟨WordLift.cons head tail⟩⟩

/-- Concatenate two lifted words whose intermediate states agree. -/
def WordLift.append {word₁ word₂ : List CorrLetter} {x y z : TorusPoint}
    (e₁ : WordLift word₁ x y) (e₂ : WordLift word₂ y z) :
    WordLift (word₁ ++ word₂) x z := by
  induction e₁ with
  | nil _ => exact e₂
  | cons head tail ih => exact WordLift.cons head (ih e₂)

/-- Admissibility of a concatenated lift implies admissibility of its first
piece.  In the empty-word case this uses genericity of the second lift's
initial state. -/
theorem WordLift.append_left_admissible
    {word₁ word₂ : List CorrLetter} {x y z : TorusPoint}
    (e₁ : WordLift word₁ x y) (e₂ : WordLift word₂ y z)
    (he : (e₁.append e₂).Admissible) : e₁.Admissible := by
  induction e₁ with
  | nil q => exact e₂.initial_generic he
  | cons head tail ih =>
      exact ⟨he.1, ih e₂ he.2⟩

/-- Admissibility of a concatenated lift implies admissibility of its second
piece. -/
theorem WordLift.append_right_admissible
    {word₁ word₂ : List CorrLetter} {x y z : TorusPoint}
    (e₁ : WordLift word₁ x y) (e₂ : WordLift word₂ y z)
    (he : (e₁.append e₂).Admissible) : e₂.Admissible := by
  induction e₁ with
  | nil _ => exact he
  | cons head tail ih => exact ih e₂ he.2

def letterSign : CorrLetter → ℝ
  | .U | .UInv | .C | .CInv => 1
  | .rho => -1

def letterUCount : CorrLetter → ℕ
  | .U | .UInv => 1
  | .C | .CInv | .rho => 0

theorem torusCyclic_toU4 (q : TorusPoint) (hq : q.IsGeneric) :
    (torusCyclic q).toU4 ((torusCyclic_generic_iff q).2 hq) =
      cyclic (q.toU4 hq) := by
  apply Subtype.ext
  rfl

theorem torusCyclicInv_toU4 (q : TorusPoint) (hq : q.IsGeneric) :
    (torusCyclicInv q).toU4 ((torusCyclicInv_generic_iff q).2 hq) =
      cyclicSq (q.toU4 hq) := by
  apply Subtype.ext
  rfl

theorem torusRho_toU4 (q : TorusPoint) (hq : q.IsGeneric) :
    (torusRho q).toU4 ((torusRho_generic_iff q).2 hq) = rho (q.toU4 hq) := by
  apply Subtype.ext
  rfl

theorem LetterStep.value_oscillation {letter : CorrLetter} {x y : TorusPoint}
    (e : LetterStep letter x y) (he : e.Admissible)
    (f : U4 → ℝ) (hf : PointAlt f) (M : ℝ)
    (hD : ∀ q : U5, |D f q| ≤ M) :
    |f (y.toU4 (e.target_generic he)) -
        letterSign letter * f (x.toU4 (e.source_generic he))| ≤
      2 * M * letterUCount letter := by
  cases e with
  | U p =>
      simpa [letterSign, letterUCount, edgeSource, edgeTarget] using
        sameLevelOscillation_reverse f hf M hD ⟨p, he⟩
  | UInv p =>
      simpa [letterSign, letterUCount, edgeSource, edgeTarget] using
        sameLevelOscillation f hf M hD ⟨p, he⟩
  | C _ =>
      rw [torusCyclic_toU4 _ he, hf.cyclic]
      simp [letterSign, letterUCount]
  | CInv _ =>
      rw [torusCyclicInv_toU4 _ he, hf.cyclicSq]
      simp [letterSign, letterUCount]
  | rho _ =>
      rw [torusRho_toU4 _ he, hf.rho]
      simp [letterSign, letterUCount]

def wordSign : List CorrLetter → ℝ
  | [] => 1
  | letter :: word => wordSign word * letterSign letter

def wordUCount : List CorrLetter → ℕ
  | [] => 0
  | letter :: word => wordUCount word + letterUCount letter

@[simp]
theorem abs_letterSign (letter : CorrLetter) : |letterSign letter| = 1 := by
  cases letter <;> simp [letterSign]

@[simp]
theorem abs_wordSign (word : List CorrLetter) : |wordSign word| = 1 := by
  induction word with
  | nil => simp [wordSign]
  | cons letter word ih => simp [wordSign, abs_mul, ih]

/-- Oscillation accumulates linearly in the number of correspondence letters;
graph symmetries have zero cost and `rho` only changes the sign. -/
theorem WordLift.value_oscillation {word : List CorrLetter} {x y : TorusPoint}
    (e : WordLift word x y) (he : e.Admissible)
    (f : U4 → ℝ) (hf : PointAlt f) (M : ℝ)
    (hD : ∀ q : U5, |D f q| ≤ M) :
    |f (y.toU4 (e.terminal_generic he)) -
        wordSign word * f (x.toU4 (e.initial_generic he))| ≤
      2 * M * (wordUCount word : ℝ) := by
  induction e with
  | nil q => simp [wordSign, wordUCount]
  | @cons letter word x y z head tail ih =>
      rcases he with ⟨hheadAdm, htailAdm⟩
      have hhead := head.value_oscillation hheadAdm f hf M hD
      have htail := ih htailAdm
      let A := f (z.toU4 (tail.terminal_generic htailAdm))
      let B := f (y.toU4 (head.target_generic hheadAdm))
      let C := f (x.toU4 (head.source_generic hheadAdm))
      have hEq :
          f (z.toU4 ((WordLift.cons head tail).terminal_generic
            ⟨hheadAdm, htailAdm⟩)) = A := rfl
      have hMid :
          f (y.toU4 (tail.initial_generic htailAdm)) = B := by
        rfl
      have hStart :
          f (x.toU4 ((WordLift.cons head tail).initial_generic
            ⟨hheadAdm, htailAdm⟩)) = C := rfl
      rw [hEq, hStart]
      change |A - wordSign (letter :: word) * C| ≤
        2 * M * (wordUCount (letter :: word) : ℝ)
      change |A - wordSign word * letterSign letter * C| ≤ _
      calc
        |A - wordSign word * letterSign letter * C| =
            |(A - wordSign word * B) +
              wordSign word * (B - letterSign letter * C)| := by
                congr 1
                ring
        _ ≤ |A - wordSign word * B| +
            |wordSign word * (B - letterSign letter * C)| := by
              simpa [Real.norm_eq_abs] using
                norm_add_le (A - wordSign word * B)
                  (wordSign word * (B - letterSign letter * C))
        _ = |A - wordSign word * B| +
            |B - letterSign letter * C| := by
              rw [abs_mul, abs_wordSign]
              ring
        _ ≤ 2 * M * (wordUCount word : ℝ) +
            2 * M * (letterUCount letter : ℝ) := by
              apply add_le_add
              · simpa [A, B, hMid] using htail
              · simpa [B, C] using hhead
        _ = 2 * M * (wordUCount (letter :: word) : ℝ) := by
              simp [wordUCount]
              ring

/-! ## Universal bad loci and the fully generic predicate -/

/-- The bad source locus quantifies over all branches, not merely over a
chosen lift. -/
def wordBadSource (word : List CorrLetter) : Set TorusPoint :=
  {x | ∃ y : TorusPoint, ∃ e : WordLift word x y, ¬e.Admissible}

theorem every_lift_admissible_of_not_mem_wordBadSource
    (word : List CorrLetter) (x : TorusPoint)
    (hx : x ∉ wordBadSource word) {y : TorusPoint}
    (e : WordLift word x y) : e.Admissible := by
  by_contra he
  exact hx ⟨y, e, he⟩

/-- This is the exact universal property consumed by compact return.  Its
measure-theoretic largeness is a separate theorem, so no branch choice is
hidden in the definition. -/
def FullyGeneric (x : TorusPoint) : Prop :=
  ∀ n : ℕ,
    EdgeAdmissible ((sourceU^[n]) x) ∧
      ∀ (word : List CorrLetter) (y : TorusPoint)
        (e : WordLift word ((sourceU^[n]) x) y), e.Admissible

theorem FullyGeneric.edgeAdmissible_iterate {x : TorusPoint}
    (hx : FullyGeneric x) (n : ℕ) : EdgeAdmissible ((sourceU^[n]) x) :=
  (hx n).1

theorem FullyGeneric.everyLift {x : TorusPoint}
    (hx : FullyGeneric x) (n : ℕ) (word : List CorrLetter)
    {y : TorusPoint} (e : WordLift word ((sourceU^[n]) x) y) :
    e.Admissible :=
  (hx n).2 word y e

theorem FullyGeneric.forward {x : TorusPoint} (hx : FullyGeneric x) :
    FullyGeneric (sourceU x) := by
  intro n
  simpa [Function.iterate_succ_apply] using hx (n + 1)

/-! ## Logarithmic radii -/

abbrev Mat2R := Matrix (Fin 2) (Fin 2) ℝ
abbrev RadiusVector := Fin 2 → ℝ

def logRadius (q : TorusPoint) : RadiusVector :=
  ![Real.log ‖q.1.x‖, Real.log ‖q.1.y‖]

def radiusU : Mat2R := !![1, 1 / 2; 0, 1]
def radiusUInv : Mat2R := !![1, -1 / 2; 0, 1]
def radiusC : Mat2R := !![0, -1; 1, -1]
def radiusCInv : Mat2R := !![-1, 1; -1, 0]
def radiusRho : Mat2R := !![0, 1; 1, 0]

def letterRadiusMatrix : CorrLetter → Mat2R
  | .U => radiusU
  | .UInv => radiusUInv
  | .C => radiusC
  | .CInv => radiusCInv
  | .rho => radiusRho

theorem logRadius_targetU (p : TorusPoint) :
    logRadius (targetU p) = radiusU *ᵥ logRadius (sourceU p) := by
  funext i
  fin_cases i
  · simp [logRadius, targetU, targetUCoord, sourceU, sourceUCoord, radiusU,
      Matrix.mulVec, Fin.sum_univ_two]
    rw [Real.log_mul (norm_ne_zero_iff.mpr p.2.x_ne)
      (norm_ne_zero_iff.mpr p.2.y_ne)]
  · simp [logRadius, targetU, targetUCoord, sourceU, sourceUCoord, radiusU,
      Matrix.mulVec, Fin.sum_univ_two]

theorem logRadius_sourceU (p : TorusPoint) :
    logRadius (sourceU p) = radiusUInv *ᵥ logRadius (targetU p) := by
  rw [logRadius_targetU]
  rw [Matrix.mulVec_mulVec]
  have hInv : radiusUInv * radiusU = (1 : Mat2R) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [radiusUInv, radiusU, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hInv, Matrix.one_mulVec]

theorem logRadius_torusCyclic (q : TorusPoint) :
    logRadius (torusCyclic q) = radiusC *ᵥ logRadius q := by
  funext i
  fin_cases i
  · simp [logRadius, torusCyclic, cyclicCoord, radiusC,
      Matrix.mulVec, Fin.sum_univ_two, norm_div]
  · simp [logRadius, torusCyclic, cyclicCoord, radiusC,
      Matrix.mulVec, Fin.sum_univ_two, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.mpr q.2.x_ne)
      (norm_ne_zero_iff.mpr q.2.y_ne)]
    ring

theorem logRadius_torusCyclicInv (q : TorusPoint) :
    logRadius (torusCyclicInv q) = radiusCInv *ᵥ logRadius q := by
  funext i
  fin_cases i
  · simp [logRadius, torusCyclicInv, cyclicSqCoord, radiusCInv,
      Matrix.mulVec, Fin.sum_univ_two, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.mpr q.2.y_ne)
      (norm_ne_zero_iff.mpr q.2.x_ne)]
    ring
  · simp [logRadius, torusCyclicInv, cyclicSqCoord, radiusCInv,
      Matrix.mulVec, Fin.sum_univ_two, norm_div]

theorem logRadius_torusRho (q : TorusPoint) :
    logRadius (torusRho q) = radiusRho *ᵥ logRadius q := by
  funext i
  fin_cases i <;>
    simp [logRadius, torusRho, rhoCoord, radiusRho,
      Matrix.mulVec, Fin.sum_univ_two]

theorem LetterStep.logRadius_target {letter : CorrLetter} {x y : TorusPoint}
    (e : LetterStep letter x y) :
    logRadius y = letterRadiusMatrix letter *ᵥ logRadius x := by
  cases e with
  | U p => exact logRadius_targetU p
  | UInv p => exact logRadius_sourceU p
  | C _ => exact logRadius_torusCyclic _
  | CInv _ => exact logRadius_torusCyclicInv _
  | rho _ => exact logRadius_torusRho _

/-- Because the head letter acts first, matrices accumulate on the left. -/
def wordRadiusMatrix : List CorrLetter → Mat2R
  | [] => 1
  | letter :: word => wordRadiusMatrix word * letterRadiusMatrix letter

theorem WordLift.logRadius_terminal {word : List CorrLetter} {x y : TorusPoint}
    (e : WordLift word x y) :
    logRadius y = wordRadiusMatrix word *ᵥ logRadius x := by
  induction e with
  | nil q => simp [wordRadiusMatrix]
  | cons head tail ih =>
      rw [ih, head.logRadius_target, Matrix.mulVec_mulVec]
      rfl

/-! ## The explicit two-edge correction -/

def correction1Coord (q : Coord4) : Coord4 := ⟨q.x * q.y, q.y⟩
def correction2Coord (q : Coord4) : Coord4 := ⟨q.x, -(q.x * q.y)⟩

theorem correction1Coord_torus_mem (q : TorusPoint) :
    IsTorusPoint (correction1Coord q.1) :=
  ⟨mul_ne_zero q.2.x_ne q.2.y_ne, q.2.y_ne⟩

theorem correction2Coord_torus_mem (q : TorusPoint) :
    IsTorusPoint (correction2Coord q.1) :=
  ⟨q.2.x_ne, neg_ne_zero.mpr (mul_ne_zero q.2.x_ne q.2.y_ne)⟩

def correction1 (q : TorusPoint) : TorusPoint :=
  ⟨correction1Coord q.1, correction1Coord_torus_mem q⟩

def correction2 (q : TorusPoint) : TorusPoint :=
  ⟨correction2Coord q.1, correction2Coord_torus_mem q⟩

@[continuity, fun_prop]
theorem continuous_correction1Coord : Continuous correction1Coord := by
  apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
  apply Continuous.prodMk
  · change Continuous fun q : Coord4 => q.x * q.y
    fun_prop
  · change Continuous fun q : Coord4 => q.y
    exact continuous_coord4_y

@[continuity, fun_prop]
theorem continuous_correction2Coord : Continuous correction2Coord := by
  apply (coord4HomeomorphProd.isInducing.continuous_iff).mpr
  apply Continuous.prodMk
  · change Continuous fun q : Coord4 => q.x
    exact continuous_coord4_x
  · change Continuous fun q : Coord4 => -(q.x * q.y)
    fun_prop

@[continuity, fun_prop]
theorem continuous_correction1 : Continuous correction1 := by
  exact (continuous_correction1Coord.comp continuous_subtype_val).subtype_mk _

@[continuity, fun_prop]
theorem continuous_correction2 : Continuous correction2 := by
  exact (continuous_correction2Coord.comp continuous_subtype_val).subtype_mk _

def correctionParam1 (q : TorusPoint) (β : ℂ) (hβ : β ≠ 0) : TorusPoint :=
  ⟨⟨-q.1.x, β⟩, ⟨neg_ne_zero.mpr q.2.x_ne, hβ⟩⟩

def correctionParam2 (q : TorusPoint) (β : ℂ) (hβ : β ≠ 0) : TorusPoint :=
  ⟨⟨q.1.x * β, -β⟩,
    ⟨mul_ne_zero q.2.x_ne hβ, neg_ne_zero.mpr hβ⟩⟩

/-- The two displayed parameters form a literal two-edge lift from `q` to
`correction1 q`; no global square-root choice is involved. -/
theorem twoEdgeCorrection (q : TorusPoint) (β : ℂ) (hβ : β ≠ 0)
    (hroot : β ^ 2 = -q.1.y) :
    sourceU (correctionParam1 q β hβ) = q ∧
      targetU (correctionParam1 q β hβ) =
        sourceU (correctionParam2 q β hβ) ∧
      targetU (correctionParam2 q β hβ) = correction1 q := by
  constructor
  · apply Subtype.ext
    apply Coord4.ext
    · simp [sourceU, sourceUCoord, correctionParam1]
    · change -(β ^ 2) = q.1.y
      rw [hroot]
      simp
  constructor
  · apply Subtype.ext
    apply Coord4.ext <;>
      simp [targetU, targetUCoord, sourceU, sourceUCoord,
        correctionParam1, correctionParam2]
  · apply Subtype.ext
    apply Coord4.ext
    · change q.1.x * β * -β = q.1.x * q.1.y
      rw [show q.1.x * β * -β = -q.1.x * β ^ 2 by ring, hroot]
      ring
    · change -((-β) ^ 2) = q.1.y
      rw [show (-β) ^ 2 = β ^ 2 by ring, hroot]
      ring

def correction1Word : List CorrLetter := [.U, .U]

def correction2Word : List CorrLetter := [.rho, .U, .U, .rho]

@[simp]
theorem correction1Word_length : correction1Word.length = 2 := by decide

@[simp]
theorem correction2Word_length : correction2Word.length = 4 := by decide

@[simp]
theorem correction1Word_sign : wordSign correction1Word = 1 := by
  norm_num [correction1Word, wordSign, letterSign]

@[simp]
theorem correction2Word_sign : wordSign correction2Word = 1 := by
  norm_num [correction2Word, wordSign, letterSign]

@[simp]
theorem correction1Word_UCount : wordUCount correction1Word = 2 := by decide

@[simp]
theorem correction2Word_UCount : wordUCount correction2Word = 2 := by decide

/-- The displayed two-edge correction is an actual dependent `WordLift`. -/
theorem exists_correction1Lift (q : TorusPoint) :
    Nonempty (WordLift correction1Word q (correction1 q)) := by
  obtain ⟨β, hβroot⟩ :=
    IsAlgClosed.exists_pow_nat_eq (-q.1.y) (by omega : 0 < 2)
  have hβ : β ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : 2 ≠ 0)] at hβroot
    exact q.2.y_ne (by simpa using hβroot.symm)
  obtain ⟨hsource, hmiddle, htarget⟩ :=
    twoEdgeCorrection q β hβ hβroot
  let tail : WordLift [.U]
      (targetU (correctionParam1 q β hβ))
      (targetU (correctionParam2 q β hβ)) := by
    rw [hmiddle]
    exact WordLift.cons (LetterStep.U (correctionParam2 q β hβ))
      (WordLift.nil _)
  let e₀ : WordLift [.U, .U]
      (sourceU (correctionParam1 q β hβ))
      (targetU (correctionParam2 q β hβ)) :=
    WordLift.cons (LetterStep.U (correctionParam1 q β hβ)) tail
  have e : WordLift correction1Word q (correction1 q) := by
    simpa only [correction1Word, hsource, htarget] using e₀
  exact ⟨e⟩

theorem correction2_eq_rho_correction1_rho (q : TorusPoint) :
    correction2 q = torusRho (correction1 (torusRho q)) := by
  apply Subtype.ext
  apply Coord4.ext <;>
    simp [correction2, correction2Coord, correction1, correction1Coord,
      torusRho, rhoCoord] <;> ring

/-- The conjugated correction is a literal four-letter lift, including both
occurrences of `rho`. -/
theorem exists_correction2Lift (q : TorusPoint) :
    Nonempty (WordLift correction2Word q (correction2 q)) := by
  obtain ⟨emiddle⟩ := exists_correction1Lift (torusRho q)
  let middle := correction1 (torusRho q)
  have hend : torusRho middle = correction2 q := by
    simpa [middle] using (correction2_eq_rho_correction1_rho q).symm
  let elast : WordLift [.rho] middle (torusRho middle) :=
    WordLift.cons (LetterStep.rho middle) (WordLift.nil _)
  have hword : CorrLetter.rho :: (correction1Word ++ [.rho]) =
      correction2Word := by decide
  let e : WordLift correction2Word q (correction2 q) := by
    rw [← hend]
    rw [← hword]
    exact WordLift.cons (LetterStep.rho q) (emiddle.append elast)
  exact ⟨e⟩

/-- If `q` lies on the deleted divisor, at least one of the two explicit
corrections leaves it. -/
theorem correction_leaves_divisor (q : TorusPoint)
    (hq : delta4 q.1 = 0) :
    (correction1 q).IsGeneric ∨ (correction2 q).IsGeneric := by
  by_cases h1 : (correction1 q).IsGeneric
  · exact Or.inl h1
  right
  have h1z : delta4 (correction1 q).1 = 0 := not_ne_iff.mp h1
  have hy2 : q.1.y ^ 2 = 1 := by
    change 1 - q.1.x + q.1.y = 0 at hq
    change 1 - q.1.x * q.1.y + q.1.y = 0 at h1z
    linear_combination q.1.y * hq - h1z
  have hy : q.1.y = 1 := by
    rcases sq_eq_one_iff.mp hy2 with hy | hy
    · exact hy
    · exfalso
      apply q.2.x_ne
      change 1 - q.1.x + q.1.y = 0 at hq
      rw [hy] at hq
      linear_combination -hq
  have hx : q.1.x = 2 := by
    change 1 - q.1.x + q.1.y = 0 at hq
    rw [hy] at hq
    linear_combination -hq
  change delta4 (correction2Coord q.1) ≠ 0
  rw [show delta4 (correction2Coord q.1) = -3 by
    simp [delta4, correction2Coord, hx, hy]
    norm_num]
  norm_num

end
end Pfaffian
end Sp4
