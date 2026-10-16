/- GID: D5/S3/FiniteGroups/HartRowleyGreedyRefutation
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/HartRowleyGreedyRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S3/FiniteGroups/HartRowleyGreedyRefutation.claim; result=D5/S3/FiniteGroups/HartRowleyGreedyRefutation.result; claim=D5/S3/FiniteGroups/HartRowleyGreedyRefutation.claim
   digest: Greedy involution prefix and suffix counts need not agree. -/

import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

set_option maxRecDepth 4096

namespace D5.S3.FiniteGroups.HartRowleyGreedyRefutation

abbrev P := Equiv.Perm (Fin 4)
abbrev N := Fin 2 × Fin 3 × Fin 4
abbrev A3 := (CoxeterMatrix.A 3).Group
abbrev canonical := (CoxeterMatrix.A 3).toCoxeterSystem

def adjacent (i : Fin 3) : P := Equiv.swap i.castSucc i.succ

def normalWord (n : N) : List (Fin 3) :=
  (if n.1.val = 0 then [] else [0] : List (Fin 3)) ++
  (match n.2.1.val with | 0 => [] | 1 => [1] | _ => [1, 0] : List (Fin 3)) ++
  (match n.2.2.val with | 0 => [] | 1 => [2] | 2 => [2, 1] | _ => [2, 1, 0] : List (Fin 3))

def permWord (l : List (Fin 3)) : P := (l.map adjacent).prod

def indices : List N :=
  (List.finRange 2).flatMap fun i =>
    (List.finRange 3).flatMap fun j => (List.finRange 4).map fun k => (i, j, k)

def normalIndex (p : P) : N :=
  ((indices.find? fun n => decide (permWord (normalWord n) = p))).getD (0, 0, 0)

set_option maxHeartbeats 4000000 in
theorem normal_index_spec (p : P) : permWord (normalWord (normalIndex p)) = p := by
  revert p
  decide

def representation : A3 →* P :=
  canonical.lift ⟨adjacent, by
    intro i j
    fin_cases i <;> fin_cases j <;> decide⟩

set_option maxHeartbeats 4000000 in
theorem normal_step (n : N) (r : Fin 3) :
    canonical.wordProd (normalWord n) * canonical.simple r =
      canonical.wordProd (normalWord (normalIndex (permWord (normalWord n) * adjacent r))) := by
  let a : A3 := canonical.simple 0
  let b : A3 := canonical.simple 1
  let c : A3 := canonical.simple 2
  have aa : a * a = 1 := canonical.simple_mul_simple_self 0
  have bb : b * b = 1 := canonical.simple_mul_simple_self 1
  have cc : c * c = 1 := canonical.simple_mul_simple_self 2
  have ca : c * a = a * c := by
    have h := (canonical.wordProd_braidWord_eq 0 2).symm
    change c * (a * 1) = a * (c * 1) at h
    simpa only [mul_one] using h
  have bab : b * a * b = a * b * a := by
    have h := canonical.wordProd_braidWord_eq 0 1
    change b * (a * (b * 1)) = a * (b * (a * 1)) at h
    simpa only [mul_one, mul_assoc] using h
  have cbc : c * b * c = b * c * b := by
    have h := canonical.wordProd_braidWord_eq 1 2
    change c * (b * (c * 1)) = b * (c * (b * 1)) at h
    simpa only [mul_one, mul_assoc] using h
  have raa (x : A3) : a * (a * x) = x := by rw [← mul_assoc, aa, one_mul]
  have rbb (x : A3) : b * (b * x) = x := by rw [← mul_assoc, bb, one_mul]
  have rcc (x : A3) : c * (c * x) = x := by rw [← mul_assoc, cc, one_mul]
  have rca (x : A3) : c * (a * x) = a * (c * x) := by simp only [← mul_assoc, ca]
  have rbab (x : A3) : b * (a * (b * x)) = a * (b * (a * x)) := by
    simp only [← mul_assoc, bab]
  have rcbc (x : A3) : c * (b * (c * x)) = b * (c * (b * x)) := by
    simp only [← mul_assoc, cbc]
  have rcbac (x : A3) : c * (b * (a * (c * x))) = b * (c * (b * (a * x))) := by
    rw [← rca, rcbc]
  have rcbab (x : A3) : c * (b * (a * (b * x))) = a * (c * (b * (a * x))) := by
    rw [rbab, rca]
  have bab0 : b * (a * b) = a * (b * a) := by simpa using rbab 1
  have cbc0 : c * (b * c) = b * (c * b) := by simpa using rcbc 1
  have cbac0 : c * (b * (a * c)) = b * (c * (b * a)) := by simpa using rcbac 1
  have cbab0 : c * (b * (a * b)) = a * (c * (b * a)) := by simpa using rcbab 1
  dsimp only [a, b, c] at bab0 cbc0 cbac0 cbab0
  dsimp only [a, b, c] at aa bb cc ca bab cbc raa rbb rcc rca rbab rcbc rcbac rcbab
  rcases n with ⟨i, j, k⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases r
  all_goals
    conv_rhs => pattern normalIndex _; cbv
    simp only [normalWord, CoxeterSystem.wordProd, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, List.append_nil, List.nil_append,
      List.cons_append, mul_one, one_mul, ite_true, ite_false,
      ↓reduceIte, Nat.one_ne_zero]
    simp only [show (⟨0, by decide⟩ : Fin 3) = 0 from rfl,
      show (⟨1, by decide⟩ : Fin 3) = 1 from rfl,
      show (⟨2, by decide⟩ : Fin 3) = 2 from rfl]
    try simp only [mul_assoc, aa, bb, cc, ca, bab, cbc,
      raa, rbb, rcc, rca, rbab, rcbc, rcbac, rcbab, bab0, cbc0, cbac0, cbab0]
  all_goals try rfl

theorem representation_word (l : List (Fin 3)) :
    representation (canonical.wordProd l) = permWord l := by
  induction l with
  | nil => simp [permWord]
  | cons i l ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul]
    have hi : representation (canonical.simple i) = adjacent i :=
      canonical.lift_apply_simple _ _
    rw [hi, ih]
    rfl

theorem normal_form (g : A3) :
    canonical.wordProd (normalWord (normalIndex (representation g))) = g := by
  apply canonical.simple_induction_right g
  · change canonical.wordProd (normalWord (normalIndex (1 : P))) = 1
    rfl
  · intro g i ih
    have h := normal_step (normalIndex (representation g)) i
    rw [normal_index_spec] at h
    rw [map_mul]
    change canonical.wordProd
      (normalWord (normalIndex (representation g * adjacent i))) = g * canonical.simple i
    exact h.symm.trans (congrArg (· * canonical.simple i) ih)

def equivalence : A3 ≃* P :=
  { representation with
    invFun := fun p => canonical.wordProd (normalWord (normalIndex p))
    left_inv := normal_form
    right_inv := fun p => (representation_word _).trans (normal_index_spec p) }

def system : CoxeterSystem (CoxeterMatrix.A 3) P := canonical.map equivalence

theorem system_simple (i : Fin 3) : system.simple i = adjacent i := by
  change representation (canonical.simple i) = adjacent i
  exact canonical.lift_apply_simple _ _

def invLength (p : P) : ℕ :=
  (if p 0 > p 1 then 1 else 0) + (if p 0 > p 2 then 1 else 0) +
  (if p 0 > p 3 then 1 else 0) + (if p 1 > p 2 then 1 else 0) +
  (if p 1 > p 3 then 1 else 0) + (if p 2 > p 3 then 1 else 0)

set_option maxHeartbeats 4000000 in
theorem inv_step : ∀ (p : P) (i : Fin 3),
    invLength (adjacent i * p) ≤ invLength p + 1 := by decide

set_option maxHeartbeats 4000000 in
theorem normal_length : ∀ n : N,
    (normalWord n).length = invLength (permWord (normalWord n)) := by decide

theorem system_word (l : List (Fin 3)) : system.wordProd l = permWord l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [CoxeterSystem.wordProd_cons, system_simple, ih]
    rfl

theorem length_eq (p : P) : system.length p = invLength p := by
  apply Nat.le_antisymm
  · have h := system.length_wordProd_le (normalWord (normalIndex p))
    rw [system_word, normal_index_spec, normal_length, normal_index_spec] at h
    exact h
  · have bound (l : List (Fin 3)) : invLength (permWord l) ≤ l.length := by
      induction l with
      | nil => decide
      | cons i l ih =>
        exact (inv_step (permWord l) i).trans (Nat.add_le_add_right ih 1)
    obtain ⟨l, hl, hp⟩ := system.exists_isReduced p
    rw [hp, hl.eq, system_word]
    exact bound l


section Greedy

variable {B W : Type*} [Group W] {M : CoxeterMatrix B}

/-- An order-exactly-two prefix, with the actual Coxeter length-additivity law. -/
def InvolutionPrefix (cs : CoxeterSystem M W) (w u : W) : Prop :=
  u ≠ 1 ∧ u * u = 1 ∧ cs.length w = cs.length u + cs.length (u⁻¹ * w)

/-- A maximum by length over all involution prefixes, not an inclusion maximum. -/
def Ancestor (cs : CoxeterSystem M W) (w u : W) : Prop :=
  InvolutionPrefix cs w u ∧
    ∀ v, InvolutionPrefix cs w v → cs.length v ≤ cs.length u

def AncestorProperty (cs : CoxeterSystem M W) : Prop :=
  ∀ w, w ≠ 1 → ∃! u, Ancestor cs w u

noncomputable def ancestor (cs : CoxeterSystem M W) (h : AncestorProperty cs) (w : W) : W := by
  classical
  exact if hw : w = 1 then 1 else Classical.choose (h w hw)

theorem ancestor_spec (cs : CoxeterSystem M W) (h : AncestorProperty cs)
    (w : W) (hw : w ≠ 1) : Ancestor cs w (ancestor cs h w) := by
  simp only [ancestor, dif_neg hw]
  exact (Classical.choose_spec (h w hw)).1

theorem ancestor_eq (cs : CoxeterSystem M W) (h : AncestorProperty cs)
    (w u : W) (hw : w ≠ 1) (hu : Ancestor cs w u) : ancestor cs h w = u := by
  classical
  rw [ancestor, dif_neg hw]
  exact ((Classical.choose_spec (h w hw)).2 _ hu).symm

def InvolutionSuffix (cs : CoxeterSystem M W) (w u : W) : Prop :=
  u ≠ 1 ∧ u * u = 1 ∧ cs.length w = cs.length (w * u⁻¹) + cs.length u

def SuffixAncestor (cs : CoxeterSystem M W) (w u : W) : Prop :=
  InvolutionSuffix cs w u ∧
    ∀ v, InvolutionSuffix cs w v → cs.length v ≤ cs.length u

/-- Inversion identifies the source suffix condition with the prefix condition. -/
theorem suffix_characterization (cs : CoxeterSystem M W) (w u : W) :
    InvolutionPrefix cs w⁻¹ u⁻¹ ↔ InvolutionSuffix cs w u := by
  have hsquare : u⁻¹ * u⁻¹ = 1 ↔ u * u = 1 := by
    constructor <;> intro h <;> have hi := congrArg Inv.inv h
    · simpa only [mul_inv_rev, inv_inv, inv_one] using hi
    · simpa only [mul_inv_rev, inv_one] using hi
  have hlen : cs.length (u * w⁻¹) = cs.length (w * u⁻¹) := by
    rw [← cs.length_inv (u * w⁻¹), mul_inv_rev, inv_inv]
  simp only [InvolutionPrefix, InvolutionSuffix, inv_ne_one, inv_inv, cs.length_inv, hsquare, hlen,
    Nat.add_comm]

theorem suffix_ancestor_spec (cs : CoxeterSystem M W) (h : AncestorProperty cs)
    (w : W) (hw : w ≠ 1) :
    SuffixAncestor cs w (ancestor cs h w⁻¹)⁻¹ ∧
      ∀ v, SuffixAncestor cs w v → v = (ancestor cs h w⁻¹)⁻¹ := by
  have hiw : w⁻¹ ≠ 1 := inv_ne_one.mpr hw
  have ha := ancestor_spec cs h w⁻¹ hiw
  have actual : InvolutionSuffix cs w (ancestor cs h w⁻¹)⁻¹ :=
    (suffix_characterization cs w _).mp (by simpa only [inv_inv] using ha.1)
  refine ⟨⟨actual, ?_⟩, ?_⟩
  · intro v hv
    have hm := ha.2 v⁻¹ ((suffix_characterization cs w v).mpr hv)
    simpa only [cs.length_inv] using hm
  · intro v hv
    have hvp : Ancestor cs w⁻¹ v⁻¹ := by
      refine ⟨(suffix_characterization cs w v).mpr hv.1, ?_⟩
      intro u hu
      have hs : InvolutionSuffix cs w u⁻¹ :=
        (suffix_characterization cs w u⁻¹).mp (by simpa only [inv_inv] using hu)
      simpa only [cs.length_inv] using hv.2 _ hs
    have he := ancestor_eq cs h w⁻¹ v⁻¹ hiw hvp
    simpa only [inv_inv] using (congrArg Inv.inv he).symm

/-- Choose the unique maximum suffix; its existence is proved by inversion. -/
noncomputable def suffixAncestor (cs : CoxeterSystem M W) (h : AncestorProperty cs)
    (w : W) : W := by
  classical
  exact if hw : w = 1 then 1 else Classical.choose
    (show ∃! u, SuffixAncestor cs w u from
      ⟨_, (suffix_ancestor_spec cs h w hw).1, (suffix_ancestor_spec cs h w hw).2⟩)

theorem suffixAncestor_eq (cs : CoxeterSystem M W) (h : AncestorProperty cs) (w : W) :
    suffixAncestor cs h w = (ancestor cs h w⁻¹)⁻¹ := by
  classical
  by_cases hw : w = 1
  · subst w
    simp only [suffixAncestor, dif_pos rfl, inv_one, ancestor]
    simp
  · rw [suffixAncestor, dif_neg hw]
    apply (suffix_ancestor_spec cs h w hw).2
    exact (Classical.choose_spec
      (show ∃! u, SuffixAncestor cs w u from
        ⟨_, (suffix_ancestor_spec cs h w hw).1, (suffix_ancestor_spec cs h w hw).2⟩)).1

/-- The suffix factor is the inverse of the ancestor of the inverse element. -/
noncomputable def residual (cs : CoxeterSystem M W) (h : AncestorProperty cs)
    (suffix : Bool) (w : W) : W :=
  if suffix then w * (suffixAncestor cs h w)⁻¹ else (ancestor cs h w)⁻¹ * w

theorem residual_drop (cs : CoxeterSystem M W) (h : AncestorProperty cs)
    (suffix : Bool) (w : W) (hw : w ≠ 1) :
    cs.length (residual cs h suffix w) < cs.length w := by
  cases suffix
  · have ha := (ancestor_spec cs h w hw).1
    have hp : 0 < cs.length (ancestor cs h w) :=
      Nat.pos_of_ne_zero (fun he => ha.1 (cs.length_eq_zero_iff.mp he))
    change cs.length ((ancestor cs h w)⁻¹ * w) < cs.length w
    have he := ha.2.2
    omega
  · have ha := (suffix_ancestor_spec cs h w hw).1.1
    have hp : 0 < cs.length ((ancestor cs h w⁻¹)⁻¹) :=
      Nat.pos_of_ne_zero (fun he => ha.1 (cs.length_eq_zero_iff.mp he))
    have he := ha.2.2
    simp only [inv_inv] at he
    change cs.length (w * (suffixAncestor cs h w)⁻¹) < cs.length w
    rw [suffixAncestor_eq, inv_inv]
    omega

variable [DecidableEq W]

/-- The actual greedy recursion; identity has count zero and each step removes one factor. -/
noncomputable def greedyCount (cs : CoxeterSystem M W) (h : AncestorProperty cs)
    (suffix : Bool) (w : W) : ℕ :=
  if hw : w = 1 then 0 else greedyCount cs h suffix (residual cs h suffix w) + 1
termination_by cs.length w
decreasing_by exact residual_drop cs h suffix w hw

/-- A finite evaluator used only after its fuel is proved at least the Coxeter length. -/
def run (next : W → W) : ℕ → W → ℕ
  | 0, _ => 0
  | n + 1, w => if w = 1 then 0 else run next n (next w) + 1

theorem count_eq_run (cs : CoxeterSystem M W) (h : AncestorProperty cs) (suffix : Bool)
    (fuel : ℕ) (w : W) (hf : cs.length w ≤ fuel) :
    greedyCount cs h suffix w = run (residual cs h suffix) fuel w := by
  induction fuel generalizing w with
  | zero =>
    have hw : w = 1 := cs.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hf)
    subst w
    rw [greedyCount]
    simp [run]
  | succ fuel ih =>
    rw [greedyCount, run]
    split_ifs with hw
    · rfl
    · rw [ih _ (by have hd := residual_drop cs h suffix w hw; omega)]

end Greedy

/-- The full equality, with no finiteness, rank, or Coxeter-element restriction. -/
def claim : Prop :=
  ∀ (B W : Type) [Group W] [DecidableEq W] (M : CoxeterMatrix B)
    (cs : CoxeterSystem M W) (h : AncestorProperty cs) (w : W),
    greedyCount cs h false w = greedyCount cs h true w

def computablePrefix (w u : P) : Prop :=
  u ≠ 1 ∧ u * u = 1 ∧ invLength w = invLength u + invLength (u⁻¹ * w)

instance (w u : P) : Decidable (computablePrefix w u) :=
  inferInstanceAs (Decidable (u ≠ 1 ∧ u * u = 1 ∧
    invLength w = invLength u + invLength (u⁻¹ * w)))

/-- All nine nonidentity involutions, ordered by decreasing inversion length. -/
def involutions : List P :=
  [[0, 1, 0, 2, 1, 0], [0, 1, 2, 1, 0], [1, 0, 2, 1],
    [1, 2, 1], [0, 1, 0], [0, 2], [2], [1], [0]].map permWord

def finiteAncestor (w : P) : P :=
  ((involutions.find? fun u => decide (computablePrefix w u))).getD 1

set_option maxHeartbeats 12000000 in
-- The certificate quantifies over every element and every competing involution prefix.
theorem finite_ancestor_certificate : ∀ w : P, w ≠ 1 →
    computablePrefix w (finiteAncestor w) ∧
      ∀ v, computablePrefix w v →
        invLength v ≤ invLength (finiteAncestor w) ∧
          (invLength (finiteAncestor w) ≤ invLength v → v = finiteAncestor w) := by
  decide

theorem prefix_computes (w u : P) :
    InvolutionPrefix system w u ↔ computablePrefix w u := by
  simp only [InvolutionPrefix, computablePrefix, length_eq]

theorem qualification : AncestorProperty system := by
  intro w hw
  have hc := finite_ancestor_certificate w hw
  refine ⟨finiteAncestor w, ⟨(prefix_computes _ _).mpr hc.1, ?_⟩, ?_⟩
  · intro v hv
    simpa only [length_eq] using (hc.2 v ((prefix_computes _ _).mp hv)).1
  · intro v hv
    apply (hc.2 v ((prefix_computes _ _).mp hv.1)).2
    simpa only [length_eq] using hv.2 _ ((prefix_computes _ _).mpr hc.1)

theorem ancestor_computes (w : P) : ancestor system qualification w = finiteAncestor w := by
  by_cases hw : w = 1
  · subst w
    rw [ancestor, dif_pos rfl]
    decide
  · apply ancestor_eq system qualification w _ hw
    have hc := finite_ancestor_certificate w hw
    refine ⟨(prefix_computes _ _).mpr hc.1, ?_⟩
    intro v hv
    simpa only [length_eq] using (hc.2 v ((prefix_computes _ _).mp hv)).1

def finiteResidual (suffix : Bool) (w : P) : P :=
  if suffix then w * finiteAncestor w⁻¹ else (finiteAncestor w)⁻¹ * w

theorem residual_computes (suffix : Bool) :
    residual system qualification suffix = finiteResidual suffix := by
  funext w
  simp only [residual, finiteResidual, suffixAncestor_eq, inv_inv, ancestor_computes]

def witness : P := permWord [0, 2, 1, 2]

/-- A nonidentity element of an actual qualifying system with counts three and two. -/
theorem unequal_counts :
    witness ≠ 1 ∧ greedyCount system qualification false witness = 3 ∧
      greedyCount system qualification true witness = 2 := by
  have hp := count_eq_run system qualification false 4 witness
    (by rw [length_eq]; decide)
  have hs := count_eq_run system qualification true 4 witness
    (by rw [length_eq]; decide)
  rw [residual_computes] at hp hs
  exact ⟨by decide, hp.trans (by decide), hs.trans (by decide)⟩

theorem result : ¬ claim := by
  intro h
  have he := h (Fin 3) P (CoxeterMatrix.A 3) system qualification witness
  rw [unequal_counts.2.1, unequal_counts.2.2] at he
  exact (by decide : (3 : ℕ) ≠ 2) he

end D5.S3.FiniteGroups.HartRowleyGreedyRefutation

