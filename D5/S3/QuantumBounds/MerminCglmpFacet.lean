/- GID: D5/S3/QuantumBounds/MerminCglmpFacet
   generality: I
   mirror-B: D5/B/S3/QuantumBounds/MerminCglmpFacet
   mirror-E: none(waiver:non-computational-content)
   anchors: []
   utility: none
   digest: The Mermin-CGLMP inequality is a facet of the local polytope for every K >= 2. -/
/-
proof_shape: result: content (including its local tripartite rigidity proof).
proof_shape: tripartite_rigidity, rigidity_vertices: content.
proof_shape: vertex_expectation, normalization_vertex, equiv_natCast, equiv_val_cast,
  mkStrategy_surjective, bracket_cast, I_vertex_mkStrategy, vertex_basis_expansion,
  local_function_representation, validity_vertex, J3_lower, neg_pair_val,
  neg_pred_pair_val, sigma_zero_witness, sigma_neg_one_witness, multiplier_constant,
  tripLocal_rectangular, slice_AB: bind-only; each consumer is listed below its statement.
escape_witness: tripartite_rigidity, via the Charlie slice and rectangular gluing.
admission_basis: open-problem-resolution (#13574; Proved)
Utility: universal facet theorem, without enumeration, checker, numeric reduction or instance.
Direct frozen dependencies: none (pinned Mathlib only).
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S3.QuantumBounds.FacetRigidityBridge
import D5.S3.QuantumBounds.CglmpFacetRigidity

set_option autoImplicit false
open scoped BigOperators
open Set

namespace D5.S3.QuantumBounds.MerminCglmpFacet
open D5.S3.QuantumBounds.CglmpFacetRigidity

def vertex (K : ℕ) (s : ((Fin 2 → Fin K) × (Fin 2 → Fin K) × (Fin 2 → Fin K))) : ((Fin 2 × Fin 2 ×
  Fin 2) × (Fin K × Fin K × Fin K) → ℝ) := fun q =>
  if s.1 q.1.1 = q.2.1 ∧ s.2.1 q.1.2.1 = q.2.2.1 ∧
    s.2.2 q.1.2.2 = q.2.2.2 then 1 else 0

noncomputable def L (K : ℕ) : Set (((Fin 2 × Fin 2 × Fin 2) × (Fin K × Fin K × Fin K) → ℝ)) :=
  convexHull ℝ (Set.range (vertex K))

def bracket (K : ℕ) (t : ℤ) : ℝ := ((t % (K : ℤ) : ℤ) : ℝ)

noncomputable def I (K : ℕ) (p : ((Fin 2 × Fin 2 × Fin 2) × (Fin K × Fin K × Fin K) → ℝ)) : ℝ :=
  (∑ a : Fin K, ∑ b : Fin K, ∑ c : Fin K,
    bracket K ((a : ℤ) - b + c) * p ((1, 0, 0), (a, b, c))) +
  (∑ a : Fin K, ∑ b : Fin K, ∑ c : Fin K,
    bracket K ((a : ℤ) + b - c) * p ((0, 1, 0), (a, b, c))) +
  (∑ a : Fin K, ∑ b : Fin K, ∑ c : Fin K,
    bracket K (-(a : ℤ) + b + c) * p ((0, 0, 1), (a, b, c))) +
  (∑ a : Fin K, ∑ b : Fin K, ∑ c : Fin K,
    bracket K (-(a : ℤ) - b - c - 1) * p ((1, 1, 1), (a, b, c)))

noncomputable def claim : Prop := ∀ K : ℕ, 2 ≤ K →
  (∀ p ∈ L K, (K : ℝ) - 1 ≤ I K p) ∧
  Module.finrank ℝ (vectorSpan ℝ {p ∈ L K | I K p = (K : ℝ) - 1}) + 1 =
    Module.finrank ℝ (vectorSpan ℝ (L K))


variable {K : ℕ}

section
variable [NeZero K]

private def J3 (a A b B c C : ZMod K) : ℕ :=
  (A - b + c).val + (a + B - c).val + (-a + b + C).val + (-A - B - C - 1).val

/-- proof_shape: bind-only; consumer: validity_vertex. -/
private theorem J3_lower (a A b B c C : ZMod K) : K - 1 ≤ J3 a A b B c C := by
  have he : (A - b + c) + (a + B - c) + (-a + b + C) + (-A - B - C - 1) = -1 := by ring
  have h1 := ZMod.val_add_le (A - b + c) (a + B - c)
  have h2 := ZMod.val_add_le ((A - b + c) + (a + B - c)) (-a + b + C)
  have h3 := ZMod.val_add_le ((A - b + c) + (a + B - c) + (-a + b + C)) (-A - B - C - 1)
  have hm : (-1 : ZMod K).val = K - 1 := by
    cases K with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ k => exact ZMod.val_neg_one k
  rw [he, hm] at h3
  unfold J3
  omega

/-- proof_shape: bind-only; consumer: sigma_zero_witness, sigma_neg_one_witness. -/
private theorem neg_pair_val (x : ZMod K) :
    (x.val : ℝ) + (-x).val = (K : ℝ) * (if x = 0 then 0 else 1) := by
  rw [ZMod.neg_val]
  split_ifs with h
  · simp [h]
  · have hx := ZMod.val_lt x
    rw [Nat.cast_sub (by omega)]
    ring

/-- proof_shape: bind-only; consumer: sigma_zero_witness, sigma_neg_one_witness. -/
private theorem neg_pred_pair_val (x : ZMod K) :
    (x.val : ℝ) + (-x - 1).val = (K : ℝ) - 1 := by
  rw [val_neg_sub_one]
  have hx := ZMod.val_lt x
  have hk : 0 < K := NeZero.pos K
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
  ring

/-- proof_shape: bind-only; consumer: tripartite_rigidity, result. -/
private theorem sigma_zero_witness (p c C : ZMod K) :
    (J3 0 (-p) 0 p c C : ℝ) - ((K : ℝ) - 1) =
      (K : ℝ) * (if c = p then 0 else 1) := by
  have e1 : -p - 0 + c = c - p := by ring
  have e2 : 0 + p - c = -(c - p) := by ring
  have e3 : -(0 : ZMod K) + 0 + C = C := by ring
  have e4 : -(-p) - p - C - 1 = -C - 1 := by ring
  have he : c - p=0 ↔ c=p := sub_eq_zero
  simp only [J3, Nat.cast_add, e1, e2, e3, e4]
  have h1 := neg_pair_val (c - p)
  simp only [he] at h1
  have h2 := neg_pred_pair_val C
  linarith

/-- proof_shape: bind-only; consumer: tripartite_rigidity. -/
private theorem sigma_neg_one_witness (p c C : ZMod K) :
    (J3 p 0 0 (-p - 1) c C : ℝ) - ((K : ℝ) - 1) =
      (K : ℝ) * (if C = p then 0 else 1) := by
  have e1 : (0 : ZMod K) - 0 + c = c := by ring
  have e2 : p + (-p - 1) - c = -c - 1 := by ring
  have e3 : -p + 0 + C = C - p := by ring
  have e4 : -(0 : ZMod K) - (-p - 1) - C - 1 = -(C - p) := by ring
  have he : C - p=0 ↔ C=p := sub_eq_zero
  simp only [J3, Nat.cast_add, e1, e2, e3, e4]
  have h1 := neg_pred_pair_val c
  have h2 := neg_pair_val (C - p)
  simp only [he] at h2
  linarith

/-- proof_shape: bind-only; consumer: tripartite_rigidity. -/
private theorem multiplier_constant {α : Type*} [Nontrivial α] [DecidableEq α] (Λ : α → α → ℝ)
    (hv : ∀ p, (∀ c q C U,
      Λ c C * (if c = p then 0 else 1) + Λ q U * (if q = p then 0 else 1) =
        Λ c U * (if c = p then 0 else 1) + Λ q C * (if q = p then 0 else 1)))
    (hh : ∀ p, (∀ c q C U,
      Λ c C * (if C = p then 0 else 1) + Λ q U * (if U = p then 0 else 1) =
        Λ c U * (if U = p then 0 else 1) + Λ q C * (if C = p then 0 else 1))) :
    ∃ lam : ℝ, ∀ c C, Λ c C = lam := by
  classical
  have vertical (c C U : α) : Λ c C = Λ c U := by
    obtain ⟨p, hp⟩ := exists_ne c
    have h := hv p c p C U
    simp only [if_neg hp.symm, if_true, mul_one, mul_zero, add_zero] at h
    exact h
  have horizontal (c p C : α) : Λ c C = Λ p C := by
    obtain ⟨U, hU⟩ := exists_ne C
    have h := hh U c p C U
    simp only [if_neg hU.symm, if_true, mul_one, mul_zero, zero_add, add_zero] at h
    exact h
  let o : α := Classical.arbitrary α
  refine ⟨Λ o o, ?_⟩
  intro c C
  calc Λ c C = Λ c o := vertical c C o
       _ = Λ o o := horizontal c o o

private def TripLocal (f : Fin 2 → Fin 2 → Fin 2 → ZMod K → ZMod K → ZMod K → ℝ)
    (a A b B c C : ZMod K) : ℝ :=
  ∑ x : Fin 2, ∑ y : Fin 2, ∑ z : Fin 2,
    f x y z (if x = 0 then a else A) (if y = 0 then b else B) (if z = 0 then c else C)

omit [NeZero K] in
/-- proof_shape: bind-only; consumer: tripartite_rigidity. -/
private theorem tripLocal_rectangular
    (f : Fin 2 → Fin 2 → Fin 2 → ZMod K → ZMod K → ZMod K → ℝ)
    (a A b B : ZMod K) : ∀ c p C U,
    TripLocal f a A b B c C + TripLocal f a A b B p U =
      TripLocal f a A b B c U + TripLocal f a A b B p C := by
  intro c p C U
  simp [TripLocal, Fin.sum_univ_two]
  ring

omit [NeZero K] in
/-- proof_shape: bind-only; consumer: tripartite_rigidity. -/
private theorem slice_AB (a A b B c C : ZMod K) :
    J3 a A b B c C = J2AB (a - C) (A + c) b (B + C - c) := by
  have e1 : (A + c) - b = A - b + c := by ring
  have e2 : (a - C) + (B + C - c) = a + B - c := by ring
  have e3 : -(a - C) + b = -a + b + C := by ring
  have e4 : -(A + c) - (B + C - c) - 1 = -A - B - C - 1 := by ring
  simp only [J3, J2AB, e1, e2, e3, e4]

/-- proof_shape: content; consumer: rigidity_vertices. -/
private theorem tripartite_rigidity (hK : 2 ≤ K)
    (f : Fin 2 → Fin 2 → Fin 2 → ZMod K → ZMod K → ZMod K → ℝ)
    (hs : ∀ a A b B c C, J3 a A b B c C = K - 1 → TripLocal f a A b B c C = 0) :
    ∃ lam : ℝ, ∀ a A b B c C,
      TripLocal f a A b B c C = lam * ((J3 a A b B c C : ℝ) - ((K : ℝ) - 1)) := by
  classical
  have : Fact (1 < K) := ⟨by omega⟩
  have hslice (c C : ZMod K) : ∃ lam : ℝ, ∀ a A b B,
      TripLocal f a A b B c C = lam * ((J3 a A b B c C : ℝ) - ((K : ℝ) - 1)) := by
    let f2 : Fin 2 → Fin 2 → ZMod K → ZMod K → ℝ := fun x y a' b' =>
      ∑ z : Fin 2, f x y z (if x = 0 then a'+C else a'-c)
        (if y = 0 then b' else b'-C + c) (if z = 0 then c else C)
    have hrep (a A b B : ZMod K) :
        BipLocal f2 a A b B = TripLocal f (a + C) (A - c) b (B - C + c) c C := by
      simp [BipLocal, TripLocal, f2, Fin.sum_univ_two]
    obtain ⟨lam, hlam⟩ := bipartite_rigidity f2 (by
      intro a A b B hJ
      rw [hrep]
      apply hs
      rw [slice_AB]
      have e1 : (a + C) - C = a := by ring
      have e2 : (A - c) + c = A := by ring
      have e3 : (B - C + c) + C - c = B := by ring
      rw [e1, e2, e3]
      exact hJ)
    refine ⟨lam, ?_⟩
    intro a A b B
    have hh := hlam (a - C) (A + c) b (B + C - c)
    rw [hrep] at hh
    have e1 : (a - C) + C = a := by ring
    have e2 : (A + c) - c = A := by ring
    have e3 : (B + C - c) - C + c = B := by ring
    rw [e1, e2, e3, ← slice_AB] at hh
    exact hh
  let Λ : ZMod K → ZMod K → ℝ := fun c C => Classical.choose (hslice c C)
  have hΛ (a A b B c C : ZMod K) :
      TripLocal f a A b B c C = Λ c C * ((J3 a A b B c C : ℝ) - ((K : ℝ) - 1)) :=
    Classical.choose_spec (hslice c C) a A b B
  have hkR : (K : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne K)
  have hv (p : ZMod K) : (∀ c q C U,
      Λ c C * (if c = p then 0 else 1) + Λ q U * (if q = p then 0 else 1) =
        Λ c U * (if c = p then 0 else 1) + Λ q C * (if q = p then 0 else 1)) := by
    intro c q C U
    have hh := tripLocal_rectangular f 0 (-p) 0 p c q C U
    simp only [hΛ, sigma_zero_witness] at hh
    apply mul_left_cancel₀ hkR
    convert hh using 1 <;> ring
  have hh (p : ZMod K) : (∀ c q C U,
      Λ c C * (if C = p then 0 else 1) + Λ q U * (if U = p then 0 else 1) =
        Λ c U * (if U = p then 0 else 1) + Λ q C * (if C = p then 0 else 1)) := by
    intro c q C U
    have hh := tripLocal_rectangular f p 0 0 (-p - 1) c q C U
    simp only [hΛ, sigma_neg_one_witness] at hh
    apply mul_left_cancel₀ hkR
    convert hh using 1 <;> ring
  obtain ⟨lam, hlam⟩ := multiplier_constant Λ hv hh
  refine ⟨lam, ?_⟩
  intro a A b B c C
  rw [hΛ, hlam]


end

private noncomputable def linearI (K : ℕ) : ((Fin 2 × Fin 2 × Fin 2) × (Fin K × Fin K × Fin K) → ℝ)
  →ₗ[ℝ] ℝ where
  toFun := I K
  map_add' p q := by
    simp only [I, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' r p := by
    simp [I, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_add, mul_left_comm]

private noncomputable def normalization (K : ℕ) : ((Fin 2 × Fin 2 × Fin 2) × (Fin K × Fin K × Fin
  K) → ℝ) →ₗ[ℝ] ℝ where
  toFun p := ∑ a : Fin K, ∑ b : Fin K, ∑ c : Fin K, p ((0,0,0),(a,b,c))
  map_add' p q := by simp [Finset.sum_add_distrib]
  map_smul' r p := by simp [Finset.mul_sum]

variable {K : ℕ}

/-- proof_shape: bind-only; consumer: normalization_vertex, I_vertex_mkStrategy. -/
private theorem vertex_expectation (s : ((Fin 2 → Fin K) × (Fin 2 → Fin K) × (Fin 2 → Fin K))) (x y
  z : Fin 2)
    (F : Fin K → Fin K → Fin K → ℝ) :
    (∑ a : Fin K, ∑ b : Fin K, ∑ c : Fin K,
      F a b c * vertex K s ((x,y,z),(a,b,c))) =
      F (s.1 x) (s.2.1 y) (s.2.2 z) := by
  classical
  rw [Finset.sum_eq_single (s.1 x)]
  · rw [Finset.sum_eq_single (s.2.1 y)]
    · rw [Finset.sum_eq_single (s.2.2 z)]
      · simp [vertex]
      · intro c _ hc
        simp [vertex, Ne.symm hc]
      · simp
    · intro b _ hb
      simp [vertex, Ne.symm hb]
    · simp
  · intro a _ ha
    simp [vertex, Ne.symm ha]
  · simp

/-- proof_shape: bind-only; consumer: result. -/
private theorem normalization_vertex (s : ((Fin 2 → Fin K) × (Fin 2 → Fin K) × (Fin 2 → Fin K))) :
  normalization K (vertex K s) = 1 := by
  have h := vertex_expectation s 0 0 0 (fun _ _ _ => 1)
  simpa [normalization] using h

private def mkStrategy [NeZero K] (a A b B c C : ZMod K) : ((Fin 2 → Fin K) × (Fin 2 → Fin K) ×
  (Fin 2 → Fin K)) :=
  (fun x => if x=0 then (ZMod.finEquiv K).symm a else (ZMod.finEquiv K).symm A,
   fun y => if y=0 then (ZMod.finEquiv K).symm b else (ZMod.finEquiv K).symm B,
   fun z => if z=0 then (ZMod.finEquiv K).symm c else (ZMod.finEquiv K).symm C)

/-- proof_shape: bind-only; consumer: mkStrategy_surjective. -/
private theorem equiv_natCast [NeZero K] (a : Fin K) :
    (ZMod.finEquiv K).symm (a.val : ZMod K) = a := by
  cases K with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k => apply Fin.ext; exact ZMod.val_cast_of_lt a.isLt

/-- proof_shape: bind-only; consumer: I_vertex_mkStrategy. -/
private theorem equiv_val_cast [NeZero K] (a : ZMod K) :
    (((ZMod.finEquiv K).symm a).val : ZMod K) = a := by
  cases K with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k => exact ZMod.natCast_zmod_val a

/-- proof_shape: bind-only; consumer: validity_vertex, rigidity_vertices. -/
private theorem mkStrategy_surjective [NeZero K] (s : ((Fin 2 → Fin K) × (Fin 2 → Fin K) × (Fin 2 →
  Fin K))) :
    mkStrategy (s.1 0).val (s.1 1).val (s.2.1 0).val (s.2.1 1).val
      (s.2.2 0).val (s.2.2 1).val = s := by
  apply Prod.ext
  · funext x
    fin_cases x <;> simp [mkStrategy, equiv_natCast]
  · apply Prod.ext
    · funext y
      fin_cases y <;> simp [mkStrategy, equiv_natCast]
    · funext z
      fin_cases z <;> simp [mkStrategy, equiv_natCast]

/-- proof_shape: bind-only; consumer: I_vertex_mkStrategy. -/
private theorem bracket_cast [NeZero K] (t : ℤ) : bracket K t = ((t : ZMod K).val : ℝ) := by
  unfold bracket
  have h := ZMod.val_intCast (n := K) t
  exact_mod_cast h.symm

/-- proof_shape: bind-only; consumer: validity_vertex, rigidity_vertices, result. -/
private theorem I_vertex_mkStrategy [NeZero K] (a A b B c C : ZMod K) :
    I K (vertex K (mkStrategy a A b B c C)) = (J3 a A b B c C : ℝ) := by
  simp only [I, vertex_expectation]
  simp [mkStrategy]
  simp only [bracket_cast]
  have e1 : (((((ZMod.finEquiv K).symm A).val : ℤ) - ((ZMod.finEquiv K).symm b).val +
    ((ZMod.finEquiv K).symm c).val : ℤ) : ZMod K) = A - b + c := by
    push_cast
    simp only [equiv_val_cast]
  have e2 : (((((ZMod.finEquiv K).symm a).val : ℤ) + ((ZMod.finEquiv K).symm B).val -
    ((ZMod.finEquiv K).symm c).val : ℤ) : ZMod K) = a + B - c := by
    push_cast
    simp only [equiv_val_cast]
  have e3 : ((-(((ZMod.finEquiv K).symm a).val : ℤ) + ((ZMod.finEquiv K).symm b).val +
    ((ZMod.finEquiv K).symm C).val : ℤ) : ZMod K) = -a + b + C := by
    push_cast
    simp only [equiv_val_cast]
  have e4 : ((-(((ZMod.finEquiv K).symm A).val : ℤ) - ((ZMod.finEquiv K).symm B).val -
    ((ZMod.finEquiv K).symm C).val - 1 : ℤ) : ZMod K) = -A - B - C - 1 := by
    push_cast
    simp only [equiv_val_cast]
  simp only [e1, e2, e3, e4, J3, Nat.cast_add]

/-- proof_shape: bind-only; consumer: local_function_representation. -/
private theorem vertex_basis_expansion (s : ((Fin 2 → Fin K) × (Fin 2 → Fin K) × (Fin 2 → Fin K)))
  :
    vertex K s = ∑ x : Fin 2, ∑ y : Fin 2, ∑ z : Fin 2,
      Pi.single ((x,y,z),(s.1 x,s.2.1 y,s.2.2 z)) (1 : ℝ) := by
  classical
  funext q
  rcases q with ⟨⟨x,y,z⟩,a,b,c⟩
  simp only [Finset.sum_apply, Pi.single_apply, Prod.mk.injEq]
  simp [vertex, ite_and, Finset.sum_ite_irrel, eq_comm]

/-- proof_shape: bind-only; consumer: rigidity_vertices. -/
private theorem local_function_representation [NeZero K] (ell : ((Fin 2 × Fin 2 × Fin 2) × (Fin K ×
  Fin K × Fin K) → ℝ) →ₗ[ℝ] ℝ)
    (a A b B c C : ZMod K) :
    ell (vertex K (mkStrategy a A b B c C)) =
    TripLocal (fun x y z a b c => ell (Pi.single ((x,y,z),((ZMod.finEquiv K).symm a,(ZMod.finEquiv
      K).symm b,(ZMod.finEquiv K).symm c)) 1))
      a A b B c C := by
  rw [vertex_basis_expansion]
  simp only [map_sum, TripLocal, mkStrategy]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> rfl

/-- proof_shape: bind-only; consumer: result. -/
private theorem validity_vertex [NeZero K] (hK : 2 ≤ K) (s : ((Fin 2 → Fin K) × (Fin 2 → Fin K) ×
  (Fin 2 → Fin K))) :
    (K : ℝ) - 1 ≤ I K (vertex K s) := by
  rw [← mkStrategy_surjective s, I_vertex_mkStrategy]
  have hh := J3_lower ((s.1 0).val : ZMod K) (s.1 1).val (s.2.1 0).val
    (s.2.1 1).val (s.2.2 0).val (s.2.2 1).val
  have hr : ((K - 1 : ℕ) : ℝ) ≤
      (J3 ((s.1 0).val : ZMod K) (s.1 1).val (s.2.1 0).val
        (s.2.1 1).val (s.2.2 0).val (s.2.2 1).val : ℝ) := by exact_mod_cast hh
  simpa only [Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one] using hr

/-- proof_shape: content; consumer: result. -/
private theorem rigidity_vertices [NeZero K] (hK : 2 ≤ K) (ell : ((Fin 2 × Fin 2 × Fin 2) × (Fin K
  × Fin K × Fin K) → ℝ) →ₗ[ℝ] ℝ)
    (hs : ∀ s : ((Fin 2 → Fin K) × (Fin 2 → Fin K) × (Fin 2 → Fin K)), I K (vertex K s) = (K : ℝ) -
      1 → ell (vertex K s) = 0) :
    ∃ lam : ℝ, ∀ s : ((Fin 2 → Fin K) × (Fin 2 → Fin K) × (Fin 2 → Fin K)),
      ell (vertex K s) = lam * (I K (vertex K s) - ((K : ℝ) - 1)) := by
  let f : Fin 2 → Fin 2 → Fin 2 → ZMod K → ZMod K → ZMod K → ℝ :=
    fun x y z a b c => ell (Pi.single ((x,y,z),((ZMod.finEquiv K).symm a,(ZMod.finEquiv K).symm
      b,(ZMod.finEquiv K).symm c)) 1)
  have htrip : ∀ a A b B c C, J3 a A b B c C = K - 1 → TripLocal f a A b B c C = 0 := by
    intro a A b B c C hJ
    rw [← local_function_representation ell]
    apply hs
    rw [I_vertex_mkStrategy, hJ]
    simp [Nat.cast_sub (by omega : 1 ≤ K)]
  obtain ⟨lam, hlam⟩ := tripartite_rigidity hK f htrip
  refine ⟨lam, ?_⟩
  intro s
  have hh := hlam ((s.1 0).val : ZMod K) (s.1 1).val (s.2.1 0).val
    (s.2.1 1).val (s.2.2 0).val (s.2.2 1).val
  rw [← local_function_representation ell, ← I_vertex_mkStrategy,
    mkStrategy_surjective s] at hh
  exact hh

theorem result : claim := by
  intro K hK
  have : NeZero K := ⟨by omega⟩
  have : Fact (1 < K) := ⟨by omega⟩
  have hv : ∀ p ∈ Set.range (vertex K), (K : ℝ) - 1 ≤ linearI K p := by
    rintro p ⟨s, rfl⟩
    exact validity_vertex hK s
  constructor
  · intro p hp
    exact (convexHull_min hv ((convex_Ici ((K : ℝ) - 1)).linear_preimage (linearI K))) hp
  · let o : ((Fin 2 × Fin 2 × Fin 2) × (Fin K × Fin K × Fin K) → ℝ) := vertex K (mkStrategy 0 0 0 0
    0 0)
    let t : ((Fin 2 × Fin 2 × Fin 2) × (Fin K × Fin K × Fin K) → ℝ) := vertex K (mkStrategy 0 0 0 0
      1 0)
    have ho : o ∈ Set.range (vertex K) := Set.mem_range_self _
    have ht : t ∈ Set.range (vertex K) := Set.mem_range_self _
    have hIo : linearI K o = (K : ℝ) - 1 := by
      change I K (vertex K (mkStrategy 0 0 0 0 0 0)) = _
      rw [I_vertex_mkStrategy]
      have hm : (-1 : ZMod K).val = K - 1 := by
        simpa only [neg_zero, zero_sub, ZMod.val_zero, Nat.sub_zero] using
          val_neg_sub_one (0 : ZMod K)
      simp only [J3, sub_zero, add_zero, neg_zero, zero_sub, ZMod.val_zero, zero_add, hm]
      rw [Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one]
    have hIt : linearI K t ≠ (K : ℝ) - 1 := by
      change I K (vertex K (mkStrategy 0 0 0 0 1 0)) ≠ _
      rw [I_vertex_mkStrategy]
      have hw := sigma_zero_witness (0 : ZMod K) 1 0
      simp only [neg_zero, one_ne_zero, if_false] at hw
      have hkR : (K : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne K)
      intro he
      rw [he, sub_self, mul_one] at hw
      exact hkR hw.symm
    have hn : ∀ p ∈ Set.range (vertex K), normalization K p = 1 := by
      rintro p ⟨s, rfl⟩
      exact normalization_vertex s
    apply D5.S3.QuantumBounds.FacetRigidityBridge.rigidity_facet_bridge (Set.range (vertex K))
      (linearI K)
      (normalization K) ((K : ℝ) - 1) hv hn o ho hIo t ht hIt
    intro ell hell
    obtain ⟨lam, hlam⟩ := rigidity_vertices hK ell (by
      intro s hIs
      exact hell _ (Set.mem_range_self s) hIs)
    refine ⟨lam, ?_⟩
    rintro p ⟨s, rfl⟩
    exact hlam s


end D5.S3.QuantumBounds.MerminCglmpFacet
