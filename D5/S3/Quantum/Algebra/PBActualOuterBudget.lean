/- GID: D5/S3/Quantum/Algebra/PBActualOuterBudget
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/PBActualOuterBudget
   mirror-E: none(waiver:registration-template-not-established)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.Symmetric]
   utility: none
   digest: Supporting vectors read the two actual PB outer calls without descending the original nonlinear response. -/

import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Tactic

/-! Actual original-label PB calls and their represented finite budgets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

/- Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/28045 -/

namespace D5.S3.Quantum.Algebra.PBActualOuterBudget

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- Construct a supporting vector, including the case where the first candidate vanishes. -/
private theorem supporting_vector [Nontrivial H] (n m : H →ₗ[ℝ] H)
    (hn : ∀ v, n (n v) = v) (hm : ∀ v, m (m v) = v)
    (hnm : ∀ v, n (m v) = -m (n v)) :
    ∃ v : H, ‖v‖ = 1 ∧ n v = v := by
  obtain ⟨w, hw⟩ := exists_ne (0 : H)
  have exists_nonzero : ∃ v : H, v ≠ 0 ∧ n v = v := by
    by_cases h : w + n w = 0
    · have hnw : n w = -w := eq_neg_of_add_eq_zero_right h
      refine ⟨m w + n (m w), ?_, ?_⟩
      · have hmw : m w ≠ 0 := by
          intro hz
          have := hm w
          rw [hz, map_zero] at this
          exact hw this.symm
        rw [hnm, hnw, map_neg, neg_neg]
        intro hz
        have hz' : (2 : ℝ) • m w = 0 := by simpa [two_smul] using hz
        exact hmw ((smul_eq_zero.mp hz').resolve_left (by norm_num))
      · simp only [map_add, hn]
        abel
    · exact ⟨w + n w, h, by simp only [map_add, hn]; abel⟩
  obtain ⟨v, hv, hnv⟩ := exists_nonzero
  refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
  · simp [norm_smul, hv]
  · simp [hnv]

/-- A symmetric operator anticommuting with a supported symmetry has zero expectation. -/
private theorem supported_orthogonal (n k : H →ₗ[ℝ] H)
    (hs : n.IsSymmetric) (v : H) (hv : n v = v)
    (hk : ∀ w, n (k w) = -k (n w)) : ⟪v, k v⟫ = 0 := by
  have he := hs v (k v)
  rw [hv, hk, hv, inner_neg_right] at he
  linarith

/-- The complete separate-owner B interface is derived debt, rather than a new raw axiom. -/
structure BDerivedInterface {E : Type*} [AddCommGroup E] [Module ℝ E]
    (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (u : E) (D : E → E → E) : Prop where
  unit_row : ∀ (s : ℝ) (a : E), D (s • u) a = 0
  rotation : ∀ (a b : E) (θ : ℝ), D (Real.cos θ • a + Real.sin θ • b)
    (-Real.sin θ • a + Real.cos θ • b) = D a b
  odd_left : ∀ a b, D (-a) b = -D a b
  odd_right : ∀ a b, D a (-b) = -D a b
  affine_zero : ∀ (a : E) (s t x y : ℝ), D (s • u + x • a) (t • u + y • a) = 0
  square_row : ∀ (a : E) (s : ℝ), D a (s • J a a) = 0

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Original PB, with both actual outer second labels preserved. -/
def PB (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (D : E → E → E) : Prop :=
  ∀ a b c, let ν := D a b - J a c
           let ω := J a b + D a c
           D (b + ν) (c + ω) - D (b - ν) (c - ω) =
             (-2 : ℝ) • (J b ν + J c ω)

/-- A readout is linear on every original label. Multiplication is required only on
its known Jordan subspace L, not on unknown outer D outputs. No response on a quotient
is part of this structure. All vector masses, including zero, occur in P2. -/
structure Readout (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (u : E) (D : E → E → E)
    (L : Submodule ℝ E) where
  op : E →ₗ[ℝ] (H →ₗ[ℝ] H)
  symmetric : ∀ a, (op a).IsSymmetric
  unit : op u = LinearMap.id
  jordan : ∀ a ∈ L, ∀ b ∈ L, op (J a b) =
    (1 / 2 : ℝ) • ((op a).comp (op b) + (op b).comp (op a))
  p2 : ∀ (v : H) a b,
    ⟪v, op (D a b) v⟫ ^ 2 ≤
      ⟪v, op (J a a) v⟫ * ⟪v, op (J b b) v⟫ - ⟪v, op (J a b) v⟫ ^ 2

/-- An expectation of an original label, not a newly available preparation. -/
def reading {J : E →ₗ[ℝ] E →ₗ[ℝ] E} {u : E} {D : E → E → E}
    {L : Submodule ℝ E} (R : Readout (H := H) J u D L) (v : H) : E →ₗ[ℝ] ℝ where
  toFun a := ⟪v, R.op a v⟫
  map_add' a b := by simp [inner_add_right]
  map_smul' r a := by simp [inner_smul_right]

private theorem reading_jordan {J : E →ₗ[ℝ] E →ₗ[ℝ] E} {u : E} {D : E → E → E}
    {L : Submodule ℝ E} (R : Readout (H := H) J u D L)
    {a b : E} (ha : a ∈ L) (hb : b ∈ L) (v : H) :
    reading R v (J a b) = ⟪R.op a v, R.op b v⟫ := by
  simp only [reading, LinearMap.coe_mk, AddHom.coe_mk, R.jordan a ha b hb,
    LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    inner_smul_right, inner_add_right]
  rw [← R.symmetric a v (R.op b v), ← R.symmetric b v (R.op a v), real_inner_comm]
  ring

private theorem anticommuting_inner (e f : H →ₗ[ℝ] H)
    (he : e.IsSymmetric) (hf : f.IsSymmetric)
    (hef : ∀ v, e (f v) = -f (e v)) (v : H) : ⟪e v, f v⟫ = 0 := by
  have h := he v (f v)
  rw [hef, inner_neg_right, ← hf v (e v), real_inner_comm (f v) (e v)] at h
  rw [real_inner_comm]
  linarith

private theorem supporting_readings [Nontrivial H] (e f k : H →ₗ[ℝ] H)
    (he : e.IsSymmetric) (hf : f.IsSymmetric) (hk : k.IsSymmetric)
    (hee : ∀ v, e (e v) = v) (hff : ∀ v, f (f v) = v)
    (hef : ∀ v, e (f v) = -f (e v))
    (hek : ∀ v, e (k v) = -k (e v))
    (hfk : ∀ v, f (k v) = -k (f v))
    (δ c s : ℝ) (hkk : ∀ v, k (k v) = δ^2 • v) (hcs : c^2+s^2=1) :
    ∃ v : H, ⟪v,v⟫ = 1 ∧ ⟪v,e v⟫ = c ∧ ⟪v,f v⟫ = s ∧
      ⟪v,k v⟫ = 0 ∧ ⟪e v,e v⟫ = 1 ∧ ⟪f v,f v⟫ = 1 ∧
      ⟪k v,k v⟫ = δ^2 ∧ ⟪e v,f v⟫ = 0 ∧
      ⟪e v,k v⟫ = 0 ∧ ⟪f v,k v⟫ = 0 := by
  let n := c • e + s • f
  let m := -s • e + c • f
  have hfe (v : H) : f (e v) = -e (f v) := by
    have := hef v
    exact eq_neg_of_add_eq_zero_left (by rw [this]; abel)
  have hn (v : H) : n (n v) = v := by
    change (c • e + s • f) ((c • e + s • f) v) = v
    simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, hee, hff, hfe]
    calc
      _ = (c^2+s^2) • v := by module
      _ = v := by rw [hcs, one_smul]
  have hm (v : H) : m (m v) = v := by
    change (-s • e + c • f) ((-s • e + c • f) v) = v
    simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, hee, hff, hfe]
    calc
      _ = (c^2+s^2) • v := by module
      _ = v := by rw [hcs, one_smul]
  have hnm (v : H) : n (m v) = -m (n v) := by
    change (c • e + s • f) ((-s • e + c • f) v) =
      -(-s • e + c • f) ((c • e + s • f) v)
    simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, hee, hff, hfe]
    module
  obtain ⟨v, hv, hnv⟩ := supporting_vector n m hn hm hnm
  have hvv : ⟪v,v⟫ = 1 := by simpa [hv] using real_inner_self_eq_norm_sq v
  have hns : n.IsSymmetric := by
    intro a b
    simp [n, inner_add_left, inner_smul_left, inner_add_right, inner_smul_right, he a b, hf a b]
  have hmv := supported_orthogonal n m hns v hnv hnm
  have hkv : ⟪v,k v⟫ = 0 := by
    apply supported_orthogonal n k hns v hnv
    intro w
    simp only [n, LinearMap.add_apply, LinearMap.smul_apply, hek, hfk, map_add, map_smul]
    module
  have heq : c*⟪v,e v⟫ + s*⟪v,f v⟫ = 1 := by
    have := congrArg (fun w => ⟪v,w⟫) hnv
    simpa [n, inner_add_right, inner_smul_right, hv] using this
  have hmq : -s*⟪v,e v⟫ + c*⟪v,f v⟫ = 0 := by
    simpa [m, inner_add_right, inner_smul_right] using hmv
  have hce : ⟪v,e v⟫ = c := by
    linear_combination c*heq - s*hmq - ⟪v,e v⟫*hcs
  have hsf : ⟪v,f v⟫ = s := by
    linear_combination s*heq + c*hmq - ⟪v,f v⟫*hcs
  refine ⟨v, hvv, hce, hsf, hkv, ?_, ?_, ?_,
    anticommuting_inner e f he hf hef v,
    anticommuting_inner e k he hk hek v,
    anticommuting_inner f k hf hk hfk v⟩
  · rw [he, hee, hvv]
  · rw [hf, hff, hvv]
  · rw [hk, hkk, inner_smul_right, hvv, mul_one]

/-- The actual known-label fibre, with no assertion about unknown outer responses.
The two axes are mathematical readings of original x,y, not replacement original inputs. -/
structure Fibre {J : E →ₗ[ℝ] E →ₗ[ℝ] E} {u : E} {D : E → E → E}
    {L : Submodule ℝ E} (R : Readout (H := H) J u D L)
    (x y : E) (X Y δ : ℝ) where
  e : H →ₗ[ℝ] H
  f : H →ₗ[ℝ] H
  reads_x : R.op x = X • e
  reads_y : R.op y = Y • f
  symmetric_e : e.IsSymmetric
  symmetric_f : f.IsSymmetric
  square_e : ∀ v, e (e v) = v
  square_f : ∀ v, f (f v) = v
  cross : ∀ v, e (f v) = -f (e v)
  cross_d_left : ∀ v, e (R.op (D x y) v) = -R.op (D x y) (e v)
  cross_d_right : ∀ v, f (R.op (D x y) v) = -R.op (D x y) (f v)
  square_d : ∀ v, R.op (D x y) (R.op (D x y) v) = δ^2 • v

/-- Both P2 budgets are derived for the actual PB calls. Only the operator reading
of omega vanishes; omega itself can be nonzero. The finite inequality includes δ=0.
This conditional readout lemma does not construct central-character fibres, discharge B,
or prove the original operator-square theorem. -/
theorem actual_outer_budget [Nontrivial H]
    (J : E →ₗ[ℝ] E →ₗ[ℝ] E) (u : E) (D : E → E → E)
    (hPB : PB J D) (B : BDerivedInterface J u D)
    (L : Submodule ℝ E) (hu : u ∈ L)
    (hL : ∀ a ∈ L, ∀ b ∈ L, J a b ∈ L)
    (R : Readout (H := H) J u D L)
    (x y : E) (hx : x ∈ L) (hy : y ∈ L) (hd : D x y ∈ L)
    (X Y δ l t : ℝ) (ht : t ≠ 0) (htsq : t^2 = l^2*X^2+1)
    (F : Fibre R x y X Y δ) :
    let z := t • u + l • x
    let ν := D x y - J x z
    let ω := J x y + D x z
    ∃ v : H, ⟪v,v⟫ = 1 ∧
      reading R v (D (y+ν) (z+ω))^2 ≤ X^2/t^2+δ^2 ∧
      reading R v (D (y-ν) (z-ω))^2 ≤ X^2/t^2+δ^2 ∧
      reading R v (D (y+ν) (z+ω)) - reading R v (D (y-ν) (z-ω)) =
        2*l*X^2*Y/t ∧
      l^2*X^2*(X^2*Y^2-δ^2) ≤ X^2+δ^2 := by
  let z := t • u + l • x
  let ν := D x y - J x z
  let ω := J x y + D x z
  have hz : z ∈ L := L.add_mem (L.smul_mem t hu) (L.smul_mem l hx)
  have hzero : D x z = 0 := by
    simpa [z] using B.affine_zero x 0 t 1 l
  have hν : ν ∈ L := L.sub_mem hd (hL x hx z hz)
  have hω : ω ∈ L := by simpa [ω, hzero] using hL x hx y hy
  have hrp : y+ν ∈ L := L.add_mem hy hν
  have hrm : y-ν ∈ L := L.sub_mem hy hν
  have hsp : z+ω ∈ L := L.add_mem hz hω
  have hsm : z-ω ∈ L := L.sub_mem hz hω
  have hcs : (-(l*X)/t)^2 + (1/t)^2 = 1 := by
    field_simp [ht]
    nlinarith [htsq]
  obtain ⟨v, hv, he, hf, hk, hee, hff, hkk, hef, hek, hfk⟩ :=
    supporting_readings F.e F.f (R.op (D x y)) F.symmetric_e F.symmetric_f
      (R.symmetric _) F.square_e F.square_f F.cross F.cross_d_left
      F.cross_d_right δ (-(l*X)/t) (1/t) F.square_d hcs
  have hωop (w : H) : R.op ω w = 0 := by
    simp only [ω, hzero, add_zero, R.jordan x hx y hy,
      F.reads_x, F.reads_y, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.comp_apply, map_smul, F.cross]
    module
  have hzop (w : H) : R.op z w = t • w + (l*X) • F.e w := by
    simp only [z, map_add, map_smul, R.unit, F.reads_x,
      LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply]
    module
  have hνop (w : H) : R.op ν w = R.op (D x y) w -
      (t*X) • F.e w - (l*X^2) • w := by
    simp only [ν, map_sub, LinearMap.sub_apply, R.jordan x hx z hz,
      LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
      F.reads_x, hzop, map_add, map_smul, F.square_e]
    module
  have hp (w : H) : R.op (y+ν) w = Y • F.f w + R.op (D x y) w -
      (t*X) • F.e w - (l*X^2) • w := by
    simp only [map_add, LinearMap.add_apply, F.reads_y, LinearMap.smul_apply, hνop]
    module
  have hm (w : H) : R.op (y-ν) w = Y • F.f w - R.op (D x y) w +
      (t*X) • F.e w + (l*X^2) • w := by
    simp only [map_sub, LinearMap.sub_apply, F.reads_y, LinearMap.smul_apply, hνop]
    module
  have hspop (w : H) : R.op (z+ω) w = t • w + (l*X) • F.e w := by
    simp [hωop, hzop]
  have hsmop (w : H) : R.op (z-ω) w = t • w + (l*X) • F.e w := by
    simp [hωop, hzop]
  have sym (a b : H) : ⟪a,b⟫ = ⟪b,a⟫ := real_inner_comm _ _
  have gram_plus : reading R v (J (y+ν) (y+ν)) * reading R v (J (z+ω) (z+ω)) -
      reading R v (J (y+ν) (z+ω))^2 = X^2/t^2+δ^2 := by
    rw [reading_jordan R hrp hrp, reading_jordan R hsp hsp, reading_jordan R hrp hsp]
    rw [hp, hspop]
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left,
      inner_add_right, inner_sub_right, real_inner_smul_right]
    simp only [hv, he, hf, hk, hee, hff, hkk, hef, hek, hfk,
      sym (F.e v) v, sym (F.f v) v, sym (R.op (D x y) v) v,
      sym (F.f v) (F.e v), sym (R.op (D x y) v) (F.e v),
      sym (R.op (D x y) v) (F.f v)]
    simp only [he, hf, hk, hef, hek, hfk]
    field_simp [ht]
    linear_combination (Y^2*t^2+δ^2*t^2+X^2*((t^2-l^2*X^2)^2+(t^2-l^2*X^2)+1))*htsq
  have gram_minus : reading R v (J (y-ν) (y-ν)) * reading R v (J (z-ω) (z-ω)) -
      reading R v (J (y-ν) (z-ω))^2 = X^2/t^2+δ^2 := by
    rw [reading_jordan R hrm hrm, reading_jordan R hsm hsm, reading_jordan R hrm hsm]
    rw [hm, hsmop]
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left,
      inner_add_right, inner_sub_right, real_inner_smul_right]
    simp only [hv, he, hf, hk, hee, hff, hkk, hef, hek, hfk,
      sym (F.e v) v, sym (F.f v) v, sym (R.op (D x y) v) v,
      sym (F.f v) (F.e v), sym (R.op (D x y) v) (F.e v),
      sym (R.op (D x y) v) (F.f v)]
    simp only [he, hf, hk, hef, hek, hfk]
    field_simp [ht]
    linear_combination (Y^2*t^2+δ^2*t^2+X^2*((t^2-l^2*X^2)^2+(t^2-l^2*X^2)+1))*htsq
  have pp := R.p2 v (y+ν) (z+ω)
  have pm := R.p2 v (y-ν) (z-ω)
  change reading R v (D (y+ν) (z+ω))^2 ≤
    reading R v (J (y+ν) (y+ν)) * reading R v (J (z+ω) (z+ω)) -
      reading R v (J (y+ν) (z+ω))^2 at pp
  change reading R v (D (y-ν) (z-ω))^2 ≤
    reading R v (J (y-ν) (y-ν)) * reading R v (J (z-ω) (z-ω)) -
      reading R v (J (y-ν) (z-ω))^2 at pm
  rw [gram_plus] at pp
  rw [gram_minus] at pm
  have difference : reading R v (D (y+ν) (z+ω)) - reading R v (D (y-ν) (z-ω)) =
      2*l*X^2*Y/t := by
    rw [← map_sub, hPB x y z, map_smul, map_add,
      reading_jordan R hy hν, reading_jordan R hz hω]
    simp only [reading, LinearMap.coe_mk, AddHom.coe_mk, hωop, inner_zero_right,
      add_zero, F.reads_y, LinearMap.smul_apply, hνop,
      inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    simp only [sym (R.op (D x y) v) (F.f v), hfk, sym (F.f v) (F.e v), hef,
      sym (F.f v) v, hf, smul_eq_mul]
    ring
  refine ⟨v, hv, pp, pm, difference, ?_⟩
  have bound : (2*l*X^2*Y/t)^2 ≤ 4*(X^2/t^2+δ^2) := by
    rw [← difference]
    nlinarith [sq_nonneg (reading R v (D (y+ν) (z+ω)) +
      reading R v (D (y-ν) (z-ω)))]
  have bound' := (div_le_iff₀ (sq_pos_iff.mpr ht)).mp
    (show (2*l*X^2*Y)^2/t^2 ≤ 4*(X^2/t^2+δ^2) by simpa [div_pow] using bound)
  field_simp [ht] at bound'
  rw [htsq] at bound'
  nlinarith [bound']

end D5.S3.Quantum.Algebra.PBActualOuterBudget
