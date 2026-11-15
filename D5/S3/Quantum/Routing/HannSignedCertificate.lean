/- GID: D5/S3/Quantum/Routing/HannSignedCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Routing/HannSignedCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Prescribed signed coefficient recursion on actual loaded router records. -/

import D5.S3.Quantum.Routing.HannRouterProfiles
import Mathlib.RingTheory.RootsOfUnity.Complex

/-! Exact signed Fourier records and prescribed recursive address coefficients. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder

namespace D5.S3.Quantum.Routing.HannSignedCertificate

open HannSpatialQram
open HannRouterProfiles (Router routerLabel loadedLabel)
open ReversibleQram (Address)

/-- The prescribed positive-angle third root of unity. -/
def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

private theorem omega_primitive : IsPrimitiveRoot omega 3 :=
  Complex.isPrimitiveRoot_exp 3 (by norm_num)

private theorem omega_cube : omega ^ 3 = 1 := omega_primitive.pow_eq_one

private theorem omega_sum : 1 + omega + omega ^ 2 = 0 := by
  have h := omega_primitive.geom_sum_eq_zero (by norm_num : 1 < 3)
  simpa [Finset.sum_range_succ, add_assoc] using h

private theorem omega_inv : omega⁻¹ = omega ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  calc
    omega * omega ^ 2 = omega ^ 3 := by ring
    _ = 1 := omega_cube

private theorem omega_sq_sq : (omega ^ 2) ^ 2 = omega := by
  calc
    (omega ^ 2) ^ 2 = omega ^ 3 * omega := by ring
    _ = omega := by rw [omega_cube, one_mul]

private theorem omega_sq_inv : (omega ^ 2)⁻¹ = omega := by
  rw [← inv_pow, omega_inv, omega_sq_sq]

private theorem omega_neg_two : omega ^ (-2 : ℤ) = omega := by
  rw [zpow_neg, zpow_ofNat, ← inv_pow, omega_inv, omega_sq_sq]

/-- The label exponents are wait=0, zero=1, one=2. -/
def labelIndex : Qutrit → ℤ
  | .wait => 0
  | .zero => 1
  | .one => 2

/-- The three specified Fourier coordinates, with nonnegative real square roots. -/
def localRecord (q : ℝ) (s : Qutrit) (e : Fin 3) : ℂ :=
  if e = 0 then (Real.sqrt ((1 + 2 * q) / 3) : ℂ)
  else (Real.sqrt ((1 - q) / 3) : ℂ) *
    omega ^ (if e = 1 then labelIndex s else -labelIndex s)

theorem local_upper (s : Qutrit) (e : Fin 3) :
    localRecord 1 s e = localRecord 1 Qutrit.wait e := by
  simp [localRecord]

theorem local_lower (e : Fin 3) :
    localRecord (-(1 / 2 : ℝ)) Qutrit.wait e =
      -localRecord (-(1 / 2 : ℝ)) Qutrit.zero e -
        localRecord (-(1 / 2 : ℝ)) Qutrit.one e := by
  fin_cases e <;>
    norm_num [localRecord, labelIndex, omega_neg_two, omega_inv, omega_sq_inv] <;>
    linear_combination (Real.sqrt (2 : ℝ) : ℂ)⁻¹ * omega_sum

abbrev Environment (n : ℕ) := Router n → Fin 3
abbrev Coeff (n : ℕ) := Address n → ℂ

/-- One assignment is restricted along the actual child coordinates. -/
def restrict (n : ℕ) (q : Router (n + 1) → ℝ) (b : Bool) : Router n → ℝ :=
  fun v => q (some (b, v))

def childEnvironment (n : ℕ) (e : Environment (n + 1)) (b : Bool) : Environment n :=
  fun v => e (some (b, v))

/-- Actual loaded records retain an arbitrary external bus. -/
def record (n : ℕ) (q : Router n → ℝ) (bus : Qutrit)
    (a : Address n) (e : Environment n) : ℂ :=
  ∏ v, localRecord (q v) (loadedLabel n a bus v) (e v)

def vacuumRecord (n : ℕ) (q : Router n → ℝ) (e : Environment n) : ℂ :=
  ∏ v, localRecord (q v) Qutrit.wait (e v)

/-- Complex coefficient synthesis, with the exact address order. -/
def synthesis (n : ℕ) (q : Router n → ℝ) (bus : Qutrit) :
    Coeff n →ₗ[ℂ] (Environment n → ℂ) where
  toFun x e := ∑ a, x a * record n q bus a e
  map_add' x y := by ext e; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by ext e; simp [Finset.mul_sum, mul_assoc]

/-- Zero extension along the selected first address bit. -/
def embed (n : ℕ) (b : Bool) (x : Coeff n) : Coeff (n + 1) :=
  fun a => if a.1 = b then x a.2 else 0

private theorem product_split (n : ℕ) (f : Router (n + 1) → ℂ) :
    (∏ v, f v) = f none * (∏ v : Router n, f (some (false, v))) *
      (∏ v : Router n, f (some (true, v))) := by
  rw [Fintype.prod_option, Fintype.prod_prod_type, Fintype.prod_bool]
  ring

private theorem record_split (n : ℕ) (q : Router (n + 1) → ℝ)
    (bus : Qutrit) (a : Address (n + 1)) (e : Environment (n + 1)) :
    record (n + 1) q bus a e =
      localRecord (q none) (encode a.1) (e none) *
        (if a.1 then vacuumRecord n (restrict n q false) (childEnvironment n e false)
         else record n (restrict n q false) bus a.2 (childEnvironment n e false)) *
        (if a.1 then record n (restrict n q true) bus a.2 (childEnvironment n e true)
         else vacuumRecord n (restrict n q true) (childEnvironment n e true)) := by
  simp only [record, HannRouterProfiles.loaded_label]
  rw [product_split]
  cases a with
  | mk b a =>
    cases b <;>
      simp [routerLabel, programmed, vacuumRecord, restrict, childEnvironment,
        HannRouterProfiles.vacuum_label]

theorem vacuum_split (n : ℕ) (q : Router (n + 1) → ℝ)
    (e : Environment (n + 1)) :
    vacuumRecord (n + 1) q e = localRecord (q none) Qutrit.wait (e none) *
      vacuumRecord n (restrict n q false) (childEnvironment n e false) *
      vacuumRecord n (restrict n q true) (childEnvironment n e true) :=
  product_split n _

private theorem synthesis_embed (n : ℕ) (q : Router (n + 1) → ℝ) (bus : Qutrit)
    (b : Bool) (x : Coeff n) (e : Environment (n + 1)) :
    synthesis (n + 1) q bus (embed n b x) e =
      if b then localRecord (q none) Qutrit.one (e none) *
        vacuumRecord n (restrict n q false) (childEnvironment n e false) *
        synthesis n (restrict n q true) bus x (childEnvironment n e true)
      else localRecord (q none) Qutrit.zero (e none) *
        synthesis n (restrict n q false) bus x (childEnvironment n e false) *
        vacuumRecord n (restrict n q true) (childEnvironment n e true) := by
  change (∑ a, embed n b x a * record (n + 1) q bus a e) = _
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  cases b <;>
    simp [embed, record_split, encode, synthesis, Finset.mul_sum,
      mul_assoc, mul_left_comm, mul_comm]

/-- Ordered coefficient data. The vacuum flag is exactly presence of its representative. -/
structure Output (n : ℕ) where
  dimension : ℕ
  kernel : List (Coeff n)
  representative : Option (Coeff n)

def Output.flag {n : ℕ} (o : Output n) : Bool := o.representative.isSome

/-- Child kernels occur left first, then right, with neither elimination nor rescaling. -/
def inherited (n : ℕ) (l r : Output n) : List (Coeff (n + 1)) :=
  l.kernel.map (embed n false) ++ r.kernel.map (embed n true)

/-- One prescribed step. Only the upper endpoint with two vacua appends a collision. -/
def step (n : ℕ) (q : ℝ) (l r : Output n) : Output (n + 1) :=
  if q = 1 then
    match l.representative, r.representative with
    | some u, some v =>
        ⟨l.dimension + r.dimension - 1,
          inherited n l r ++ [embed n false u - embed n true v], some (embed n false u)⟩
    | some u, none =>
        ⟨l.dimension + r.dimension, inherited n l r, some (embed n false u)⟩
    | none, some v =>
        ⟨l.dimension + r.dimension, inherited n l r, some (embed n true v)⟩
    | none, none => ⟨l.dimension + r.dimension, inherited n l r, none⟩
  else
    ⟨l.dimension + r.dimension, inherited n l r,
      if q = -(1 / 2 : ℝ) then
        match l.representative, r.representative with
        | some u, some v => some (-embed n false u - embed n true v)
        | _, _ => none
      else none⟩

/-- The literal recursive outputs for restrictions of a single common assignment. -/
def outputs : (n : ℕ) → (Router n → ℝ) → Output n
  | 0, _ => ⟨1, [], some (fun _ => 1)⟩
  | n + 1, q => step n (q none)
      (outputs n (restrict n q false)) (outputs n (restrict n q true))

/-- Sound coefficient data and the exact dimension/list accounting. -/
structure Sound (n : ℕ) (q : Router n → ℝ) (bus : Qutrit) (o : Output n) : Prop where
  kernel_sound : ∀ x ∈ o.kernel, synthesis n q bus x = 0
  representative_sound : ∀ u, o.representative = some u →
    synthesis n q bus u = vacuumRecord n q
  dimension_positive : 0 < o.dimension
  count : o.kernel.length + o.dimension = 2 ^ n

private theorem inherited_sound (n : ℕ) (q : Router (n + 1) → ℝ) (bus : Qutrit)
    (l r : Output n) (hl : Sound n (restrict n q false) bus l)
    (hr : Sound n (restrict n q true) bus r) :
    ∀ x ∈ inherited n l r, synthesis (n + 1) q bus x = 0 := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    ext e
    rw [synthesis_embed n q bus false y e]
    simp [hl.kernel_sound y hy]
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    ext e
    rw [synthesis_embed n q bus true y e]
    simp [hr.kernel_sound y hy]

private theorem upper_left (n : ℕ) (q : Router (n + 1) → ℝ) (bus : Qutrit)
    (hq : q none = 1) (u : Coeff n)
    (hu : synthesis n (restrict n q false) bus u = vacuumRecord n (restrict n q false)) :
    synthesis (n + 1) q bus (embed n false u) = vacuumRecord (n + 1) q := by
  ext e
  rw [synthesis_embed n q bus false u e]
  simp only [Bool.false_eq_true, ↓reduceIte, hu, vacuum_split, hq, local_upper]

private theorem upper_right (n : ℕ) (q : Router (n + 1) → ℝ) (bus : Qutrit)
    (hq : q none = 1) (u : Coeff n)
    (hu : synthesis n (restrict n q true) bus u = vacuumRecord n (restrict n q true)) :
    synthesis (n + 1) q bus (embed n true u) = vacuumRecord (n + 1) q := by
  ext e
  rw [synthesis_embed n q bus true u e]
  simp only [↓reduceIte, hu, vacuum_split, hq, local_upper]

private theorem lower_representative (n : ℕ) (q : Router (n + 1) → ℝ) (bus : Qutrit)
    (hq : q none = -(1 / 2 : ℝ)) (u v : Coeff n)
    (hu : synthesis n (restrict n q false) bus u = vacuumRecord n (restrict n q false))
    (hv : synthesis n (restrict n q true) bus v = vacuumRecord n (restrict n q true)) :
    synthesis (n + 1) q bus (-embed n false u - embed n true v) =
      vacuumRecord (n + 1) q := by
  ext e
  simp only [map_sub, map_neg, Pi.sub_apply, Pi.neg_apply]
  rw [synthesis_embed n q bus false u e, synthesis_embed n q bus true v e]
  simp only [
    Bool.false_eq_true, ↓reduceIte, hu, hv, vacuum_split, hq, local_lower]
  ring

private theorem step_sound (n : ℕ) (q : Router (n + 1) → ℝ) (bus : Qutrit)
    (l r : Output n) (hl : Sound n (restrict n q false) bus l)
    (hr : Sound n (restrict n q true) bus r) :
    Sound (n + 1) q bus (step n (q none) l r) := by
  have hk := inherited_sound n q bus l r hl hr
  have hc : (inherited n l r).length = l.kernel.length + r.kernel.length := by
    simp [inherited]
  have hp := hl.dimension_positive
  have hp' := hr.dimension_positive
  have hcount := hl.count
  have hcount' := hr.count
  by_cases hq : q none = 1
  · cases hu : l.representative with
    | none =>
      cases hv : r.representative with
      | none =>
        simp only [step, ite_eq_left hq, hu, hv]
        refine ⟨hk, ?_, by change 0 < l.dimension + r.dimension; omega, ?_⟩
        · simp
        · simp only [hc, pow_succ]; omega
      | some v =>
        simp only [step, ite_eq_left hq, hu, hv]
        refine ⟨hk, ?_, by change 0 < l.dimension + r.dimension; omega, ?_⟩
        · intro u heq
          have heq' : embed n true v = u := by simpa [step, hq, hu, hv] using heq
          subst u
          exact upper_right n q bus hq v (hr.representative_sound v hv)
        · simp only [hc, pow_succ]; omega
    | some u =>
      cases hv : r.representative with
      | none =>
        simp only [step, ite_eq_left hq, hu, hv]
        refine ⟨hk, ?_, by change 0 < l.dimension + r.dimension; omega, ?_⟩
        · intro v heq
          have heq' : embed n false u = v := by simpa [step, hq, hu, hv] using heq
          subst v
          exact upper_left n q bus hq u (hl.representative_sound u hu)
        · simp only [hc, pow_succ]; omega
      | some v =>
        simp only [step, ite_eq_left hq, hu, hv]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro x hx
          have hx' : x ∈ inherited n l r ∨ x = embed n false u - embed n true v := by
            simpa [step, hq, hu, hv] using hx
          rcases hx' with hx | rfl
          · exact hk x hx
          · rw [map_sub, upper_left n q bus hq u (hl.representative_sound u hu),
              upper_right n q bus hq v (hr.representative_sound v hv), sub_self]
        · intro w heq
          have heq' : embed n false u = w := by simpa [step, hq, hu, hv] using heq
          subst w
          exact upper_left n q bus hq u (hl.representative_sound u hu)
        · change 0 < l.dimension + r.dimension - 1; omega
        · simp only [List.length_append,
            List.length_singleton, hc, pow_succ]; omega
  · simp only [step, ite_eq_right hq]
    refine ⟨hk, ?_, by change 0 < l.dimension + r.dimension; omega, ?_⟩
    · intro w heq
      by_cases hq' : q none = -(1 / 2 : ℝ)
      · rw [ite_eq_left hq'] at heq
        cases hu : l.representative <;> cases hv : r.representative <;>
          simp only [hu, hv, Option.some.injEq, reduceCtorEq] at heq
        rename_i u v
        subst w
        exact lower_representative n q bus hq' u v
          (hl.representative_sound u hu) (hr.representative_sound v hv)
      · rw [ite_eq_right hq'] at heq
        cases heq
    · simp only [hc, pow_succ]; omega

/-- Every prescribed kernel vector annihilates the actual synthesis, every chosen vacuum
representative has the prescribed image, and the ordered list has the stated deficit.
This does not assert kernel completeness or false-flag nonmembership. -/
private theorem recursion_sound (n : ℕ) (q : Router n → ℝ) (bus : Qutrit) :
    Sound n q bus (outputs n q) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, by simp [outputs], by simp [outputs]⟩
    · simp [outputs]
    · intro u hu
      have hu' : (fun _ : Address 0 => (1 : ℂ)) = u := by simpa [outputs] using hu
      subst u
      ext e
      simp [synthesis, record, vacuumRecord]
  | succ n ih =>
    exact step_sound n q bus _ _ (ih (restrict n q false)) (ih (restrict n q true))

/-- A fixed nonzero vacuum coordinate, including the negative endpoint. -/
def vacuumCoordinate (n : ℕ) (q : Router n → ℝ) : Environment n :=
  fun v => if q v = -(1 / 2 : ℝ) then 1 else 0

private theorem vacuum_nonzero (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v) : vacuumRecord n q ≠ 0 := by
  have hp : vacuumRecord n q (vacuumCoordinate n q) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    by_cases hv : q v = -(1 / 2 : ℝ)
    · simp only [vacuumCoordinate, hv, ↓reduceIte]
      norm_num [localRecord, labelIndex]
    · have hstrict : -(1 / 2 : ℝ) < q v := lt_of_le_of_ne (hq v) (Ne.symm hv)
      have hpos : 0 < (1 + 2 * q v) / 3 := by linarith
      rw [show vacuumCoordinate n q v = 0 from ite_eq_right hv]
      change (Real.sqrt ((1 + 2 * q v) / 3) : ℂ) ≠ 0
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hpos))
  intro hz
  exact hp (congrFun hz _)

private def embedLinear (n : ℕ) (b : Bool) : Coeff n →ₗ[ℂ] Coeff (n + 1) where
  toFun := embed n b
  map_add' x y := by ext a; by_cases h : a.1 = b <;> simp [embed, h]
  map_smul' c x := by ext a; by_cases h : a.1 = b <;> simp [embed, h]

private theorem embed_injective (n : ℕ) (b : Bool) :
    Function.Injective (embedLinear n b) := by
  intro x y h
  ext a
  simpa [embedLinear, embed] using congrFun h (b, a)

private theorem embed_disjoint (n : ℕ) :
    Disjoint (LinearMap.range (embedLinear n false)) (LinearMap.range (embedLinear n true)) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, hv⟩ := hy
  have hu : u = 0 := by
    ext a
    simpa [embedLinear, embed] using (congrFun hv (false, a)).symm
  simp [hu]

/-- Both order and independence are retained: no repeated vector is collapsed to a set. -/
def ListIndependent (n : ℕ) (L : List (Coeff n)) : Prop :=
  L.Nodup ∧ LinearIndepOn ℂ id {x | x ∈ L}

private theorem inherited_independent (n : ℕ) (l r : Output n)
    (hl : ListIndependent n l.kernel) (hr : ListIndependent n r.kernel) :
    ListIndependent (n + 1) (inherited n l r) := by
  let A : Set (Coeff (n + 1)) := embedLinear n false '' {x | x ∈ l.kernel}
  let B : Set (Coeff (n + 1)) := embedLinear n true '' {x | x ∈ r.kernel}
  have ha : LinearIndepOn ℂ id A := hl.2.id_imageₛ (embed_injective n false).injOn
  have hb : LinearIndepOn ℂ id B := hr.2.id_imageₛ (embed_injective n true).injOn
  have hsa : Submodule.span ℂ A ≤ LinearMap.range (embedLinear n false) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have hsb : Submodule.span ℂ B ≤ LinearMap.range (embedLinear n true) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have hd : Disjoint (Submodule.span ℂ A) (Submodule.span ℂ B) :=
    (embed_disjoint n).mono hsa hsb
  have hs : {x | x ∈ inherited n l r} = A ∪ B := by
    ext x
    simp [inherited, A, B, embedLinear]
  refine ⟨?_, hs ▸ ha.id_union hb hd⟩
  apply List.Nodup.append (List.Nodup.map (embed_injective n false) hl.1)
    (List.Nodup.map (embed_injective n true) hr.1)
  intro x hx hy
  have hxa : x ∈ A := by simpa [A, embedLinear] using hx
  have hxb : x ∈ B := by simpa [B, embedLinear] using hy
  have hz := Submodule.disjoint_def.mp hd x (Submodule.subset_span hxa)
    (Submodule.subset_span hxb)
  have hnot : (0 : Coeff (n + 1)) ∉ A := by simpa using ha.zero_notMem_image
  exact hnot (hz ▸ hxa)

private def leftObservation (n : ℕ) (q : Router (n + 1) → ℝ) (bus : Qutrit) :
    Coeff (n + 1) →ₗ[ℂ] (Environment n → ℂ) :=
  (synthesis n (restrict n q false) bus).comp ({
    toFun := fun x a => x (false, a)
    map_add' := by intros; rfl
    map_smul' := by intros; rfl } : Coeff (n + 1) →ₗ[ℂ] Coeff n)

private theorem collision_outside (n : ℕ) (q : Router (n + 1) → ℝ) (bus : Qutrit)
    (l r : Output n) (hl : Sound n (restrict n q false) bus l)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v) (u v : Coeff n)
    (hu : l.representative = some u) :
    embed n false u - embed n true v ∉
      Submodule.span ℂ {x | x ∈ inherited n l r} := by
  have hs : Submodule.span ℂ {x | x ∈ inherited n l r} ≤
      LinearMap.ker (leftObservation n q bus) := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      change synthesis n (restrict n q false) bus (fun a => embed n false y (false, a)) = 0
      simpa [embed] using hl.kernel_sound y hy
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      change synthesis n (restrict n q false) bus (fun a => embed n true y (false, a)) = 0
      simp only [embed, Bool.false_eq_true, ↓reduceIte]
      exact map_zero _
  intro hc
  have he := hs hc
  change synthesis n (restrict n q false) bus
    (fun a => (embed n false u - embed n true v) (false, a)) = 0 at he
  have he' : synthesis n (restrict n q false) bus u = 0 := by simpa [embed] using he
  rw [hl.representative_sound u hu] at he'
  exact vacuum_nonzero n (restrict n q false) (fun w => hq (some (false, w))) he'

private theorem step_independent (n : ℕ) (q : Router (n + 1) → ℝ) (bus : Qutrit)
    (l r : Output n) (hl : Sound n (restrict n q false) bus l)
    (il : ListIndependent n l.kernel) (ir : ListIndependent n r.kernel)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v) :
    ListIndependent (n + 1) (step n (q none) l r).kernel := by
  have hi := inherited_independent n l r il ir
  by_cases hq' : q none = 1
  · cases hu : l.representative <;> cases hv : r.representative <;>
      simp only [step, ite_eq_left hq', hu, hv]
    · exact hi
    · exact hi
    · exact hi
    · rename_i u v
      have hc := collision_outside n q bus l r hl hq u v hu
      have hn : embed n false u - embed n true v ∉ inherited n l r :=
        fun h => hc (Submodule.subset_span h)
      refine ⟨?_, ?_⟩
      · simpa only [List.concat_eq_append] using (List.nodup_concat _ _).mpr ⟨hn, hi.1⟩
      · have he : {x | x ∈ inherited n l r ++ [embed n false u - embed n true v]} =
          insert (embed n false u - embed n true v) {x | x ∈ inherited n l r} := by
          ext x; simp [or_comm]
        rw [he]
        exact hi.2.id_insert hc
  · simpa only [step, ite_eq_right hq'] using hi

/-- The literal recursive list is independent and sound at every height and bus, and each
preferred representative synthesizes the actual vacuum. Completeness is a separate condition. -/
private theorem recursion_certificate (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v) (bus : Qutrit) :
    Sound n q bus (outputs n q) ∧ ListIndependent n (outputs n q).kernel := by
  refine ⟨recursion_sound n q bus, ?_⟩
  induction n with
  | zero =>
    constructor
    · simp [outputs]
    · simp [outputs]
  | succ n ih =>
    exact step_independent n q bus _ _
      (recursion_sound n (restrict n q false) bus)
      (ih _ (fun w => hq (some (false, w))))
      (ih _ (fun w => hq (some (true, w)))) hq

private theorem local_equation (q : ℝ) (hq : -(1 / 2 : ℝ) ≤ q) (hq' : q < 1)
    (a b c : ℂ)
    (h : ∀ e, localRecord q Qutrit.zero e * a + localRecord q Qutrit.one e * b =
      localRecord q Qutrit.wait e * c) :
    a = -c ∧ b = -c ∧ (q ≠ -(1 / 2 : ℝ) → c = 0) := by
  have hb : (Real.sqrt ((1 - q) / 3) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by linarith)))
  have h1 : omega * a + omega ^ 2 * b = c := by
    apply mul_left_cancel₀ hb
    have hh := h 1
    norm_num only [localRecord, labelIndex, Fin.reduceEq, ite_false, ite_true,
      zpow_one, zpow_ofNat, zpow_zero, mul_one] at hh
    linear_combination hh
  have h2 : omega ^ 2 * a + omega * b = c := by
    apply mul_left_cancel₀ hb
    have hh := h 2
    norm_num only [localRecord, labelIndex, Fin.reduceEq, ite_false, zpow_neg_one,
      zpow_neg, zpow_ofNat, zpow_zero, pow_one, pow_zero, mul_one, omega_inv, omega_sq_inv] at hh
    linear_combination hh
  have hd : omega - omega ^ 2 ≠ 0 := by
    intro he
    have he' : omega * (omega - 1) = 0 := by linear_combination -he
    rcases mul_eq_zero.mp he' with he' | he'
    · exact omega_primitive.ne_zero (by norm_num) he'
    · exact omega_primitive.ne_one (by norm_num) (sub_eq_zero.mp he')
  have hab : a = b := by
    have he : (omega - omega ^ 2) * (a - b) = 0 := by linear_combination h1 - h2
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hd)
  have ha : a = -c := by
    linear_combination a * omega_sum - h1 + omega ^ 2 * (hab.symm)
  have hbneg : b = -c := hab ▸ ha
  refine ⟨ha, hbneg, ?_⟩
  intro hneq
  have hstrict : -(1 / 2 : ℝ) < q := lt_of_le_of_ne hq (Ne.symm hneq)
  have ha0 : (Real.sqrt ((1 + 2 * q) / 3) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by linarith)))
  have h0 : a + b = c := by
    apply mul_left_cancel₀ ha0
    have hh := h 0
    norm_num only [localRecord, Fin.reduceEq, ite_true, Complex.ofReal_one, one_mul] at hh
    linear_combination hh
  linear_combination (ha + hbneg - h0) / 3

private def joinEnvironment (n : ℕ) (i : Fin 3) (l r : Environment n) :
    Environment (n + 1)
  | none => i
  | some (b, v) => if b then r v else l v

private theorem childEnvironment_join_left (n : ℕ) (i : Fin 3) (l r : Environment n) :
    childEnvironment n (joinEnvironment n i l r) false = l := rfl

private theorem childEnvironment_join_right (n : ℕ) (i : Fin 3) (l r : Environment n) :
    childEnvironment n (joinEnvironment n i l r) true = r := rfl

def childCoeff (n : ℕ) (x : Coeff (n + 1)) (b : Bool) : Coeff n :=
  fun a => x (b, a)

private theorem coefficient_split (n : ℕ) (x : Coeff (n + 1)) :
    x = embed n false (childCoeff n x false) + embed n true (childCoeff n x true) := by
  ext a
  cases a with
  | mk b a => cases b <;> simp [embed, childCoeff]

theorem synthesis_split (n : ℕ) (q : Router (n + 1) → ℝ) (bus : Qutrit)
    (x : Coeff (n + 1)) (e : Environment (n + 1)) :
    synthesis (n + 1) q bus x e =
      localRecord (q none) Qutrit.zero (e none) *
        synthesis n (restrict n q false) bus (childCoeff n x false) (childEnvironment n e false) *
        vacuumRecord n (restrict n q true) (childEnvironment n e true) +
      localRecord (q none) Qutrit.one (e none) *
        vacuumRecord n (restrict n q false) (childEnvironment n e false) *
        synthesis n (restrict n q true) bus (childCoeff n x true) (childEnvironment n e true) := by
  conv_lhs => rw [coefficient_split n x]
  rw [map_add, Pi.add_apply, synthesis_embed n q bus false _ e,
    synthesis_embed n q bus true _ e]
  rfl

theorem below_upper_relation (n : ℕ) (q : Router (n + 1) → ℝ) (bus : Qutrit)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v) (hr : q none < 1) (x : Coeff (n + 1)) (c : ℂ)
    (hx : synthesis (n + 1) q bus x = c • vacuumRecord (n + 1) q) :
    synthesis n (restrict n q false) bus (childCoeff n x false) =
        -c • vacuumRecord n (restrict n q false) ∧
      synthesis n (restrict n q true) bus (childCoeff n x true) =
        -c • vacuumRecord n (restrict n q true) ∧
      (q none ≠ -(1 / 2 : ℝ) → c = 0) := by
  obtain ⟨el, hel⟩ := Function.ne_iff.mp
    (vacuum_nonzero n (restrict n q false) (fun w => hq (some (false, w))))
  obtain ⟨er, her⟩ := Function.ne_iff.mp
    (vacuum_nonzero n (restrict n q true) (fun w => hq (some (true, w))))
  have hlocal (l r : Environment n) := local_equation (q none) (hq none) hr
    (synthesis n (restrict n q false) bus (childCoeff n x false) l *
      vacuumRecord n (restrict n q true) r)
    (vacuumRecord n (restrict n q false) l *
      synthesis n (restrict n q true) bus (childCoeff n x true) r)
    (c * vacuumRecord n (restrict n q false) l * vacuumRecord n (restrict n q true) r)
    (by
      intro i
      have he := congrFun hx (joinEnvironment n i l r)
      rw [synthesis_split n q bus x (joinEnvironment n i l r), Pi.smul_apply, vacuum_split] at he
      simp only [childEnvironment_join_left, childEnvironment_join_right,
        joinEnvironment, smul_eq_mul] at he
      linear_combination he)
  refine ⟨?_, ?_, ?_⟩
  · ext e
    apply mul_right_cancel₀ her
    have he := (hlocal e er).1
    simpa only [Pi.smul_apply, smul_eq_mul, neg_mul, mul_assoc] using he
  · ext e
    apply mul_left_cancel₀ hel
    have he := (hlocal el e).2.1
    change vacuumRecord n (restrict n q false) el * _ =
      vacuumRecord n (restrict n q false) el * (-c * vacuumRecord n (restrict n q true) e)
    linear_combination he
  · intro hneq
    have he := (hlocal el er).2.2 hneq
    exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_right her)).resolve_right hel

theorem upper_relation (n : ℕ) (q : Router (n + 1) → ℝ) (bus : Qutrit)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v) (hr : q none = 1) (x : Coeff (n + 1)) (c : ℂ)
    (hx : synthesis (n + 1) q bus x = c • vacuumRecord (n + 1) q) :
    ∃ z : ℂ,
      synthesis n (restrict n q false) bus (childCoeff n x false) =
        z • vacuumRecord n (restrict n q false) ∧
      synthesis n (restrict n q true) bus (childCoeff n x true) =
        (c - z) • vacuumRecord n (restrict n q true) := by
  obtain ⟨el, hel⟩ := Function.ne_iff.mp
    (vacuum_nonzero n (restrict n q false) (fun w => hq (some (false, w))))
  obtain ⟨er, her⟩ := Function.ne_iff.mp
    (vacuum_nonzero n (restrict n q true) (fun w => hq (some (true, w))))
  have he (l r : Environment n) :
      synthesis n (restrict n q false) bus (childCoeff n x false) l *
          vacuumRecord n (restrict n q true) r +
      vacuumRecord n (restrict n q false) l *
          synthesis n (restrict n q true) bus (childCoeff n x true) r =
      c * vacuumRecord n (restrict n q false) l * vacuumRecord n (restrict n q true) r := by
    have hh := congrFun hx (joinEnvironment n 0 l r)
    rw [synthesis_split n q bus x (joinEnvironment n 0 l r), Pi.smul_apply, vacuum_split] at hh
    norm_num only [childEnvironment_join_left, childEnvironment_join_right,
      joinEnvironment, hr, localRecord, Pi.smul_apply, smul_eq_mul,
      Fin.reduceEq, ite_true, Complex.ofReal_one, one_mul] at hh
    linear_combination hh
  let z := synthesis n (restrict n q false) bus (childCoeff n x false) el /
    vacuumRecord n (restrict n q false) el
  have hz : z * vacuumRecord n (restrict n q false) el =
      synthesis n (restrict n q false) bus (childCoeff n x false) el :=
    div_mul_cancel₀ _ hel
  have hright : synthesis n (restrict n q true) bus (childCoeff n x true) =
      (c - z) • vacuumRecord n (restrict n q true) := by
    ext e
    apply mul_left_cancel₀ hel
    change vacuumRecord n (restrict n q false) el * _ =
      vacuumRecord n (restrict n q false) el * ((c - z) * vacuumRecord n (restrict n q true) e)
    linear_combination he el e + hz * vacuumRecord n (restrict n q true) e
  refine ⟨z, ?_, hright⟩
  ext e
  apply mul_right_cancel₀ her
  have hh := he e er
  rw [hright] at hh
  simp only [Pi.smul_apply, smul_eq_mul] at hh
  change _ = (z * vacuumRecord n (restrict n q false) e) * vacuumRecord n (restrict n q true) er
  linear_combination hh

/-- Completeness and the two directions of pointed vacuum membership. -/
structure Complete (n : ℕ) (q : Router n → ℝ) (bus : Qutrit) (o : Output n) : Prop where
  kernel_complete : ∀ x, synthesis n q bus x = 0 →
    x ∈ Submodule.span ℂ {y | y ∈ o.kernel}
  vacuum_iff : vacuumRecord n q ∈ LinearMap.range (synthesis n q bus) ↔ o.flag = true

private theorem scaled_vacuum_range (n : ℕ) (q : Router n → ℝ) (bus : Qutrit)
    (x : Coeff n) (z : ℂ) (hz : z ≠ 0)
    (hx : synthesis n q bus x = z • vacuumRecord n q) :
    vacuumRecord n q ∈ LinearMap.range (synthesis n q bus) := by
  refine ⟨z⁻¹ • x, ?_⟩
  rw [map_smul, hx, smul_smul, inv_mul_cancel₀ hz, one_smul]

private theorem absent_scalar_zero (n : ℕ) (q : Router n → ℝ) (bus : Qutrit)
    (o : Output n) (ho : Complete n q bus o) (hu : o.representative = none)
    (x : Coeff n) (z : ℂ) (hx : synthesis n q bus x = z • vacuumRecord n q) : z = 0 := by
  by_contra hz
  have h := ho.vacuum_iff.mp (scaled_vacuum_range n q bus x z hz hx)
  simp [Output.flag, hu] at h

private theorem embed_mem_inherited (n : ℕ) (l r : Output n) (b : Bool) (x : Coeff n)
    (hx : x ∈ Submodule.span ℂ {y | y ∈ if b then r.kernel else l.kernel}) :
    embed n b x ∈ Submodule.span ℂ {y | y ∈ inherited n l r} := by
  have he := Submodule.apply_mem_span_image_of_mem_span (embedLinear n b) hx
  apply Submodule.span_mono _ he
  rintro y ⟨z, hz, rfl⟩
  cases b
  · apply List.mem_append_left
    exact List.mem_map.mpr ⟨z, hz, rfl⟩
  · apply List.mem_append_right
    exact List.mem_map.mpr ⟨z, hz, rfl⟩

private theorem inherited_complete (n : ℕ) (q : Router (n + 1) → ℝ) (bus : Qutrit)
    (l r : Output n) (hl : Complete n (restrict n q false) bus l)
    (hr : Complete n (restrict n q true) bus r) (x : Coeff (n + 1))
    (hx0 : synthesis n (restrict n q false) bus (childCoeff n x false) = 0)
    (hx1 : synthesis n (restrict n q true) bus (childCoeff n x true) = 0) :
    x ∈ Submodule.span ℂ {y | y ∈ inherited n l r} := by
  rw [coefficient_split n x]
  exact Submodule.add_mem _
    (embed_mem_inherited n l r false _ (hl.kernel_complete _ hx0))
    (embed_mem_inherited n l r true _ (hr.kernel_complete _ hx1))

private theorem step_kernel_complete (n : ℕ) (q : Router (n + 1) → ℝ) (bus : Qutrit)
    (l r : Output n) (sl : Sound n (restrict n q false) bus l)
    (sr : Sound n (restrict n q true) bus r)
    (cl : Complete n (restrict n q false) bus l) (cr : Complete n (restrict n q true) bus r)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v) (hq' : q none ≤ 1)
    (x : Coeff (n + 1)) (hx : synthesis (n + 1) q bus x = 0) :
    x ∈ Submodule.span ℂ {y | y ∈ (step n (q none) l r).kernel} := by
  by_cases hroot : q none = 1
  · obtain ⟨z, hz0, hz1⟩ := upper_relation n q bus hq hroot x 0 (by simpa using hx)
    simp only [zero_sub] at hz1
    have hzero (hz : z = 0) : x ∈ Submodule.span ℂ {y | y ∈ inherited n l r} := by
      apply inherited_complete n q bus l r cl cr x
      · simpa [hz] using hz0
      · simpa [hz] using hz1
    cases hu : l.representative with
    | none =>
      have hz := absent_scalar_zero n (restrict n q false) bus l cl hu _ z hz0
      cases hv : r.representative <;> simpa only [step, ite_eq_left hroot, hu, hv] using hzero hz
    | some u =>
      cases hv : r.representative with
      | none =>
        have hz := absent_scalar_zero n (restrict n q true) bus r cr hv _ (-z) hz1
        have hz' : z = 0 := neg_eq_zero.mp hz
        simpa only [step, ite_eq_left hroot, hu, hv] using hzero hz'
      | some v =>
        simp only [step, ite_eq_left hroot, hu, hv]
        let N := Submodule.span ℂ {y | y ∈ inherited n l r ++ [embed n false u - embed n true v]}
        have hs : Submodule.span ℂ {y | y ∈ inherited n l r} ≤ N :=
          Submodule.span_mono (by intro y hy; exact List.mem_append_left _ hy)
        have hk0 : synthesis n (restrict n q false) bus
            (childCoeff n x false - z • u) = 0 := by
          rw [map_sub, map_smul, hz0, sl.representative_sound u hu, sub_self]
        have hk1 : synthesis n (restrict n q true) bus
            (childCoeff n x true + z • v) = 0 := by
          rw [map_add, map_smul, hz1, sr.representative_sound v hv, neg_smul, neg_add_cancel]
        have he0 := hs (embed_mem_inherited n l r false _ (cl.kernel_complete _ hk0))
        have he1 := hs (embed_mem_inherited n l r true _ (cr.kernel_complete _ hk1))
        have hc : embed n false u - embed n true v ∈ N :=
          Submodule.subset_span (by simp)
        have heq : x = embed n false (childCoeff n x false - z • u) +
            embed n true (childCoeff n x true + z • v) +
              z • (embed n false u - embed n true v) := by
          ext a
          cases a with
          | mk b a => cases b <;> simp [embed, childCoeff]
        rw [heq]
        exact Submodule.add_mem N (Submodule.add_mem N he0 he1) (Submodule.smul_mem N z hc)
  · have hl := below_upper_relation n q bus hq (lt_of_le_of_ne hq' hroot) x 0 (by simpa using hx)
    have he := inherited_complete n q bus l r cl cr x (by simpa using hl.1) (by simpa using hl.2.1)
    simpa only [step, ite_eq_right hroot] using he

private theorem step_vacuum_forward (n : ℕ) (q : Router (n + 1) → ℝ) (bus : Qutrit)
    (l r : Output n) (cl : Complete n (restrict n q false) bus l)
    (cr : Complete n (restrict n q true) bus r)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v) (hq' : q none ≤ 1)
    (h : vacuumRecord (n + 1) q ∈ LinearMap.range (synthesis (n + 1) q bus)) :
    (step n (q none) l r).flag = true := by
  obtain ⟨x, hx⟩ := h
  by_cases hroot : q none = 1
  · obtain ⟨z, hz0, hz1⟩ := upper_relation n q bus hq hroot x 1 (by simpa using hx)
    cases hu : l.representative with
    | some u => cases hv : r.representative <;> simp [step, hroot, hu, hv, Output.flag]
    | none =>
      have hz := absent_scalar_zero n (restrict n q false) bus l cl hu _ z hz0
      have hrange : vacuumRecord n (restrict n q true) ∈
          LinearMap.range (synthesis n (restrict n q true) bus) :=
        ⟨childCoeff n x true, by simpa [hz] using hz1⟩
      have hflag := cr.vacuum_iff.mp hrange
      cases hv : r.representative <;> simp_all [Output.flag, step]
  · have hh := below_upper_relation n q bus hq (lt_of_le_of_ne hq' hroot) x 1 (by simpa using hx)
    have hlow : q none = -(1 / 2 : ℝ) := by
      by_contra he
      exact one_ne_zero (hh.2.2 he)
    have hlflag := cl.vacuum_iff.mp
      (scaled_vacuum_range n (restrict n q false) bus _ (-1) (by norm_num) hh.1)
    have hrflag := cr.vacuum_iff.mp
      (scaled_vacuum_range n (restrict n q true) bus _ (-1) (by norm_num) hh.2.1)
    cases hu : l.representative <;> cases hv : r.representative <;>
      simp_all [step, Output.flag]

private theorem step_complete (n : ℕ) (q : Router (n + 1) → ℝ) (bus : Qutrit)
    (l r : Output n) (sl : Sound n (restrict n q false) bus l)
    (sr : Sound n (restrict n q true) bus r)
    (cl : Complete n (restrict n q false) bus l) (cr : Complete n (restrict n q true) bus r)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v) (hq' : q none ≤ 1) :
    Complete (n + 1) q bus (step n (q none) l r) := by
  refine ⟨step_kernel_complete n q bus l r sl sr cl cr hq hq', ?_⟩
  refine ⟨step_vacuum_forward n q bus l r cl cr hq hq', ?_⟩
  intro hflag
  have hs := step_sound n q bus l r sl sr
  cases hu : (step n (q none) l r).representative with
  | none => simp [Output.flag, hu] at hflag
  | some u => exact ⟨u, hs.representative_sound u hu⟩

private theorem recursion_complete (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v) (hq' : ∀ v, q v ≤ 1) (bus : Qutrit) :
    Complete n q bus (outputs n q) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro x hx
      have hx' : x = 0 := by
        ext a
        have he := congrFun hx (fun v => nomatch v)
        simpa [synthesis, record] using he
      simp [hx', outputs]
    · constructor
      · intro _; rfl
      · intro _
        exact ⟨fun _ => 1, (recursion_sound 0 q bus).representative_sound _ rfl⟩
  | succ n ih =>
    exact step_complete n q bus _ _
      (recursion_sound n (restrict n q false) bus)
      (recursion_sound n (restrict n q true) bus)
      (ih _ (fun w => hq (some (false, w))) (fun w => hq' (some (false, w))))
      (ih _ (fun w => hq (some (true, w))) (fun w => hq' (some (true, w))))
      hq (hq' none)

private theorem list_get_independent (n : ℕ) (L : List (Coeff n))
    (h : ListIndependent n L) : LinearIndependent ℂ L.get := by
  exact h.2.comp (fun i => ⟨L.get i, List.get_mem L i⟩)
    (fun i j he => h.1.injective_get (congrArg Subtype.val he))

private theorem list_get_range (n : ℕ) (L : List (Coeff n)) :
    Set.range L.get = {y | y ∈ L} := by
  ext y
  simp only [Set.mem_range, Set.mem_ofPred_eq, List.mem_iff_get]

/-- Exact all-height certificate for the prescribed ordered signed recursion.
Every complex kernel vector has a unique expansion in that literal list. -/
private theorem coefficient_certificate (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v) (hq' : ∀ v, q v ≤ 1) (bus : Qutrit) :
    Module.finrank ℂ (LinearMap.range (synthesis n q bus)) = (outputs n q).dimension ∧
    (outputs n q).kernel.length = 2 ^ n - (outputs n q).dimension ∧
    (vacuumRecord n q ∈ LinearMap.range (synthesis n q bus) ↔ (outputs n q).flag = true) ∧
    (∀ u, (outputs n q).representative = some u → synthesis n q bus u = vacuumRecord n q) ∧
    (∀ x, synthesis n q bus x = 0 ↔
      ∃! α : Fin (outputs n q).kernel.length → ℂ,
        x = ∑ i, α i • (outputs n q).kernel.get i) := by
  obtain ⟨hs, hi⟩ := recursion_certificate n q hq bus
  have hc := recursion_complete n q hq hq' bus
  have hli := list_get_independent n (outputs n q).kernel hi
  have hker : LinearMap.ker (synthesis n q bus) =
      Submodule.span ℂ {y | y ∈ (outputs n q).kernel} := by
    apply le_antisymm
    · intro x hx
      exact hc.kernel_complete x hx
    · apply Submodule.span_le.mpr
      intro y hy
      exact hs.kernel_sound y hy
  have hdimker : Module.finrank ℂ (LinearMap.ker (synthesis n q bus)) =
      (outputs n q).kernel.length := by
    rw [hker, ← list_get_range]
    simpa only [Fintype.card_fin] using finrank_span_eq_card hli
  have hdim : Module.finrank ℂ (Coeff n) = 2 ^ n := by
    simpa only [Module.finrank_pi] using HannRouterDephasing.address_card n
  have hrank := (synthesis n q bus).finrank_range_add_finrank_ker
  rw [hdimker, hdim] at hrank
  have hcount := hs.count
  refine ⟨by omega, by omega, hc.vacuum_iff, hs.representative_sound, ?_⟩
  intro x
  constructor
  · intro hx
    have hm := hc.kernel_complete x hx
    rw [← list_get_range, Submodule.mem_span_range_iff_exists_fun] at hm
    obtain ⟨a, ha⟩ := hm
    refine ⟨a, ha.symm, ?_⟩
    intro b hb
    exact funext (Fintype.linearIndependent_iffₛ.mp hli b a (hb.symm.trans ha.symm))
  · rintro ⟨a, ha, _⟩
    rw [ha, map_sum]
    simp only [map_smul]
    have hz (i : Fin (outputs n q).kernel.length) :=
      hs.kernel_sound ((outputs n q).kernel.get i) (List.get_mem _ i)
    simp only [hz, smul_zero, Finset.sum_const_zero]

instance environmentFintype (n : ℕ) : Fintype (Environment n) := by
  classical
  unfold Environment
  infer_instance

/-- The actual synthesis matrix has environment rows and address columns. -/
def recordMatrix (n : ℕ) (q : Router n → ℝ) (bus : Qutrit) :
    Matrix (Environment n) (Address n) ℂ := fun e a => record n q bus a e

def standardGram (n : ℕ) (q : Router n → ℝ) (bus : Qutrit) :
    Matrix (Address n) (Address n) ℂ :=
  (recordMatrix n q bus).conjTranspose * recordMatrix n q bus

/-- The density orientation conjugates the second record. -/
def densityGram (n : ℕ) (q : Router n → ℝ) (bus : Qutrit) :
    Matrix (Address n) (Address n) ℂ :=
  fun a b => ∑ e, record n q bus a e * conj (record n q bus b e)

private theorem local_overlap (q : ℝ) (hq : -(1 / 2 : ℝ) ≤ q) (hq' : q ≤ 1)
    (s t : Qutrit) :
    (∑ e : Fin 3, conj (localRecord q s e) * localRecord q t e) =
      ((if s = t then 1 else q : ℝ) : ℂ) := by
  have hw : conj omega = omega ^ 2 := by
    rw [← Complex.inv_eq_conj (omega_primitive.norm'_eq_one (by norm_num)), omega_inv]
  have ha : (Real.sqrt ((1 + 2 * q) / 3) : ℂ) ^ 2 = (((1 + 2 * q) / 3 : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ (1 + 2 * q) / 3 by linarith)
  have hb : (Real.sqrt ((1 - q) / 3) : ℂ) ^ 2 = (((1 - q) / 3 : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (show 0 ≤ (1 - q) / 3 by linarith)
  have hf : omega ^ 4 = omega := by
    calc
      omega ^ 4 = omega ^ 3 * omega := by ring
      _ = omega := by rw [omega_cube, one_mul]
  have hW : localRecord q .wait = ![
      (Real.sqrt ((1 + 2 * q) / 3) : ℂ), Real.sqrt ((1 - q) / 3),
      Real.sqrt ((1 - q) / 3)] := by
    funext e
    fin_cases e <;> norm_num [localRecord, labelIndex]
  have hL : localRecord q .zero = ![
      (Real.sqrt ((1 + 2 * q) / 3) : ℂ), Real.sqrt ((1 - q) / 3) * omega,
      Real.sqrt ((1 - q) / 3) * omega ^ 2] := by
    funext e
    fin_cases e <;> norm_num [localRecord, labelIndex, omega_inv]
  have hR : localRecord q .one = ![
      (Real.sqrt ((1 + 2 * q) / 3) : ℂ), Real.sqrt ((1 - q) / 3) * omega ^ 2,
      Real.sqrt ((1 - q) / 3) * omega] := by
    funext e
    fin_cases e <;> norm_num [localRecord, labelIndex, omega_neg_two, omega_sq_inv]
  cases s <;> cases t <;>
    simp only [hW, hL, hR, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Finset.univ_eq_empty,
      Finset.sum_empty, add_zero, map_mul, map_pow, Complex.conj_ofReal, hw,
      omega_sq_sq, ↓reduceIte] <;>
    push_cast at ha hb ⊢
  all_goals
    generalize (Real.sqrt ((1 + 2 * q) / 3) : ℂ) = a at *
    generalize (Real.sqrt ((1 - q) / 3) : ℂ) = b at *
    ring_nf
    try simp only [omega_cube, hf, mul_one]
    first
    | linear_combination ha + 2 * hb
    | linear_combination ha - hb + b ^ 2 * omega_sum

private theorem gram_product (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v) (hq' : ∀ v, q v ≤ 1) (bus : Qutrit)
    (a b : Address n) :
    standardGram n q bus a b =
      ((∏ v, if loadedLabel n a bus v = loadedLabel n b bus v
        then 1 else q v : ℝ) : ℂ) := by
  classical
  change (∑ e, conj (record n q bus a e) * record n q bus b e) = _
  calc
    _ = ∑ e : Environment n, ∏ v,
        conj (localRecord (q v) (loadedLabel n a bus v) (e v)) *
          localRecord (q v) (loadedLabel n b bus v) (e v) := by
      simp only [record, map_prod, Finset.prod_mul_distrib]
    _ = ∏ v, ∑ i : Fin 3,
        conj (localRecord (q v) (loadedLabel n a bus v) i) *
          localRecord (q v) (loadedLabel n b bus v) i := (Fintype.prod_sum (fun (v : Router n) (i : Fin 3) =>
        conj (localRecord (q v) (loadedLabel n a bus v) i) *
          localRecord (q v) (loadedLabel n b bus v) i)).symm
    _ = _ := by
      simp only [local_overlap _ (hq _) (hq' _), Complex.ofReal_prod]

private theorem density_standard (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v) (hq' : ∀ v, q v ≤ 1) (bus : Qutrit) :
    densityGram n q bus = standardGram n q bus := by
  ext a b
  have he : densityGram n q bus a b = conj (standardGram n q bus a b) := by
    simp only [densityGram, standardGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
      recordMatrix, map_sum, map_mul, starRingEnd_apply, star_star]
  rw [he, gram_product n q hq hq' bus a b, Complex.conj_ofReal]

private theorem matrix_synthesis (n : ℕ) (q : Router n → ℝ) (bus : Qutrit) :
    (recordMatrix n q bus).mulVecLin = synthesis n q bus := by
  apply LinearMap.ext
  intro x
  funext e
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, recordMatrix, synthesis,
    LinearMap.coe_mk, AddHom.coe_mk, mul_comm]

/-- The complete signed coefficient certificate and its actual physical Gram consumer.
The Gram equality follows from real local overlaps, not from reality of record entries. -/
theorem signed_event (n : ℕ) (q : Router n → ℝ)
    (hq : ∀ v, -(1 / 2 : ℝ) ≤ q v) (hq' : ∀ v, q v ≤ 1) (bus : Qutrit) :
    Module.finrank ℂ (LinearMap.range (synthesis n q bus)) = (outputs n q).dimension ∧
    (outputs n q).kernel.length = 2 ^ n - (outputs n q).dimension ∧
    (vacuumRecord n q ∈ LinearMap.range (synthesis n q bus) ↔ (outputs n q).flag = true) ∧
    (∀ u, (outputs n q).representative = some u → synthesis n q bus u = vacuumRecord n q) ∧
    (∀ x, synthesis n q bus x = 0 ↔
      ∃! α : Fin (outputs n q).kernel.length → ℂ,
        x = ∑ i, α i • (outputs n q).kernel.get i) ∧
    (∀ a b, standardGram n q bus a b =
      ((∏ v, if loadedLabel n a bus v = loadedLabel n b bus v then 1 else q v : ℝ) : ℂ)) ∧
    densityGram n q bus = standardGram n q bus ∧
    LinearMap.ker (densityGram n q bus).mulVecLin = LinearMap.ker (synthesis n q bus) ∧
    (densityGram n q bus).rank = (outputs n q).dimension := by
  classical
  obtain ⟨h1, h2, h3, h4, h5⟩ := coefficient_certificate n q hq hq' bus
  refine ⟨h1, h2, h3, h4, h5, gram_product n q hq hq' bus,
    density_standard n q hq hq' bus, ?_, ?_⟩
  · rw [density_standard n q hq hq' bus, standardGram,
      Matrix.ker_mulVecLin_conjTranspose_mul_self, matrix_synthesis]
  · rw [density_standard n q hq hq' bus, standardGram,
      Matrix.rank_conjTranspose_mul_self]
    change Module.finrank ℂ (LinearMap.range (recordMatrix n q bus).mulVecLin) = _
    rw [matrix_synthesis]
    exact h1

end D5.S3.Quantum.Routing.HannSignedCertificate
