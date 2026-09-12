/- GID: D5/S1/Words/Mechanical/MechanicalHistoryCapacity
   generality: G
   mirror-B: D5/B/S1/Words/Mechanical/MechanicalHistoryCapacity
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: []
   digest: Realized mechanical histories have sharp finite encoding capacity but admit
     no finite autonomous exact state model, for every irrational slope. -/

import D5.S1.Words.Mechanical.MechanicalFactorComplexity
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

namespace D5.S1.Words.Mechanical.HistoryCapacity

/-- A window at one common natural starting point. -/
noncomputable def read (alpha rho : Real) (n i : Nat) : Fin n → Bool :=
  fun k => lowerMechanicalWord alpha rho (i + k.val)

/-- All actual words, not a finite sample of occurrence indices. -/
noncomputable def histories (alpha rho : Real) (n : Nat) : Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter (fun w => ∃ i : Nat, w = read alpha rho n i)

abbrev History (alpha rho : Real) (n : Nat) := ↥(histories alpha rho n)

@[simp] theorem mem_histories {alpha rho : Real} {n : Nat} {w : Fin n → Bool} :
    w ∈ histories alpha rho n ↔ ∃ i : Nat, w = read alpha rho n i := by
  classical
  simp [histories]

/-- The new finite-function presentation is exactly the existing list-valued owner. -/
theorem image_ofFn (alpha rho : Real) (n : Nat) :
    (histories alpha rho n).image List.ofFn = lowerMechanicalFactorSet alpha rho n := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨i, rfl⟩ := mem_histories.mp hf
    exact mem_lowerMechanicalFactorSet.mpr ⟨i, rfl⟩
  · intro hw
    obtain ⟨i, rfl⟩ := mem_lowerMechanicalFactorSet.mp hw
    exact Finset.mem_image.mpr
      ⟨read alpha rho n i, mem_histories.mpr ⟨i, rfl⟩, rfl⟩

/-- Reuse the all-irrational theorem through a proved word-preserving presentation. -/
theorem histories_card {alpha rho : Real}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1) (ha : Irrational alpha) (n : Nat) :
    (histories alpha rho n).card = n + 1 := by
  classical
  have hi : Function.Injective (List.ofFn : (Fin n → Bool) → List Bool) :=
    fun _ _ h => List.ofFn_inj.mp h
  calc
    (histories alpha rho n).card = ((histories alpha rho n).image List.ofFn).card :=
      (Finset.card_image_of_injective _ hi).symm
    _ = (lowerMechanicalFactorSet alpha rho n).card := by rw [image_ofFn]
    _ = n + 1 := lower_mechanical_factor_complexity ha0 ha1 ha n

theorem card_history {alpha rho : Real}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1) (ha : Irrational alpha) (n : Nat) :
    Fintype.card (History alpha rho n) = n + 1 := by
  simpa using histories_card (rho := rho) ha0 ha1 ha n

/-- Truncation retains a shared underlying start, not merely pairwise compatible edges. -/
def truncate (n h : Nat) (w : Fin (n + h) → Bool) : Fin n → Bool :=
  fun k => w ⟨k.val, by have := k.isLt; omega⟩

noncomputable def prefix (alpha rho : Real) (n h : Nat) :
    History alpha rho (n + h) → History alpha rho n := fun w =>
  ⟨truncate n h w.val, by
    obtain ⟨i, hi⟩ := mem_histories.mp w.property
    apply mem_histories.mpr
    refine ⟨i, ?_⟩
    rw [hi]
    rfl⟩

theorem prefix_surjective (alpha rho : Real) (n h : Nat) :
    Function.Surjective (prefix alpha rho n h) := by
  intro w
  obtain ⟨i, hi⟩ := mem_histories.mp w.property
  refine ⟨⟨read alpha rho (n + h) i, mem_histories.mpr ⟨i, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  exact hi.symm

/-- At every finite depth, an actual longer history is still unresolved. -/
theorem prefix_not_injective {alpha rho : Real}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1) (ha : Irrational alpha)
    (n h : Nat) (hh : 0 < h) : ¬ Function.Injective (prefix alpha rho n h) := by
  intro hi
  have hc := Fintype.card_le_of_injective (prefix alpha rho n h) hi
  rw [card_history ha0 ha1 ha, card_history ha0 ha1 ha] at hc
  omega

/-- The unresolved words have genuine natural starts with a common observed prefix. -/
theorem actual_future_collision {alpha rho : Real}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1) (ha : Irrational alpha)
    (n h : Nat) (hh : 0 < h) :
    ∃ i j : Nat, read alpha rho n i = read alpha rho n j ∧
      read alpha rho (n + h) i ≠ read alpha rho (n + h) j := by
  have hn := prefix_not_injective (rho := rho) ha0 ha1 ha n h hh
  unfold Function.Injective at hn
  push_neg at hn
  obtain ⟨u, v, hp, huv⟩ := hn
  obtain ⟨i, hi⟩ := mem_histories.mp u.property
  obtain ⟨j, hj⟩ := mem_histories.mp v.property
  have he := congrArg Subtype.val hp
  change truncate n h u.val = truncate n h v.val at he
  rw [hi, hj] at he
  refine ⟨i, j, he, ?_⟩
  intro hij
  apply huv
  apply Subtype.ext
  exact hi.trans (hij.trans hj.symm)

/-- A finite static encoding has no transition-compatibility requirement. -/
def BitEncoding (X : Type) (b : Nat) : Prop :=
  ∃ encode : X → (Fin b → Bool), Function.Injective encode

private theorem finite_injection_iff (X Y : Type) [Fintype X] [Fintype Y] :
    (∃ f : X → Y, Function.Injective f) ↔ Fintype.card X ≤ Fintype.card Y := by
  classical
  constructor
  · rintro ⟨f, hf⟩
    exact Fintype.card_le_of_injective f hf
  · intro h
    let f : Fin (Fintype.card X) → Fin (Fintype.card Y) :=
      fun i => ⟨i.val, lt_of_lt_of_le i.isLt h⟩
    have hf : Function.Injective f := by
      intro a b hab
      exact Fin.ext (congrArg Fin.val hab)
    refine ⟨fun x => (Fintype.equivFin Y).symm (f ((Fintype.equivFin X) x)), ?_⟩
    exact (Fintype.equivFin Y).symm.injective.comp
      (hf.comp (Fintype.equivFin X).injective)

/-- Necessary and sufficient capacity, including empty carriers and zero bits. -/
theorem bit_encoding_iff (X : Type) [Fintype X] (b : Nat) :
    BitEncoding X b ↔ Fintype.card X ≤ 2 ^ b := by
  classical
  unfold BitEncoding
  simpa using finite_injection_iff X (Fin b → Bool)

/-- The arbitrary-length history law, with no restriction to Fibonacci indices. -/
theorem history_bit_encoding_iff {alpha rho : Real}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1) (ha : Irrational alpha) (n b : Nat) :
    BitEncoding (History alpha rho n) b ↔ n + 1 ≤ 2 ^ b := by
  rw [bit_encoding_iff, card_history ha0 ha1 ha]

/-- The capacity vector underlying the separate 5040 divisor-box example. -/
abbrev Capacity5040 := Fin 5 × Fin 3 × Fin 2 × Fin 2

theorem capacity5040_card : Fintype.card Capacity5040 = 60 := by
  norm_num [Capacity5040]

/-- Six is the least width; it is not a period or a Zeckendorf window depth. -/
theorem capacity5040_min_bits (b : Nat) : BitEncoding Capacity5040 b ↔ 6 ≤ b := by
  rw [bit_encoding_iff, capacity5040_card]
  constructor
  · intro he
    by_contra hn
    have hb : b ≤ 5 := by omega
    have hp : (2 : Nat) ^ b ≤ 2 ^ 5 := by gcongr
    norm_num at hp
    omega
  · intro hb
    have hp : (2 : Nat) ^ 6 ≤ 2 ^ b := by gcongr
    norm_num at hp
    omega

/-- Every injective six-bit encoding leaves exactly four unused words. -/
theorem capacity5040_unused (encode : Capacity5040 → (Fin 6 → Bool))
    (he : Function.Injective encode) :
    (Finset.univ \ Finset.univ.image encode).card = 4 := by
  classical
  rw [Finset.card_sdiff (Finset.subset_univ _),
    Finset.card_image_of_injective _ he]
  norm_num [Capacity5040]

/-- Sixty and sixty-four both arise on the general history-capacity curve. -/
theorem six_bit_history_cutoff {alpha rho : Real}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1) (ha : Irrational alpha) :
    Fintype.card (History alpha rho 59) = 60 ∧
      Fintype.card (History alpha rho 63) = 64 ∧
      BitEncoding (History alpha rho 63) 6 ∧
      ¬ BitEncoding (History alpha rho 64) 6 := by
  rw [card_history ha0 ha1 ha, card_history ha0 ha1 ha,
    history_bit_encoding_iff ha0 ha1 ha, history_bit_encoding_iff ha0 ha1 ha]
  norm_num

/-- A finite autonomous evolution, with no external clock or input hidden in its update. -/
def evolve {C : Type} (step : C → C) : Nat → C → C
  | 0, c => c
  | t + 1, c => step (evolve step t c)

private theorem state_at_add {C : Type} (step : C → C) (q : Nat → C)
    (hq : ∀ i : Nat, q (i + 1) = step (q i)) (i t : Nat) :
    q (i + t) = evolve step t (q i) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Nat.add_succ, hq, ih]
    rfl

/-- Every exact finite autonomous model would have to encode each whole history object. -/
theorem model_capacity_bound {alpha rho : Real}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1) (ha : Irrational alpha)
    {C : Type} [Fintype C] (step : C → C) (out : C → Bool) (q : Nat → C)
    (hq : ∀ i : Nat, q (i + 1) = step (q i))
    (hout : ∀ i : Nat, out (q i) = lowerMechanicalWord alpha rho i) (n : Nat) :
    n + 1 ≤ Fintype.card C := by
  classical
  let start (w : History alpha rho n) : Nat :=
    Classical.choose (mem_histories.mp w.property)
  have hstart (w : History alpha rho n) : w.val = read alpha rho n (start w) :=
    Classical.choose_spec (mem_histories.mp w.property)
  let encode : History alpha rho n → C := fun w => q (start w)
  have he : Function.Injective encode := by
    intro u v huv
    apply Subtype.ext
    rw [hstart u, hstart v]
    funext k
    change lowerMechanicalWord alpha rho (start u + k.val) =
      lowerMechanicalWord alpha rho (start v + k.val)
    rw [← hout, ← hout, state_at_add step q hq, state_at_add step q hq]
    exact congrArg (fun c => out (evolve step k.val c)) huv
  have hc := Fintype.card_le_of_injective encode he
  rwa [card_history ha0 ha1 ha] at hc

/-- No finite autonomous exact model at any capacity, including 60 and 64.
This is not a claim about input-driven automata or general computability. -/
theorem no_finite_autonomous_model {alpha rho : Real}
    (ha0 : 0 ≤ alpha) (ha1 : alpha < 1) (ha : Irrational alpha)
    {C : Type} [Fintype C] (step : C → C) (out : C → Bool) (q : Nat → C)
    (hq : ∀ i : Nat, q (i + 1) = step (q i))
    (hout : ∀ i : Nat, out (q i) = lowerMechanicalWord alpha rho i) : False := by
  have hc := model_capacity_bound ha0 ha1 ha step out q hq hout (Fintype.card C)
  omega

#print axioms actual_future_collision
#print axioms history_bit_encoding_iff
#print axioms capacity5040_unused
#print axioms no_finite_autonomous_model

end D5.S1.Words.Mechanical.HistoryCapacity
