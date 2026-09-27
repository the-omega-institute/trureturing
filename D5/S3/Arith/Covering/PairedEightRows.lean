/- GID: D5/S3/Arith/Covering/PairedEightRows
   generality: G
   mirror-B: D5/B/S3/Arith/Covering/PairedEightRows
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Arith/Covering/PairedEightRows.claim; result=D5/S3/Arith/Covering/PairedEightRows.result; claim=D5/S3/Arith/Covering/PairedEightRows.claim
   digest: Shared phases force a horizontal deficit across paired eight-row fibers. -/

import D5.S3.Arith.Covering.BinaryCarryQuotient

set_option autoImplicit false

namespace D5.S3.Arith.Covering.PairedEightRows

/-- The last value denotes an inactive row. -/
abbrev Phase (n : ℕ) := Fin (n + 1)

def hit {n : ℕ} (p : Phase n) (r : ℕ) : Prop := p.val = r % n

instance {n : ℕ} (p : Phase n) (r : ℕ) : Decidable (hit p r) :=
  inferInstanceAs (Decidable (p.val = r % n))

def advance {n : ℕ} (hn : 0 < n) (d : ℕ) (p : Phase n) : Phase n :=
  if h : p.val < n then ⟨(p.val + d) % n, Nat.lt_trans (Nat.mod_lt _ hn) (by omega)⟩
  else p

structure Block where
  a : Phase 8
  b : Phase 8
  u : Phase 8
  v : Phase 8
  s : Phase 4
  f : Phase 4
  t : Phase 4
  h : Phase 4
  deriving DecidableEq

/-- The original transition table, including the both-inactive cases. -/
def Admissible (L R : Block) : Prop :=
  R.a = L.a ∧ R.b = advance (by decide) 1 L.b ∧
  R.s = advance (by decide) 1 L.s ∧ R.t = advance (by decide) 3 L.t ∧
  R.h = L.h ∧ (L.u = 8 ∨ R.u = 8) ∧ (L.v = 8 ∨ R.v = 8) ∧
  (L.f = 4 ∨ R.f = 4)

def covered (c : Block) (x y : ℕ) : Prop :=
  hit c.a y ∨ hit c.b (6*x+y) ∨ hit c.u (x+6*y) ∨ hit c.v (x+2*y) ∨
  hit c.s (2*x+y) ∨ hit c.f (3*x) ∨ hit c.t (2*x+y) ∨ hit c.h y

instance (c : Block) (x y : ℕ) : Decidable (covered c x y) := by
  unfold covered; infer_instance

/-- Every one of the sixteen binary lifts must be covered. -/
def full (c : Block) (i j : Fin 2) : Prop :=
  ∀ r s : Fin 4, covered c (i.val + 2*r.val) (j.val + 2*s.val)

instance (c : Block) (i j : Fin 2) : Decidable (full c i j) := by
  unfold full; infer_instance

/-- The complementary horizontal pair in the first four-point lift. -/
def A (c : Block) (x y : ℕ) : Prop :=
  (hit c.a y ∧ hit c.b (6*x+y+4)) ∨ (hit c.a (y+4) ∧ hit c.b (6*x+y))

/-- The complementary vertical pair in the first four-point lift. -/
def B (c : Block) (x y : ℕ) : Prop :=
  (hit c.u (x+6*y) ∧ hit c.v (x+2*y+4)) ∨
  (hit c.u (x+6*y+4) ∧ hit c.v (x+2*y))

def H (c : Block) (x y : ℕ) : Prop :=
  hit c.s (2*x+y) ∨ hit c.t (2*x+y) ∨ hit c.h y

def V (c : Block) (x : ℕ) : Prop := hit c.f (3*x)

def parent (c : Block) (x y : ℕ) : Prop := A c x y ∨ B c x y ∨ H c x y ∨ V c x

def J (c : Block) (i j : Fin 2) : Prop := ∀ q : Fin 2, H c i.val (j.val+2*q.val)

/-- The part of the full set not already supplied by horizontal pairs. -/
def W (c : Block) (i j : Fin 2) : Prop := full c i j ∧ ¬ J c i j

instance (c : Block) (x y : ℕ) : Decidable (A c x y) := by unfold A; infer_instance
instance (c : Block) (x y : ℕ) : Decidable (B c x y) := by unfold B; infer_instance
instance (c : Block) (x y : ℕ) : Decidable (H c x y) := by unfold H; infer_instance
instance (c : Block) (x : ℕ) : Decidable (V c x) := by unfold V; infer_instance
instance (c : Block) (x y : ℕ) : Decidable (parent c x y) := by unfold parent; infer_instance
instance (c : Block) (i j : Fin 2) : Decidable (J c i j) := by unfold J; infer_instance
instance (c : Block) (i j : Fin 2) : Decidable (W c i j) := by unfold W; infer_instance

/-- A resource is one of the two first-stage parents or the original vertical row. -/
def resource (c : Block) (k : Fin 3) (x y : ℕ) : Prop :=
  if k = 0 then A c x y else if k = 1 then B c x y else V c x

def owns (c : Block) (k : Fin 3) (i : Fin 2) : Prop :=
  ∃ x y : Fin 4, x.val % 2 = i.val ∧ resource c k x.val y.val

/-- Cardinality of the intersection with a fixed horizontal parity line. -/
def count (P : Fin 2 → Prop) [DecidablePred P] : ℕ :=
  (Finset.univ.filter P).card

/-- Completion by the same horizontal line, with both coordinates quantified. -/
def completed (c : Block) (h : Fin 2) : Prop := ∀ i j : Fin 2, full c i j ∨ j = h

/-- Horizontal carry and exclusive parents force a joint bound for fixed paired phases. -/
theorem paired_bound (L R : Block) (hp : Admissible L R) :
    (∀ i j i' j', W L i j → ¬ W R i' j') ∧
    (∀ c ∈ ({L, R} : Finset Block), ∀ i j i' j', W c i j → W c i' j' → i = i') ∧
    (∀ j, count (fun i => J L i j) + count (fun i => J R i j) ≤ 2) ∧
    (∀ j, count (fun i => full L i j) + count (fun i => full R i j) ≤ 3) ∧
    (∀ h, completed L h → ¬ completed R h) := by
  classical
  have first_descent (c : Block) (x y : Fin 4) :
      (∀ r s : Fin 2, covered c (x.val+4*r.val) (y.val+4*s.val)) ↔
      parent c x.val y.val := by
    have hb : ∀ (b : Phase 8) (x y : Fin 4) (r s : Fin 2),
        hit b (6*(x.val+4*r.val)+(y.val+4*s.val)) ↔ hit b (6*x.val+y.val+4*s.val) := by
      intros; unfold hit; omega
    have hu : ∀ (u : Phase 8) (x y : Fin 4) (r s : Fin 2),
        hit u ((x.val+4*r.val)+6*(y.val+4*s.val)) ↔ hit u (x.val+6*y.val+4*r.val) := by
      intros; unfold hit; omega
    have hv : ∀ (v : Phase 8) (x y : Fin 4) (r s : Fin 2),
        hit v ((x.val+4*r.val)+2*(y.val+4*s.val)) ↔ hit v (x.val+2*y.val+4*r.val) := by
      intros; unfold hit; omega
    have hs : ∀ (p : Phase 4) (x y : Fin 4) (r s : Fin 2),
        hit p (2*(x.val+4*r.val)+(y.val+4*s.val)) ↔ hit p (2*x.val+y.val) := by
      intros; unfold hit; omega
    have hf : ∀ (p : Phase 4) (x : Fin 4) (r : Fin 2),
        hit p (3*(x.val+4*r.val)) ↔ hit p (3*x.val) := by
      intros; unfold hit; omega
    have hh : ∀ (p : Phase 4) (y : Fin 4) (s : Fin 2),
        hit p (y.val+4*s.val) ↔ hit p y.val := by
      intros; unfold hit; omega
    simp only [covered, hb, hu, hv, hs, hf, hh, Fin.forall_fin_two]
    simp only [Fin.val_zero, Fin.val_one, mul_zero, add_zero, mul_one]
    have ab : ∀ (a b : Phase 8) (x y : Fin 4),
        ((hit a y.val ∨ hit b (6*x.val+y.val)) ∧
         (hit a (y.val+4) ∨ hit b (6*x.val+y.val+4))) ↔
        ((hit a y.val ∧ hit b (6*x.val+y.val+4)) ∨
         (hit a (y.val+4) ∧ hit b (6*x.val+y.val))) := by
      intros; unfold hit; omega
    have uv : ∀ (u v : Phase 8) (x y : Fin 4),
        ((hit u (x.val+6*y.val) ∨ hit v (x.val+2*y.val)) ∧
         (hit u (x.val+6*y.val+4) ∨ hit v (x.val+2*y.val+4))) ↔
        ((hit u (x.val+6*y.val) ∧ hit v (x.val+2*y.val+4)) ∨
         (hit u (x.val+6*y.val+4) ∧ hit v (x.val+2*y.val))) := by
      intros; unfold hit; omega
    have hab := ab c.a c.b x y
    have huv := uv c.u c.v x y
    clear hb hu hv hs hf hh ab uv
    unfold parent A B H V
    rw [← hab, ← huv]
    have logic (a₀ a₁ b₀ b₁ l : Prop) :
        (((a₀ ∨ b₀ ∨ l) ∧ (a₁ ∨ b₀ ∨ l)) ∧
         ((a₀ ∨ b₁ ∨ l) ∧ (a₁ ∨ b₁ ∨ l))) ↔
        (a₀ ∧ a₁) ∨ (b₀ ∧ b₁) ∨ l := by
      clear c x y hab huv
      have pg := BinaryCarryQuotient.plane_cover_iff
        (fun r : Fin 4 => ![a₀,a₁,b₀,b₁] r)
        ![0,0,1,1] ![1,1,0,0] ![0,1,0,1]
        (by intro r _; fin_cases r <;> decide)
      simp [Fin.forall_fin_two, Fin.exists_fin_succ] at pg
      by_cases hl : l
      · simp [hl]
      · simp only [hl, or_false]
        simpa only [and_comm, and_left_comm, and_assoc, or_comm, or_left_comm, or_assoc,
          or_self, or_self_left] using pg
    simpa only [or_assoc, or_left_comm, or_comm] using
      logic (hit c.a y.val ∨ hit c.b (6*x.val+y.val))
        (hit c.a (y.val+4) ∨ hit c.b (6*x.val+y.val+4))
        (hit c.u (x.val+6*y.val) ∨ hit c.v (x.val+2*y.val))
        (hit c.u (x.val+6*y.val+4) ∨ hit c.v (x.val+2*y.val+4))
        (hit c.s (2*x.val+y.val) ∨ hit c.f (3*x.val) ∨ hit c.t (2*x.val+y.val) ∨ hit c.h y.val)
  have local_geometry (c : Block) :
      (∀ i j, full c i j ↔ J c i j ∨ W c i j) ∧
      (∀ i j, W c i j → ∃ k l : Fin 3, k ≠ l ∧ owns c k i ∧ owns c l i) := by
    classical
    have descent (i j : Fin 2) : full c i j ↔
        ∀ p q : Fin 2, parent c (i.val+2*p.val) (j.val+2*q.val) := by
      constructor
      · intro h p q
        apply (first_descent c ⟨i.val+2*p.val, by omega⟩ ⟨j.val+2*q.val, by omega⟩).mp
        intro r s
        have hh := h ⟨p.val+2*r.val, by omega⟩ ⟨q.val+2*s.val, by omega⟩
        convert hh using 1 <;> dsimp <;> omega
      · intro h r s
        have hh := (first_descent c
          ⟨i.val+2*(r.val%2), by omega⟩ ⟨j.val+2*(s.val%2), by omega⟩).mpr
          (h ⟨r.val%2, by omega⟩ ⟨s.val%2, by omega⟩)
          ⟨r.val/2, by omega⟩ ⟨s.val/2, by omega⟩
        convert hh using 1 <;> dsimp <;> omega
    have horizontal (i j p q : Fin 2) :
        H c (i.val+2*p.val) (j.val+2*q.val) ↔ H c i.val (j.val+2*q.val) := by
      unfold H hit; omega
    constructor
    · intro i j
      constructor
      · intro h; by_cases hj : J c i j
        · exact Or.inl hj
        · exact Or.inr ⟨h, hj⟩
      · rintro (hj | hw)
        · exact (descent i j).mpr (fun p q =>
          Or.inr (Or.inr (Or.inl ((horizontal i j p q).mpr (hj q)))))
        · exact hw.1
    · intro i j hw
      obtain ⟨q, hq⟩ := not_forall.mp hw.2
      have h₀ := (descent i j).mp hw.1 0 q
      have h₁ := (descent i j).mp hw.1 1 q
      simp only [Fin.val_zero, Fin.val_one, mul_zero, add_zero, mul_one] at h₀ h₁
      have hq' : ¬ H c (i.val+2) (j.val+2*q.val) := by
        simpa using (not_congr (horizontal i j 1 q)).mpr hq
      have distinct (k : Fin 3) :
          ¬ (resource c k i.val (j.val+2*q.val) ∧
             resource c k (i.val+2) (j.val+2*q.val)) := by
        fin_cases k <;> simp [resource, A, B, V, hit] <;> omega
      have own₀ (k : Fin 3) (hk : resource c k i.val (j.val+2*q.val)) : owns c k i :=
        ⟨⟨i.val, by omega⟩, ⟨j.val+2*q.val, by omega⟩, by dsimp; omega, hk⟩
      have own₁ (k : Fin 3) (hk : resource c k (i.val+2) (j.val+2*q.val)) : owns c k i :=
        ⟨⟨i.val+2, by omega⟩, ⟨j.val+2*q.val, by omega⟩, by dsimp; omega, hk⟩
      have r₀ : ∃ k : Fin 3, resource c k i.val (j.val+2*q.val) := by
        rcases h₀ with ha | hb | hh | hv
        · exact ⟨0, ha⟩
        · exact ⟨1, hb⟩
        · exact False.elim (hq hh)
        · exact ⟨2, hv⟩
      have r₁ : ∃ k : Fin 3, resource c k (i.val+2) (j.val+2*q.val) := by
        rcases h₁ with ha | hb | hh | hv
        · exact ⟨0, ha⟩
        · exact ⟨1, hb⟩
        · exact False.elim (hq' hh)
        · exact ⟨2, hv⟩
      obtain ⟨k, hk⟩ := r₀
      obtain ⟨l, hl⟩ := r₁
      exact ⟨k, l, by rintro rfl; exact distinct k ⟨hk, hl⟩, own₀ k hk, own₁ l hl⟩
  have unique (c : Block) (k : Fin 3) (i i' : Fin 2)
      (hi : owns c k i) (hi' : owns c k i') : i = i' := by
    obtain ⟨x, y, hxi, hx⟩ := hi
    obtain ⟨x', y', hxi', hx'⟩ := hi'
    apply Fin.ext
    fin_cases k <;> simp [resource, A, B, V, hit] at hx hx' <;> omega
  have exclusive (k : Fin 3) (i i' : Fin 2)
      (hi : owns L k i) (hi' : owns R k i') : False := by
    obtain ⟨x, y, _, hx⟩ := hi
    obtain ⟨x', y', _, hx'⟩ := hi'
    obtain ⟨ha, hb, hs, ht, hh, hu, hv, hf⟩ := hp
    fin_cases k
    · change A L x.val y.val at hx
      change A R x'.val y'.val at hx'
      have par (c : Block) (x y : ℕ) (h : A c x y) :
          c.a.val % 2 = c.b.val % 2 ∧ c.b.val < 8 := by
        dsimp [A, hit] at h
        omega
      have h₀ := par L x.val y.val hx
      have h₁ := par R x'.val y'.val hx'
      rw [ha, hb] at h₁
      dsimp [advance] at h₁
      split_ifs at h₁ <;> (try dsimp at h₁) <;> omega
    · simp [resource, B, hit] at hx hx'
      rcases hu with hu | hu
      · have hval : L.u.val = 8 := congrArg Fin.val hu
        omega
      · have hval : R.u.val = 8 := congrArg Fin.val hu
        omega
    · simp [resource, V, hit] at hx hx'
      rcases hf with hf | hf
      · have hval : L.f.val = 4 := congrArg Fin.val hf
        omega
      · have hval : R.f.val = 4 := congrArg Fin.val hf
        omega
  have overlap (k l m n : Fin 3) (hkl : k ≠ l) (hmn : m ≠ n) :
      k = m ∨ k = n ∨ l = m ∨ l = n := by omega
  have wunique (c : Block) (i j i' j' : Fin 2)
      (h : W c i j) (h' : W c i' j') : i = i' := by
    obtain ⟨k, l, hkl, hk, hl⟩ := (local_geometry c).2 i j h
    obtain ⟨m, n, hmn, hm, hn⟩ := (local_geometry c).2 i' j' h'
    rcases overlap k l m n hkl hmn with e | e | e | e
    · exact unique c k i i' hk (e.symm ▸ hm)
    · exact unique c k i i' hk (e.symm ▸ hn)
    · exact unique c l i i' hl (e.symm ▸ hm)
    · exact unique c l i i' hl (e.symm ▸ hn)
  have wexclusive (i j i' j' : Fin 2) (h : W L i j) (h' : W R i' j') : False := by
    obtain ⟨k, l, hkl, hk, hl⟩ := (local_geometry L).2 i j h
    obtain ⟨m, n, hmn, hm, hn⟩ := (local_geometry R).2 i' j' h'
    rcases overlap k l m n hkl hmn with e | e | e | e
    · exact exclusive k i i' hk (e.symm ▸ hm)
    · exact exclusive k i i' hk (e.symm ▸ hn)
    · exact exclusive l i i' hl (e.symm ▸ hm)
    · exact exclusive l i i' hl (e.symm ▸ hn)
  have count_eq (P : Fin 2 → Prop) [DecidablePred P] :
      count P = (if P 0 then 1 else 0) + (if P 1 then 1 else 0) := by
    simp only [count, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_two]
  have jbound (j : Fin 2) : count (fun i => J L i j) + count (fun i => J R i j) ≤ 2 := by
    have small : ∀ (s t h : Phase 4) (j : Fin 2),
        let left : Block := ⟨8,8,8,8,s,4,t,h⟩
        let right : Block := ⟨8,8,8,8,advance (by decide) 1 s,4,advance (by decide) 3 t,h⟩
        count (fun i => J left i j) + count (fun i => J right i j) ≤ 2 := by
      decide +kernel
    obtain ⟨_, _, hs, ht, hh, _⟩ := hp
    have he := small L.s L.t L.h j
    simp only [count, Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_two] at he ⊢
    convert he using 1; simp [J, H, hs, ht, hh]
  have fbound (j : Fin 2) :
      count (fun i => full L i j) + count (fun i => full R i j) ≤ 3 := by
    have hJ := jbound j
    have wl := wunique L 0 j 1 j
    have wr := wunique R 0 j 1 j
    have e00 := wexclusive 0 j 0 j
    have e01 := wexclusive 0 j 1 j
    have e10 := wexclusive 1 j 0 j
    have e11 := wexclusive 1 j 1 j
    have wsum : (if W L 0 j then 1 else 0) + (if W L 1 j then 1 else 0) +
        (if W R 0 j then 1 else 0) + (if W R 1 j then 1 else 0) ≤ 1 := by
      clear unique exclusive overlap wunique wexclusive jbound count_eq hJ hp
        first_descent local_geometry
      by_cases a : W L 0 j <;> by_cases b : W L 1 j <;>
        by_cases c : W R 0 j <;> by_cases d : W R 1 j <;>
        simp_all
    have point (c : Block) (i : Fin 2) :
        (if full c i j then 1 else 0) ≤
        (if J c i j then 1 else 0) + (if W c i j then 1 else 0) := by
      have hg := (local_geometry c).1 i j
      by_cases a : J c i j <;> by_cases b : W c i j <;>
        simp only [a, b, or_self, or_true, or_false] at hg <;>
        simp only [hg, a, b, ↓reduceIte] <;> omega
    have p₀ := point L 0
    have p₁ := point L 1
    have p₂ := point R 0
    have p₃ := point R 1
    simp only [count_eq] at hJ ⊢
    omega
  refine ⟨wexclusive, fun c _ => wunique c, jbound, fbound, ?_⟩
  intro h hL hR
  let j : Fin 2 := 1-h
  have hj : j ≠ h := by dsimp [j]; fin_cases h <;> decide
  have allL (i : Fin 2) : full L i j := (hL i j).resolve_right hj
  have allR (i : Fin 2) : full R i j := (hR i j).resolve_right hj
  have hb := fbound j
  simp [count_eq, allL, allR] at hb

def Q : ℤ := 16865820972000

def original (c : Fin 8 → ℤ) : Fin 8 → BinaryCarryQuotient.Row :=
  ![⟨256, 48, 1, c 0⟩, ⟨3328, 1134, 1, c 1⟩,
    ⟨3840, 2273, 3534, c 2⟩, ⟨3840, 2257, 3762, c 3⟩,
    ⟨640, 470, 1, c 4⟩, ⟨384, 139, 232, c 5⟩,
    ⟨1408, 58, 1, c 6⟩, ⟨4480, 3112, 1, c 7⟩]

/-- Euclidean representatives make the definition valid for every integer phase. -/
def residual (g m inv : ℕ) (hm : 0 < m) (d : ℤ) : Phase m :=
  let r := (d % (g*m : ℕ)).toNat
  if r % g = 0 then ⟨(inv*(r/g)) % m, by have := Nat.mod_lt (inv*(r/g)) hm; omega⟩
  else ⟨m, by omega⟩

def blockAt (c : Fin 8 → ℤ) (k l : ℤ) : Block where
  a := residual 32 8 7 (by decide) (c 0-48*k-l)
  b := residual 416 8 3 (by decide) (c 1-1134*k-l)
  u := residual 480 8 1 (by decide) (c 2-2273*k-3534*l)
  v := residual 480 8 1 (by decide) (c 3-2257*k-3762*l)
  s := residual 160 4 3 (by decide) (c 4-470*k-l)
  f := residual 96 4 1 (by decide) (c 5-139*k-232*l)
  t := residual 352 4 1 (by decide) (c 6-58*k-l)
  h := residual 1120 4 1 (by decide) (c 7-3112*k-l)

def localRow (c : Block) (r : Fin 8) (x y : ℕ) : Prop :=
  ![hit c.a y, hit c.b (6*x+y), hit c.u (x+6*y), hit c.v (x+2*y),
    hit c.s (2*x+y), hit c.f (3*x), hit c.t (2*x+y), hit c.h y] r

def originalCovered (c : Fin 8 → ℤ) (k l : ℤ) : Prop :=
  ∃ r : Fin 8, (original c r).covers k l

def originalFull (c : Fin 8 → ℤ) (k l : ℤ) (i j : Fin 2) : Prop :=
  ∀ u v : Fin 4, originalCovered c (k+Q*(i.val+2*u.val)) (l+Q*(j.val+2*v.val))

def originalCompleted (c : Fin 8 → ℤ) (k l : ℤ) (h : Fin 2) : Prop :=
  ∀ i j : Fin 2, originalFull c k l i j ∨ j = h

instance (c : Fin 8 → ℤ) (k l : ℤ) : Decidable (originalCovered c k l) := by
  unfold originalCovered BinaryCarryQuotient.Row.covers; infer_instance
instance (c : Fin 8 → ℤ) (k l : ℤ) (i j : Fin 2) : Decidable (originalFull c k l i j) := by
  unfold originalFull; infer_instance
instance (c : Fin 8 → ℤ) (k l : ℤ) (h : Fin 2) : Decidable (originalCompleted c k l h) := by
  unfold originalCompleted; infer_instance

/-- Literal original coverage inherits the paired bound at every integer basepoint. -/
theorem original_bound (c : Fin 8 → ℤ) (k l : ℤ) :
    (∀ i j, originalFull c k l i j ↔ full (blockAt c k l) i j) ∧
    (∀ j, count (fun i => originalFull c k l i j) +
      count (fun i => originalFull c (k+Q/2) l i j) ≤ 3) ∧
    (∀ h, originalCompleted c k l h → ¬ originalCompleted c (k+Q/2) l h) := by
  have original_row_bridge (c : Fin 8 → ℤ) (k l : ℤ) (r : Fin 8) (x y : ℕ) :
      (original c r).covers (k+Q*x) (l+Q*y) ↔ localRow (blockAt c k l) r x y := by
    unfold BinaryCarryQuotient.Row.covers
    rw [show (original c r).a * (k+Q*x) + (original c r).b * (l+Q*y) -
        (original c r).c = Q*(original c r).a*x + Q*(original c r).b*y -
        ((original c r).c-(original c r).a*k-(original c r).b*l) by ring]
    have norm (e a b a' b' x y d : ℤ) (ha : a ≡ a' [ZMOD e])
        (hb : b ≡ b' [ZMOD e]) :
        (e ∣ a*x+b*y-d) ↔ (e ∣ a'*x+b'*y-d) :=
      (((ha.mul_right x).add (hb.mul_right y)).sub_right d).dvd_iff
    fin_cases r
    · dsimp [original, localRow, blockAt]
      try simp only [one_mul]
      generalize hd : c 0 - 48*k - l = d
      rw [norm 256 (Q*48) (Q*1) 0 224 x y d (by decide +kernel) (by decide +kernel)]
      simp only [hit, residual, Int.dvd_iff_emod_eq_zero]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.reduceMul]
      split_ifs <;> (try dsimp) <;> omega
    · dsimp [original, localRow, blockAt]
      try simp only [one_mul]
      generalize hd : c 1 - 1134*k - l = d
      rw [norm 3328 (Q*1134) (Q*1) 832 1248 x y d (by decide +kernel) (by decide +kernel)]
      simp only [hit, residual, Int.dvd_iff_emod_eq_zero]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.reduceMul]
      split_ifs <;> (try dsimp) <;> omega
    · dsimp [original, localRow, blockAt]
      try simp only [one_mul]
      generalize hd : c 2 - 2273*k - 3534*l = d
      rw [norm 3840 (Q*2273) (Q*3534) 480 2880 x y d (by decide +kernel) (by decide +kernel)]
      simp only [hit, residual, Int.dvd_iff_emod_eq_zero]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.reduceMul]
      split_ifs <;> (try dsimp) <;> omega
    · dsimp [original, localRow, blockAt]
      try simp only [one_mul]
      generalize hd : c 3 - 2257*k - 3762*l = d
      rw [norm 3840 (Q*2257) (Q*3762) 480 960 x y d (by decide +kernel) (by decide +kernel)]
      simp only [hit, residual, Int.dvd_iff_emod_eq_zero]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.reduceMul]
      split_ifs <;> (try dsimp) <;> omega
    · dsimp [original, localRow, blockAt]
      try simp only [one_mul]
      generalize hd : c 4 - 470*k - l = d
      rw [norm 640 (Q*470) (Q*1) 320 480 x y d (by decide +kernel) (by decide +kernel)]
      simp only [hit, residual, Int.dvd_iff_emod_eq_zero]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.reduceMul]
      split_ifs <;> (try dsimp) <;> omega
    · dsimp [original, localRow, blockAt]
      try simp only [one_mul]
      generalize hd : c 5 - 139*k - 232*l = d
      rw [norm 384 (Q*139) (Q*232) 288 0 x y d (by decide +kernel) (by decide +kernel)]
      simp only [hit, residual, Int.dvd_iff_emod_eq_zero]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.reduceMul]
      split_ifs <;> (try dsimp) <;> omega
    · dsimp [original, localRow, blockAt]
      try simp only [one_mul]
      generalize hd : c 6 - 58*k - l = d
      rw [norm 1408 (Q*58) (Q*1) 704 352 x y d (by decide +kernel) (by decide +kernel)]
      simp only [hit, residual, Int.dvd_iff_emod_eq_zero]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.reduceMul]
      split_ifs <;> (try dsimp) <;> omega
    · dsimp [original, localRow, blockAt]
      try simp only [one_mul]
      generalize hd : c 7 - 3112*k - l = d
      rw [norm 4480 (Q*3112) (Q*1) 0 1120 x y d (by decide +kernel) (by decide +kernel)]
      simp only [hit, residual, Int.dvd_iff_emod_eq_zero]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.reduceMul]
      split_ifs <;> (try dsimp) <;> omega
  have original_transition (c : Fin 8 → ℤ) (k l : ℤ) :
      Admissible (blockAt c k l) (blockAt c (k+Q/2) l) := by
    unfold Admissible
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      simp only [Fin.ext_iff]
      dsimp [blockAt, residual, advance, Q]
      split_ifs <;> (try dsimp at *) <;> omega
  have eqv (k l : ℤ) (i j : Fin 2) :
      originalFull c k l i j ↔ full (blockAt c k l) i j := by
    unfold originalFull full
    apply forall_congr'; intro u
    apply forall_congr'; intro v
    have hh := exists_congr (fun r : Fin 8 =>
      original_row_bridge c k l r (i.val+2*u.val) (j.val+2*v.val))
    simpa [originalCovered, localRow, covered, Fin.exists_fin_succ,
      Nat.cast_add, Nat.cast_mul] using hh
  have hb := paired_bound (blockAt c k l) (blockAt c (k+Q/2) l) (original_transition c k l)
  refine ⟨eqv k l, ?_, ?_⟩
  · intro j
    have hcount (k l : ℤ) : count (fun i => originalFull c k l i j) =
        count (fun i => full (blockAt c k l) i j) := by
      unfold count
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, eqv]
    rw [hcount, hcount]
    exact hb.2.2.2.1 j
  · intro h h₀ h₁
    apply hb.2.2.2.2 h
    · intro i j; exact (h₀ i j).imp ((eqv k l i j).mp) id
    · intro i j; exact (h₁ i j).imp ((eqv (k+Q/2) l i j).mp) id

/-- Separate successful original-phase repairs could be assembled with one shared vector. -/
def claim : Prop :=
  ((∃ c : Fin 8 → ℤ, originalCompleted c 0 0 1) ∧
   (∃ c : Fin 8 → ℤ, originalCompleted c (Q/2) 0 1)) →
  ∃ c : Fin 8 → ℤ, originalCompleted c 0 0 1 ∧ originalCompleted c (Q/2) 0 1

/-- Exact original-phase repairs succeed separately and fail jointly. -/
theorem result : ¬ claim := by
  let c₀ : Fin 8 → ℤ := ![0,0,0,0,0,0,704,0]
  let c₁ : Fin 8 → ℤ := ![0,0,0,0,160,0,1056,0]
  have mask₀ : ∀ i j : Fin 2, originalFull c₀ 0 0 i j ↔ i = 0 ∨ j = 0 := by
    decide +kernel
  have mask₁ : ∀ i j : Fin 2, originalFull c₁ (Q/2) 0 i j ↔ j = 0 := by
    decide +kernel
  have h₀ : originalCompleted c₀ 0 0 1 := by
    intro i j
    fin_cases j
    · exact Or.inl ((mask₀ i 0).mpr (Or.inr rfl))
    · exact Or.inr rfl
  have h₁ : originalCompleted c₁ (Q/2) 0 1 := by
    intro i j
    fin_cases j
    · exact Or.inl ((mask₁ i 0).mpr rfl)
    · exact Or.inr rfl
  intro h
  obtain ⟨c, hc₀, hc₁⟩ := h ⟨⟨c₀, h₀⟩, ⟨c₁, h₁⟩⟩
  exact (original_bound c 0 0).2.2 1 hc₀ (by simpa only [zero_add] using hc₁)

end D5.S3.Arith.Covering.PairedEightRows
