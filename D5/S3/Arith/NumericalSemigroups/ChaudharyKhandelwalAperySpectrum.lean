/- GID: D5/S3/Arith/NumericalSemigroups/ChaudharyKhandelwalAperySpectrum
   generality: G
   mirror-B: D5/B/S3/Arith/NumericalSemigroups/ChaudharyKhandelwalAperySpectrum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The Apéry spectrum at modulus kb for the family {0,a,b,kb}. -/
import Mathlib


/-!
# Apéry spectra for four-element sets of the form {0, a, b, kb}

The source spectrum uses Apéry minima and interval counts as in Chaudhary–Khandelwal,
arXiv:2611.33046v1, §§3.1–3.2. The computation at modulus kb answers the named
family in §8(2).
-/

namespace CKApery

structure Params where
  a : ℕ
  b : ℕ
  k : ℕ
  a_pos : 0 < a
  a_lt_b : a < b
  coprime : Nat.Coprime a b
  k_ge : 3 ≤ k

namespace Params

variable (P : Params)

def d : ℕ := P.k * P.b

private theorem b_pos : 0 < P.b := P.a_pos.trans P.a_lt_b

private theorem b_le_d : P.b ≤ P.d := by
  unfold d
  have hk : 1 ≤ P.k := by have := P.k_ge; omega
  simpa using Nat.mul_le_mul_right P.b hk

private theorem d_pos : 0 < P.d := P.b_pos.trans_le P.b_le_d

abbrev Rect := Fin P.b × Fin P.k

def L (x y : ℕ) : ℕ := P.a * x + P.b * y

def W (x y : ℕ) : ℕ := (P.d - P.a) * x + (P.d - P.b) * y

private theorem L_add_W (x y : ℕ) : P.L x y + P.W x y = P.d * (x + y) := by
  have ha := (P.a_lt_b.le).trans P.b_le_d
  have hb := P.b_le_d
  unfold L W
  zify [ha, hb]
  ring

/-- The two natural carries for a nonnegative coefficient pair. -/
private theorem two_carries (p z : ℕ) :
    ∃ (q : P.Rect) (m n : ℕ),
      p = (q.1 : ℕ) + P.b * m ∧
      z + P.a * m = (q.2 : ℕ) + P.k * n ∧
      P.L p z = P.L q.1 q.2 + n * P.d ∧
      P.W p z = P.W q.1 q.2 + ((P.b - P.a) * m + (P.k - 1) * n) * P.d := by
  let m := p / P.b
  let x : Fin P.b := ⟨p % P.b, Nat.mod_lt _ P.b_pos⟩
  let n := (z + P.a * m) / P.k
  let y : Fin P.k := ⟨(z + P.a * m) % P.k, Nat.mod_lt _ (by have := P.k_ge; omega)⟩
  have hpx : p = (x : ℕ) + P.b * m := (Nat.mod_add_div p P.b).symm
  have hzy : z + P.a * m = (y : ℕ) + P.k * n :=
    (Nat.mod_add_div (z + P.a * m) P.k).symm
  have hL : P.L p z = P.L x y + n * P.d := by
    unfold L d
    calc
      P.a * p + P.b * z = P.a * x + P.b * (z + P.a * m) := by rw [hpx]; ring
      _ = _ := by rw [hzy]; ring
  have hW : P.W p z = P.W x y + ((P.b - P.a) * m + (P.k - 1) * n) * P.d := by
    have hab := P.a_lt_b.le
    have hb := P.b_le_d
    have ha := hab.trans hb
    have hk : 1 ≤ P.k := by have := P.k_ge; omega
    unfold W
    zify [ha, hb, hab, hk] at hpx hzy ⊢
    simp only [d, Nat.cast_mul]
    linear_combination ((P.k : ℤ) * P.b - P.a) * hpx + ((P.k : ℤ) * P.b - P.b) * hzy
  exact ⟨(x,y), m, n, hpx, hzy, hL, hW⟩

private def leftRes (q : P.Rect) : Fin P.d := ⟨P.L q.1 q.2 % P.d, Nat.mod_lt _ P.d_pos⟩

def rightRes (q : P.Rect) : Fin P.d := ⟨P.W q.1 q.2 % P.d, Nat.mod_lt _ P.d_pos⟩

private theorem leftRes_injective : Function.Injective P.leftRes := by
  intro q q' h
  have hL : P.L q.1 q.2 ≡ P.L q'.1 q'.2 [MOD P.d] :=
    congrArg Fin.val h
  have hb : P.b ∣ P.d := ⟨P.k, Nat.mul_comm _ _⟩
  have hmodb := hL.of_dvd hb
  have hbY : P.b * (q.2 : ℕ) ≡ P.b * (q'.2 : ℕ) [MOD P.b] :=
    (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)).trans
      (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)).symm
  have hx : (q.1 : ℕ) = (q'.1 : ℕ) :=
    (Nat.ModEq.cancel_left_of_coprime P.coprime.symm
      (hbY.add_right_cancel hmodb)).eq_of_lt_of_lt q.1.isLt q'.1.isLt
  have hy : (q.2 : ℕ) = (q'.2 : ℕ) := by
    unfold L at hL
    rw [hx] at hL
    have hY := Nat.ModEq.add_left_cancel' _ hL
    have hY' : (q.2 : ℕ) * P.b ≡ (q'.2 : ℕ) * P.b [MOD P.k * P.b] := by
      simpa only [d, Nat.mul_comm P.b] using hY
    exact (Nat.ModEq.mul_right_cancel' P.b_pos.ne' hY').eq_of_lt_of_lt q.2.isLt q'.2.isLt
  exact Prod.ext (Fin.ext hx) (Fin.ext hy)

private theorem residue_sum (q : P.Rect) : P.L q.1 q.2 + P.W q.1 q.2 ≡ 0 [MOD P.d] := by
  rw [P.L_add_W]
  exact Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right _ _)

private theorem leftRes_bijective : Function.Bijective P.leftRes := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨P.leftRes_injective, by simp [d, Nat.mul_comm]⟩

private theorem rightRes_bijective : Function.Bijective P.rightRes := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp [d, Nat.mul_comm]⟩
  intro q q' h
  apply P.leftRes_injective
  apply Fin.ext
  exact Nat.ModEq.add_right_cancel (congrArg Fin.val h)
    ((P.residue_sum q).trans (P.residue_sum q').symm)

/-- Coefficient membership for the two three-generator additive monoids. -/
private def Left (t : ℕ) : Prop := ∃ p z c : ℕ, t = P.L p z + c * P.d

private def Right (t : ℕ) : Prop := ∃ p z c : ℕ, t = P.W p z + c * P.d

private theorem generated_three_iff (g h d t : ℕ) :
    t ∈ AddSubmonoid.closure ({g, h, d} : Set ℕ) ↔
      ∃ p z c : ℕ, t = g * p + h * z + c * d := by
  constructor
  · intro ht
    induction ht using AddSubmonoid.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨1, 0, 0, by simp⟩
      · exact ⟨0, 1, 0, by simp⟩
      · exact ⟨0, 0, 1, by simp⟩
    | zero => exact ⟨0, 0, 0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨p, z, c, rfl⟩ := hx
      obtain ⟨p', z', c', rfl⟩ := hy
      exact ⟨p + p', z + z', c + c', by ring⟩
  · rintro ⟨p, z, c, rfl⟩
    let S := AddSubmonoid.closure ({g, h, d} : Set ℕ)
    have hg : g ∈ S := AddSubmonoid.subset_closure (by simp)
    have hh : h ∈ S := AddSubmonoid.subset_closure (by simp)
    have hd : d ∈ S := AddSubmonoid.subset_closure (by simp)
    simpa only [Nat.nsmul_eq_mul, Nat.mul_comm p g, Nat.mul_comm z h] using
      S.add_mem (S.add_mem (S.nsmul_mem hg p) (S.nsmul_mem hh z)) (S.nsmul_mem hd c)

private theorem left_eq_closure (t : ℕ) :
    P.Left t ↔ t ∈ AddSubmonoid.closure ({P.a, P.b, P.d} : Set ℕ) :=
  (generated_three_iff P.a P.b P.d t).symm

private theorem right_eq_closure (t : ℕ) :
    P.Right t ↔ t ∈ AddSubmonoid.closure ({P.d - P.a, P.d - P.b, P.d} : Set ℕ) :=
  (generated_three_iff (P.d - P.a) (P.d - P.b) P.d t).symm

private theorem left_progression (q : P.Rect) (t : ℕ)
    (hr : t % P.d = P.leftRes q) :
    P.Left t ↔ ∃ c : ℕ, t = P.L q.1 q.2 + c * P.d := by
  constructor
  · rintro ⟨p, z, c, ht⟩
    obtain ⟨r, m, n, _, _, hL, _⟩ := P.two_carries p z
    have hform : t = P.L r.1 r.2 + (n + c) * P.d := by rw [ht, hL, Nat.add_mul, Nat.add_assoc]
    have hrq : r = q := by
      apply P.leftRes_injective
      apply Fin.ext
      rw [← hr, hform, Nat.add_mul_mod_self_right]
      rfl
    exact ⟨n + c, hrq ▸ hform⟩
  · rintro ⟨c, ht⟩
    exact ⟨q.1, q.2, c, ht⟩

private theorem right_progression (q : P.Rect) (t : ℕ)
    (hr : t % P.d = P.rightRes q) :
    P.Right t ↔ ∃ c : ℕ, t = P.W q.1 q.2 + c * P.d := by
  constructor
  · rintro ⟨p, z, c, ht⟩
    obtain ⟨r, m, n, _, _, _, hW⟩ := P.two_carries p z
    let carry := (P.b - P.a) * m + (P.k - 1) * n
    have hform : t = P.W r.1 r.2 + (carry + c) * P.d := by
      rw [ht, hW]
      change P.W r.1 r.2 + carry * P.d + c * P.d = _
      exact (Nat.add_assoc _ _ _).trans
        (congrArg (fun t : ℕ => P.W r.1 r.2 + t) (Nat.add_mul carry c P.d).symm)
    have hrq : r = q := by
      apply P.rightRes_bijective.injective
      apply Fin.ext
      rw [← hr, hform, Nat.add_mul_mod_self_right]
      rfl
    exact ⟨carry + c, hrq ▸ hform⟩
  · rintro ⟨c, ht⟩
    exact ⟨q.1, q.2, c, ht⟩

private theorem left_minimum (q : P.Rect) :
    IsLeast {t : ℕ | P.Left t ∧ t % P.d = P.leftRes q} (P.L q.1 q.2) := by
  constructor
  · exact ⟨⟨q.1, q.2, 0, by simp⟩, rfl⟩
  · intro t ht
    obtain ⟨c, rfl⟩ := (P.left_progression q t ht.2).mp ht.1
    exact Nat.le_add_right _ _

private theorem right_minimum (q : P.Rect) :
    IsLeast {t : ℕ | P.Right t ∧ t % P.d = P.rightRes q} (P.W q.1 q.2) := by
  constructor
  · exact ⟨⟨q.1, q.2, 0, by simp⟩, rfl⟩
  · intro t ht
    obtain ⟨c, rfl⟩ := (P.right_progression q t ht.2).mp ht.1
    exact Nat.le_add_right _ _

/-- The opposite residue in the same modulus. -/
def negRes (s : Fin P.d) : Fin P.d :=
  ⟨(P.d - s) % P.d, Nat.mod_lt _ P.d_pos⟩

private theorem leftRes_eq_neg (q : P.Rect) : P.leftRes q = P.negRes (P.rightRes q) := by
  let s := P.rightRes q
  have h₁ : P.L q.1 q.2 + (s : ℕ) ≡ 0 [MOD P.d] :=
    ((Nat.mod_modEq _ _).add_left _).trans (P.residue_sum q)
  have h₂ : P.d - (s : ℕ) + (s : ℕ) ≡ 0 [MOD P.d] := by
    rw [Nat.sub_add_cancel s.isLt.le]
    exact Nat.modEq_zero_iff_dvd.mpr (dvd_refl _)
  apply Fin.ext
  exact Nat.ModEq.add_right_cancel' (s : ℕ) (h₁.trans h₂.symm)

/-- Each residue has a unique rectangle witness that computes both Apéry minima. -/
theorem residue_witness (s : Fin P.d) :
    ∃! q : P.Rect, P.rightRes q = s ∧
      IsLeast {t : ℕ | t ∈ AddSubmonoid.closure ({P.a, P.b, P.d} : Set ℕ) ∧
        t % P.d = P.negRes s} (P.L q.1 q.2) ∧
      IsLeast {t : ℕ | t ∈ AddSubmonoid.closure ({P.d - P.a, P.d - P.b, P.d} : Set ℕ) ∧
        t % P.d = s} (P.W q.1 q.2) := by
  obtain ⟨q, rfl⟩ := P.rightRes_bijective.surjective s
  refine ⟨q, ⟨rfl, ?_, ?_⟩, ?_⟩
  · rw [← P.leftRes_eq_neg]
    simpa only [← P.left_eq_closure] using P.left_minimum q
  · simpa only [← P.right_eq_closure] using P.right_minimum q
  · intro r hr
    exact P.rightRes_bijective.injective hr.1

private def leftSemigroup : AddSubmonoid ℕ :=
  AddSubmonoid.closure ({P.a, P.b, P.d} : Set ℕ)

private def rightSemigroup : AddSubmonoid ℕ :=
  AddSubmonoid.closure ({P.d - P.a, P.d - P.b, P.d} : Set ℕ)

private theorem left_nonempty (r : Fin P.d) :
    ∃ t : ℕ, t ∈ P.leftSemigroup ∧ t % P.d = r := by
  obtain ⟨q, rfl⟩ := P.leftRes_bijective.surjective r
  obtain ⟨hm, hr⟩ := (P.left_minimum q).1
  exact ⟨_, (P.left_eq_closure _).mp hm, hr⟩

private theorem right_nonempty (r : Fin P.d) :
    ∃ t : ℕ, t ∈ P.rightSemigroup ∧ t % P.d = r := by
  obtain ⟨q, rfl⟩ := P.rightRes_bijective.surjective r
  obtain ⟨hm, hr⟩ := (P.right_minimum q).1
  exact ⟨_, (P.right_eq_closure _).mp hm, hr⟩

private noncomputable def wLeft (r : Fin P.d) : ℕ := by
  classical
  exact Nat.find (P.left_nonempty r)

private noncomputable def wRight (r : Fin P.d) : ℕ := by
  classical
  exact Nat.find (P.right_nonempty r)

private theorem wLeft_least (r : Fin P.d) :
    IsLeast {t : ℕ | t ∈ P.leftSemigroup ∧ t % P.d = r} (P.wLeft r) := by
  classical
  exact ⟨Nat.find_spec (P.left_nonempty r), fun _ h => Nat.find_min' _ h⟩

private theorem wRight_least (r : Fin P.d) :
    IsLeast {t : ℕ | t ∈ P.rightSemigroup ∧ t % P.d = r} (P.wRight r) := by
  classical
  exact ⟨Nat.find_spec (P.right_nonempty r), fun _ h => Nat.find_min' _ h⟩

private theorem wLeft_rect (q : P.Rect) : P.wLeft (P.leftRes q) = P.L q.1 q.2 := by
  obtain ⟨r, ⟨hr, hmin, _⟩, _⟩ := P.residue_witness (P.rightRes q)
  have heq : r = q := P.rightRes_bijective.injective hr
  subst r
  rw [← P.leftRes_eq_neg] at hmin
  exact (P.wLeft_least _).unique hmin

private theorem wRight_rect (q : P.Rect) : P.wRight (P.rightRes q) = P.W q.1 q.2 := by
  apply (P.wRight_least _).unique
  simpa only [rightSemigroup, ← P.right_eq_closure] using P.right_minimum q

/-- The thresholds from arXiv:2611.33046v1, §3.1. -/
private noncomputable def u (s : Fin P.d) : ℕ := ((s : ℕ) + P.wLeft (P.negRes s)) / P.d

private noncomputable def v (s : Fin P.d) : ℕ := (P.wRight s - (s : ℕ)) / P.d

private def leftHeight (x y : ℕ) : ℕ := (P.L x y + P.d - 1) / P.d

private def rightHeight (x y : ℕ) : ℕ := P.W x y / P.d

private theorem u_rect (q : P.Rect) : P.u (P.rightRes q) = P.leftHeight q.1 q.2 := by
  let s := P.rightRes q
  let l := P.L q.1 q.2
  change ((s : ℕ) + P.wLeft (P.negRes s)) / P.d = (l + P.d - 1) / P.d
  rw [← P.leftRes_eq_neg q, P.wLeft_rect]
  change ((s : ℕ) + l) / P.d = (l + P.d - 1) / P.d
  have hmod : ((s : ℕ) + l) % P.d = 0 := by
    rw [Nat.add_comm]
    exact ((Nat.mod_modEq _ _).add_left _).trans (P.residue_sum q)
  have hmul : (((s : ℕ) + l) / P.d) * P.d = (s : ℕ) + l := by
    simpa [hmod, Nat.mul_comm] using Nat.div_add_mod ((s : ℕ) + l) P.d
  symm
  apply Nat.div_eq_of_lt_le
  · have := s.isLt
    omega
  · rw [Nat.add_mul, hmul, one_mul]
    omega

private theorem v_rect (q : P.Rect) : P.v (P.rightRes q) = P.rightHeight q.1 q.2 := by
  unfold v rightHeight
  rw [P.wRight_rect]
  let w := P.W q.1 q.2
  have h := Nat.div_add_mod w P.d
  change (w - w % P.d) / P.d = w / P.d
  have hw : w - w % P.d = P.d * (w / P.d) := by omega
  rw [hw, Nat.mul_div_cancel_left _ P.d_pos]

private theorem heights_add (q : P.Rect) : P.leftHeight q.1 q.2 + P.rightHeight q.1 q.2 = q.1 + q.2 := by
  let s := P.rightRes q
  let l := P.L q.1 q.2
  let w := P.W q.1 q.2
  rw [← P.u_rect, ← P.v_rect]
  change P.u s + P.v s = _
  have hl : P.u s = ((s : ℕ) + l) / P.d := by
    unfold u
    rw [← P.leftRes_eq_neg q, P.wLeft_rect]
  have hmod : ((s : ℕ) + l) % P.d = 0 := by
    rw [Nat.add_comm]
    exact ((Nat.mod_modEq _ _).add_left _).trans (P.residue_sum q)
  have hu : P.d * P.u s = (s : ℕ) + l := by
    rw [hl]
    simpa only [hmod, Nat.add_zero] using Nat.div_add_mod ((s : ℕ) + l) P.d
  have hv : P.d * P.v s + (s : ℕ) = w := by
    rw [P.v_rect q]
    exact Nat.div_add_mod w P.d
  have hs : l + w = P.d * ((q.1 : ℕ) + (q.2 : ℕ)) := P.L_add_W _ _
  apply Nat.eq_of_mul_eq_mul_left P.d_pos
  rw [Nat.mul_add]
  omega

private def corner : P.Rect :=
  ⟨⟨P.b - 1, by have := P.b_pos; omega⟩, ⟨P.k - 1, by have := P.k_ge; omega⟩⟩

def U : ℕ := P.leftHeight P.corner.1 P.corner.2

def V : ℕ := P.rightHeight P.corner.1 P.corner.2

private theorem u_le_U (s : Fin P.d) : P.u s ≤ P.U := by
  obtain ⟨q, rfl⟩ := P.rightRes_bijective.surjective s
  rw [P.u_rect]
  unfold U leftHeight L
  apply Nat.div_le_div_right
  have hx : (q.1 : ℕ) ≤ P.corner.1 := by have := q.1.isLt; change (q.1 : ℕ) ≤ P.b - 1; omega
  have hy : (q.2 : ℕ) ≤ P.corner.2 := by have := q.2.isLt; change (q.2 : ℕ) ≤ P.k - 1; omega
  gcongr

private theorem v_le_V (s : Fin P.d) : P.v s ≤ P.V := by
  obtain ⟨q, rfl⟩ := P.rightRes_bijective.surjective s
  rw [P.v_rect]
  unfold V rightHeight W
  apply Nat.div_le_div_right
  have hx : (q.1 : ℕ) ≤ P.corner.1 := by have := q.1.isLt; change (q.1 : ℕ) ≤ P.b - 1; omega
  have hy : (q.2 : ℕ) ≤ P.corner.2 := by have := q.2.isLt; change (q.2 : ℕ) ≤ P.k - 1; omega
  gcongr

private theorem corner_nonzero : 0 < (P.rightRes P.corner : ℕ) := by
  let origin : P.Rect := ⟨⟨0, P.b_pos⟩, ⟨0, by have := P.k_ge; omega⟩⟩
  have horigin : (P.rightRes origin : ℕ) = 0 := by simp [rightRes, origin, W]
  by_contra! h
  have heq : P.corner = origin :=
    P.rightRes_bijective.injective (Fin.ext (by omega))
  have hy : (P.corner.2 : ℕ) = 0 := congrArg (fun q : P.Rect => (q.2 : ℕ)) heq
  have := P.k_ge
  change P.k - 1 = 0 at hy
  omega

private theorem U_pos : 0 < P.U := by
  have hs := P.corner_nonzero
  have hu := P.u_rect P.corner
  unfold u at hu
  rw [← P.leftRes_eq_neg P.corner, P.wLeft_rect] at hu
  have heq : ((P.rightRes P.corner : ℕ) + P.L P.corner.1 P.corner.2) % P.d = 0 := by
    rw [Nat.add_comm]
    exact ((Nat.mod_modEq _ _).add_left _).trans (P.residue_sum P.corner)
  have h := Nat.div_add_mod ((P.rightRes P.corner : ℕ) + P.L P.corner.1 P.corner.2) P.d
  rw [heq, Nat.add_zero, hu] at h
  change P.d * P.U = _ at h
  by_contra! hh
  have hz : P.U = 0 := by omega
  rw [hz, Nat.mul_zero] at h
  omega

private theorem support_size : (P.U - 1) + P.V = P.b + P.k - 3 := by
  have h := P.heights_add P.corner
  have hb := P.b_pos
  have hk := P.k_ge
  have hu := P.U_pos
  change P.U + P.V = (P.b - 1) + (P.k - 1) at h
  omega

/-- Nonempty intervals [p.1,p.2] of positive residues, with both endpoints included. -/
private def intervals (d : ℕ) (holes : Finset ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ico 1 d) ×ˢ (Finset.Ico 1 d)).filter
    fun p => p.1 ≤ p.2 ∧ Finset.Icc p.1 p.2 ⊆ holes

private theorem mem_intervals (d : ℕ) (holes : Finset ℕ) (lo hi : ℕ) :
    (lo, hi) ∈ intervals d holes ↔
      1 ≤ lo ∧ lo ≤ hi ∧ hi < d ∧ ∀ s, lo ≤ s → s ≤ hi → s ∈ holes := by
  simp only [intervals, Finset.mem_filter, Finset.mem_product, Finset.mem_Ico,
    Finset.subset_iff, Finset.mem_Icc, and_imp]
  constructor
  · rintro ⟨⟨⟨hlo, _⟩, ⟨_, hhi⟩⟩, hle, hall⟩
    exact ⟨hlo, hle, hhi, hall⟩
  · rintro ⟨hlo, hle, hhi, hall⟩
    exact ⟨⟨⟨hlo, hle.trans_lt hhi⟩, ⟨hlo.trans hle, hhi⟩⟩, hle, hall⟩

/-- At position n, return the length of the current run and the total number
of intervals seen so far. Position zero is the initial sentinel. -/
private def scanIntervals (holes : Finset ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | n + 1 =>
    let (run, total) := scanIntervals holes n
    let nextRun := if n + 1 ∈ holes then run + 1 else 0
    (nextRun, total + nextRun)

private theorem scan_run_le (holes : Finset ℕ) (n : ℕ) :
    (scanIntervals holes n).1 ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : n + 1 ∈ holes
    · simpa only [scanIntervals, h, ite_true, Nat.succ_eq_add_one, Nat.add_le_add_iff_right] using ih
    · simp [scanIntervals, h]

private theorem scan_run_spec (holes : Finset ℕ) (n lo : ℕ)
    (hlo : 0 < lo) (hle : lo ≤ n) :
    (∀ t, lo ≤ t → t ≤ n → t ∈ holes) ↔ n - (scanIntervals holes n).1 < lo := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hm : n + 1 ∈ holes
    · simp only [scanIntervals, hm, ite_true]
      by_cases he : lo ≤ n
      · have hstep : (∀ t, lo ≤ t → t ≤ n + 1 → t ∈ holes) ↔
            (∀ t, lo ≤ t → t ≤ n → t ∈ holes) := by
          constructor
          · exact fun h t ht htn => h t ht (htn.trans (Nat.le_succ _))
          · intro h t ht htn
            by_cases ht' : t ≤ n
            · exact h t ht ht'
            · have : t = n + 1 := by omega
              simpa only [this] using hm
        simpa only [Nat.succ_sub_succ_eq_sub] using hstep.trans (ih he)
      · have heq : lo = n + 1 := by omega
        subst lo
        constructor
        · intro _
          omega
        · intro _ t ht htn
          have : t = n + 1 := by omega
          simpa only [this] using hm
    · simp only [scanIntervals, hm, ite_false, Nat.sub_zero]
      constructor
      · intro h
        exact (hm (h (n + 1) hle le_rfl)).elim
      · intro h
        omega

private theorem intervals_succ (holes : Finset ℕ) (n : ℕ) :
    intervals (n + 2) holes =
      intervals (n + 1) holes ∪
        ((Finset.Ico (n + 1 - (scanIntervals holes (n + 1)).1 + 1) (n + 2)).image
          (fun lo => (lo, n + 1))) := by
  ext ⟨lo, hi⟩
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_Ico, Prod.mk.injEq, mem_intervals]
  constructor
  · rintro ⟨hlo, hle, hhi, hall⟩
    by_cases he : hi < n + 1
    · exact Or.inl ⟨hlo, hle, he, hall⟩
    · have heq : hi = n + 1 := by omega
      subst hi
      have hb := (scan_run_spec holes (n + 1) lo hlo hle).mp hall
      exact Or.inr ⟨lo, ⟨by omega, by omega⟩, rfl, rfl⟩
  · rintro (⟨hlo, hle, hhi, hall⟩ | ⟨t, ⟨ht, htn⟩, rfl, rfl⟩)
    · exact ⟨hlo, hle, by omega, hall⟩
    · have hlo : 1 ≤ t := by omega
      have hle : t ≤ n + 1 := by omega
      exact ⟨hlo, hle, by omega, (scan_run_spec holes (n + 1) t hlo hle).mpr (by omega)⟩

private theorem scanIntervals_card (holes : Finset ℕ) (n : ℕ) :
    (scanIntervals holes n).2 = (intervals (n + 1) holes).card := by
  induction n with
  | zero => simp [scanIntervals, intervals]
  | succ n ih =>
    change (scanIntervals holes (n + 1)).2 = (intervals (n + 2) holes).card
    rw [intervals_succ, Finset.card_union_of_disjoint]
    · rw [Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h), Nat.card_Ico]
      have hle := scan_run_le holes (n + 1)
      have ht : n + 2 - (n + 1 - (scanIntervals holes (n + 1)).1 + 1) =
          (scanIntervals holes (n + 1)).1 := by omega
      rw [ht, ← ih]
      rfl
    · apply Finset.disjoint_left.mpr
      rintro ⟨lo, hi⟩ h₁ h₂
      obtain ⟨_, _, hhi, _⟩ := (mem_intervals (n + 1) holes lo hi).mp h₁
      obtain ⟨t, _, he⟩ := Finset.mem_image.mp h₂
      have hi' := congrArg Prod.snd he
      change n + 1 = hi at hi'
      omega

private theorem scanIntervals_card_modulus (holes : Finset ℕ) (d : ℕ) (hd : 0 < d) :
    (scanIntervals holes (d - 1)).2 = (intervals d holes).card := by
  simpa only [Nat.sub_add_cancel hd] using scanIntervals_card holes (d - 1)

private theorem interval_count_pos {d : ℕ} {holes : Finset ℕ}
    (h : holes ⊆ Finset.Ico 1 d) :
    0 < (intervals d holes).card ↔ holes.Nonempty := by
  rw [Finset.card_pos]
  constructor
  · rintro ⟨⟨lo, hi⟩, he⟩
    obtain ⟨_, hle, _, hall⟩ := (mem_intervals d holes lo hi).mp he
    exact ⟨lo, hall lo le_rfl hle⟩
  · rintro ⟨s, hs⟩
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp (h hs)
    exact ⟨(s, s), (mem_intervals d holes s s).mpr
      ⟨hlo, le_rfl, hhi, fun t hlo' hhi' => (le_antisymm hhi' hlo').symm ▸ hs⟩⟩

/-- The paper's hole blocks and its interval counts. -/
private noncomputable def B (i : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin P.d)).filter
    (fun s : Fin P.d => 0 < (s : ℕ) ∧ i < P.u s)).image Fin.val

private noncomputable def R (j : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.univ : Finset (Fin P.d)).filter
    (fun s : Fin P.d => 0 < (s : ℕ) ∧ j < P.v s)).image Fin.val

private noncomputable def beta (i : ℕ) : ℕ := (intervals P.d (P.B i)).card

private noncomputable def gamma (j : ℕ) : ℕ := (intervals P.d (P.R j)).card

/-- Computable hole blocks from rectangle arithmetic alone. -/
private def leftHoles (i : ℕ) : Finset ℕ :=
  (Finset.univ.filter fun q : P.Rect => 0 < (P.rightRes q : ℕ) ∧
    i < P.leftHeight q.1 q.2).image (fun q => (P.rightRes q : ℕ))

private def rightHoles (j : ℕ) : Finset ℕ :=
  (Finset.univ.filter fun q : P.Rect => 0 < (P.rightRes q : ℕ) ∧
    j < P.rightHeight q.1 q.2).image (fun q => (P.rightRes q : ℕ))

private theorem leftHoles_eq (i : ℕ) : P.leftHoles i = P.B i := by
  ext s
  simp only [leftHoles, B, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, ⟨hs, hi⟩, rfl⟩
    exact ⟨P.rightRes q, ⟨hs, by rwa [P.u_rect]⟩, rfl⟩
  · rintro ⟨r, ⟨hs, hi⟩, rfl⟩
    obtain ⟨q, rfl⟩ := P.rightRes_bijective.surjective r
    exact ⟨q, ⟨hs, by rwa [← P.u_rect]⟩, rfl⟩

private theorem rightHoles_eq (j : ℕ) : P.rightHoles j = P.R j := by
  ext s
  simp only [rightHoles, R, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, ⟨hs, hj⟩, rfl⟩
    exact ⟨P.rightRes q, ⟨hs, by rwa [P.v_rect]⟩, rfl⟩
  · rintro ⟨r, ⟨hs, hj⟩, rfl⟩
    obtain ⟨q, rfl⟩ := P.rightRes_bijective.surjective r
    exact ⟨q, ⟨hs, by rwa [← P.v_rect]⟩, rfl⟩

def evalBeta (i : ℕ) : ℕ := (scanIntervals (P.leftHoles i) (P.d - 1)).2

def evalGamma (j : ℕ) : ℕ := (scanIntervals (P.rightHoles j) (P.d - 1)).2

private theorem evalBeta_eq (i : ℕ) : P.evalBeta i = P.beta i := by
  unfold evalBeta beta
  rw [scanIntervals_card_modulus _ _ P.d_pos, P.leftHoles_eq]

private theorem evalGamma_eq (j : ℕ) : P.evalGamma j = P.gamma j := by
  unfold evalGamma gamma
  rw [scanIntervals_card_modulus _ _ P.d_pos, P.rightHoles_eq]

private theorem beta_pos_iff (i : ℕ) : 0 < P.beta i ↔ i < P.U := by
  unfold beta
  rw [interval_count_pos]
  · simp only [B, Finset.Nonempty, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, s, ⟨_, hi⟩, rfl⟩
      exact hi.trans_le (P.u_le_U s)
    · intro hi
      exact ⟨_, P.rightRes P.corner, ⟨P.corner_nonzero, by rwa [P.u_rect]⟩, rfl⟩
  · intro s hs
    simp only [B, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨r, ⟨hr, _⟩, rfl⟩ := hs
    exact Finset.mem_Ico.mpr ⟨hr, r.isLt⟩

private theorem gamma_pos_iff (j : ℕ) : 0 < P.gamma j ↔ j < P.V := by
  unfold gamma
  rw [interval_count_pos]
  · simp only [R, Finset.Nonempty, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, s, ⟨_, hj⟩, rfl⟩
      exact hj.trans_le (P.v_le_V s)
    · intro hj
      exact ⟨_, P.rightRes P.corner, ⟨P.corner_nonzero, by rwa [P.v_rect]⟩, rfl⟩
  · intro s hs
    simp only [R, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨r, ⟨hr, _⟩, rfl⟩ := hs
    exact Finset.mem_Ico.mpr ⟨hr, r.isLt⟩

private noncomputable def sourceU : ℕ := Finset.univ.sup P.u

private noncomputable def sourceV : ℕ := Finset.univ.sup P.v

private theorem sourceU_eq : P.sourceU = P.U := by
  apply le_antisymm
  · exact Finset.sup_le fun s _ => P.u_le_U s
  · unfold U
    rw [← P.u_rect P.corner]
    exact Finset.le_sup (f := P.u) (Finset.mem_univ _)

private theorem sourceV_eq : P.sourceV = P.V := by
  apply le_antisymm
  · exact Finset.sup_le fun s _ => P.v_le_V s
  · unfold V
    rw [← P.v_rect P.corner]
    exact Finset.le_sup (f := P.v) (Finset.mem_univ _)

private noncomputable def sourceEntries : List ℕ :=
  ((List.range (P.sourceU - 1)).map fun i => P.beta (i + 1)) ++
    (List.range P.sourceV).map P.gamma

private def entries : List ℕ :=
  ((List.range (P.U - 1)).map fun i => P.evalBeta (i + 1)) ++
    (List.range P.V).map P.evalGamma

private theorem entries_eq : P.entries = P.sourceEntries := by
  simp only [entries, sourceEntries, P.sourceU_eq, P.sourceV_eq, P.evalBeta_eq,
    show P.evalGamma = P.gamma from funext P.evalGamma_eq]

private theorem sourceEntries_pos {z : ℕ} (hz : z ∈ P.sourceEntries) : 0 < z := by
  simp only [sourceEntries, P.sourceU_eq, P.sourceV_eq, List.mem_append,
    List.mem_map, List.mem_range] at hz
  rcases hz with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
  · exact (P.beta_pos_iff _).mpr (by omega)
  · exact (P.gamma_pos_iff _).mpr hj

private noncomputable def sourceList : List ℕ := P.sourceEntries.mergeSort (· ≥ ·)

def spectrumList : List ℕ := P.entries.mergeSort (· ≥ ·)

/-- Entry 0 of this function is the paper's λ₁. -/
def spectrum (n : ℕ) : ℕ := P.spectrumList.getD n 0

noncomputable def sourceSpectrum (n : ℕ) : ℕ := P.sourceList.getD n 0

private theorem spectrumList_eq : P.spectrumList = P.sourceList := by
  simp only [spectrumList, sourceList, P.entries_eq]

private theorem spectrum_length : P.spectrumList.length = P.b + P.k - 3 := by
  have h := (List.mergeSort_perm P.entries (· ≥ ·)).length_eq
  change P.spectrumList.length = P.entries.length at h
  rw [h]
  simpa only [entries, List.length_append, List.length_map, List.length_range] using P.support_size

private theorem spectrum_padded (n : ℕ) (hn : P.b + P.k - 3 ≤ n) : P.spectrum n = 0 :=
  List.getD_eq_default _ _ (by rwa [P.spectrum_length])

private theorem spectrum_correct (n : ℕ) : P.spectrum n = P.sourceSpectrum n := by
  rw [spectrum, sourceSpectrum, P.spectrumList_eq]

private theorem spectrum_multiplicity (z : ℕ) :
    P.spectrumList.count z =
      (((List.range (P.U - 1)).map fun i => P.beta (i + 1)).count z +
       ((List.range P.V).map P.gamma).count z) := by
  rw [spectrumList, (List.mergeSort_perm _ _).count_eq, P.entries_eq,
    sourceEntries, P.sourceU_eq, P.sourceV_eq, List.count_append]

private theorem div_add_le_succ (h : 0 < P.d) (n c : ℕ) (hc : c ≤ P.d) :
    (n + c) / P.d ≤ n / P.d + 1 := by
  calc
    (n + c) / P.d ≤ (n + P.d) / P.d := Nat.div_le_div_right (Nat.add_le_add_left hc _)
    _ = n / P.d + 1 := by
      simpa only [Nat.mul_one] using Nat.add_mul_div_left n 1 h

private theorem left_step_x (x y : ℕ) :
    P.leftHeight (x + 1) y ≤ P.leftHeight x y + 1 := by
  have h := P.div_add_le_succ P.d_pos (P.L x y + P.d - 1) P.a
    (P.a_lt_b.le.trans P.b_le_d)
  have he : P.L (x + 1) y + P.d - 1 = (P.L x y + P.d - 1) + P.a := by
    have := P.d_pos
    simp only [L, Nat.mul_succ]
    omega
  simpa only [leftHeight, he] using h

private theorem left_step_y (x y : ℕ) :
    P.leftHeight x (y + 1) ≤ P.leftHeight x y + 1 := by
  have h := P.div_add_le_succ P.d_pos (P.L x y + P.d - 1) P.b P.b_le_d
  have he : P.L x (y + 1) + P.d - 1 = (P.L x y + P.d - 1) + P.b := by
    have := P.d_pos
    simp only [L, Nat.mul_succ]
    omega
  simpa only [leftHeight, he] using h

private theorem right_step_x (x y : ℕ) :
    P.rightHeight (x + 1) y ≤ P.rightHeight x y + 1 := by
  simpa only [rightHeight, W, Nat.mul_succ, Nat.add_right_comm] using
    P.div_add_le_succ P.d_pos (P.W x y) (P.d - P.a) (Nat.sub_le _ _)

private theorem right_step_y (x y : ℕ) :
    P.rightHeight x (y + 1) ≤ P.rightHeight x y + 1 := by
  simpa only [rightHeight, W, Nat.mul_succ, Nat.add_assoc] using
    P.div_add_le_succ P.d_pos (P.W x y) (P.d - P.b) (Nat.sub_le _ _)

private theorem rectangle_path (h : ℕ → ℕ → ℕ) (h0 : h 0 0 = 0)
    (hx : ∀ x y, h (x + 1) y ≤ h x y + 1)
    (hy : ∀ x y, h x (y + 1) ≤ h x y + 1)
    (x y t : ℕ) (ht : t ≤ h x y) :
    ∃ x' ≤ x, ∃ y' ≤ y, h x' y' = t := by
  induction x with
  | zero =>
    induction y with
    | zero => exact ⟨0, le_rfl, 0, le_rfl, by omega⟩
    | succ y ih =>
      by_cases ht' : t ≤ h 0 y
      · obtain ⟨x', hx', y', hy', he⟩ := ih ht'
        exact ⟨x', hx', y', hy'.trans (Nat.le_succ _), he⟩
      · exact ⟨0, le_rfl, y + 1, le_rfl, by have := hy 0 y; omega⟩
  | succ x ih =>
    by_cases ht' : t ≤ h x y
    · obtain ⟨x', hx', y', hy', he⟩ := ih ht'
      exact ⟨x', hx'.trans (Nat.le_succ _), y', hy', he⟩
    · exact ⟨x + 1, le_rfl, y, le_rfl, by have := hx x y; omega⟩

private def origin : P.Rect := ⟨⟨0, P.b_pos⟩, ⟨0, by have := P.k_ge; omega⟩⟩

private theorem rightRes_zero_rect (q : P.Rect) (hq : (P.rightRes q : ℕ) = 0) :
    q = P.origin := by
  apply P.rightRes_bijective.injective
  apply Fin.ext
  simpa [rightRes, origin, W] using hq

private theorem left_zero : P.leftHeight 0 0 = 0 := by
  simp only [leftHeight, L, Nat.mul_zero, Nat.zero_add]
  exact Nat.div_eq_of_lt (by have := P.d_pos; omega)

private theorem right_zero : P.rightHeight 0 0 = 0 := by simp [rightHeight, W]

private theorem u_attains (t : ℕ) (ht : 0 < t) (hb : t ≤ P.U) :
    ∃ s : Fin P.d, 0 < (s : ℕ) ∧ P.u s = t := by
  obtain ⟨x, hx, y, hy, hu⟩ := rectangle_path P.leftHeight P.left_zero P.left_step_x
    P.left_step_y P.corner.1 P.corner.2 t hb
  let q : P.Rect := ⟨⟨x, hx.trans_lt P.corner.1.isLt⟩, ⟨y, hy.trans_lt P.corner.2.isLt⟩⟩
  have hq : P.leftHeight q.1 q.2 = t := hu
  refine ⟨P.rightRes q, ?_, (P.u_rect q).trans hq⟩
  by_contra! hz
  rw [P.rightRes_zero_rect q (Nat.eq_zero_of_le_zero hz)] at hq
  have hh : P.leftHeight 0 0 = t := hq
  rw [P.left_zero] at hh
  omega

private theorem v_attains (t : ℕ) (ht : 0 < t) (hb : t ≤ P.V) :
    ∃ s : Fin P.d, 0 < (s : ℕ) ∧ P.v s = t := by
  obtain ⟨x, hx, y, hy, hv⟩ := rectangle_path P.rightHeight P.right_zero P.right_step_x
    P.right_step_y P.corner.1 P.corner.2 t hb
  let q : P.Rect := ⟨⟨x, hx.trans_lt P.corner.1.isLt⟩, ⟨y, hy.trans_lt P.corner.2.isLt⟩⟩
  have hq : P.rightHeight q.1 q.2 = t := hv
  refine ⟨P.rightRes q, ?_, (P.v_rect q).trans hq⟩
  by_contra! hz
  rw [P.rightRes_zero_rect q (Nat.eq_zero_of_le_zero hz)] at hq
  have hh : P.rightHeight 0 0 = t := hq
  rw [P.right_zero] at hh
  omega

private theorem mem_B (i : ℕ) (s : Fin P.d) : (s : ℕ) ∈ P.B i ↔ 0 < (s : ℕ) ∧ i < P.u s := by
  simp only [B, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, hr, he⟩
    exact Fin.ext he ▸ hr
  · intro hs
    exact ⟨s, hs, rfl⟩

private theorem mem_R (j : ℕ) (s : Fin P.d) : (s : ℕ) ∈ P.R j ↔ 0 < (s : ℕ) ∧ j < P.v s := by
  simp only [R, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, hr, he⟩
    exact Fin.ext he ▸ hr
  · intro hs
    exact ⟨s, hs, rfl⟩

private theorem intervals_strict {d : ℕ} {small large : Finset ℕ} (h : small ⊆ large)
    (s : ℕ) (hlo : 0 < s) (hhi : s < d) (hs : s ∈ large) (hn : s ∉ small) :
    (intervals d small).card < (intervals d large).card := by
  have hsub : intervals d small ⊆ intervals d large := by
    rintro ⟨lo, hi⟩ hp
    obtain ⟨hlo, hle, hhi, hall⟩ := (mem_intervals d small lo hi).mp hp
    exact (mem_intervals d large lo hi).mpr ⟨hlo, hle, hhi, fun t hl hr => h (hall t hl hr)⟩
  apply Finset.card_lt_card ((Finset.ssubset_iff_of_subset hsub).mpr ?_)
  refine ⟨(s, s), (mem_intervals d large s s).mpr ⟨hlo, le_rfl, hhi, ?_⟩, ?_⟩
  · intro t h₁ h₂
    exact (le_antisymm h₂ h₁).symm ▸ hs
  · intro hm
    exact hn (((mem_intervals d small s s).mp hm).2.2.2 s le_rfl le_rfl)

private theorem beta_strict {i j : ℕ} (hij : i < j) (hi : i < P.U) : P.beta j < P.beta i := by
  obtain ⟨s, hs, hu⟩ := P.u_attains (i + 1) (by omega) (by omega)
  refine intervals_strict (d := P.d) (small := P.B j) (large := P.B i) ?_
    (s : ℕ) hs s.isLt ?_ ?_
  · intro t ht
    simp only [B, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    obtain ⟨r, ⟨hr, hj⟩, rfl⟩ := ht
    exact ⟨r, ⟨hr, hij.trans hj⟩, rfl⟩
  · exact (P.mem_B i s).mpr ⟨hs, by omega⟩
  · exact fun hm => by have := ((P.mem_B j s).mp hm).2; omega

private theorem gamma_strict {i j : ℕ} (hij : i < j) (hi : i < P.V) : P.gamma j < P.gamma i := by
  obtain ⟨s, hs, hv⟩ := P.v_attains (i + 1) (by omega) (by omega)
  refine intervals_strict (d := P.d) (small := P.R j) (large := P.R i) ?_
    (s : ℕ) hs s.isLt ?_ ?_
  · intro t ht
    simp only [R, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    obtain ⟨r, ⟨hr, hj⟩, rfl⟩ := ht
    exact ⟨r, ⟨hr, hij.trans hj⟩, rfl⟩
  · exact (P.mem_R i s).mpr ⟨hs, by omega⟩
  · exact fun hm => by have := ((P.mem_R j s).mp hm).2; omega

private theorem spectrum_multiplicity_le_two (z : ℕ) : P.spectrumList.count z ≤ 2 := by
  have hleft : ((List.range (P.U - 1)).map (fun i => P.beta (i + 1))).Nodup := by
    apply List.Nodup.map_on _ List.nodup_range
    intro i hi j hj he
    simp only [List.mem_range] at hi hj
    by_contra! hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · have := P.beta_strict (show i + 1 < j + 1 by omega) (show i + 1 < P.U by omega)
      omega
    · have := P.beta_strict (show j + 1 < i + 1 by omega) (show j + 1 < P.U by omega)
      omega
  have hright : ((List.range P.V).map P.gamma).Nodup := by
    apply List.Nodup.map_on _ List.nodup_range
    intro i hi j hj he
    simp only [List.mem_range] at hi hj
    by_contra! hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact (P.gamma_strict hij hi).ne' he
    · exact (P.gamma_strict hji hj).ne he
  rw [P.spectrum_multiplicity]
  have hl := List.nodup_iff_count_le_one.mp hleft z
  have hr := List.nodup_iff_count_le_one.mp hright z
  omega

private theorem spectrum_sorted : P.spectrumList.SortedGE := List.sortedGE_mergeSort

private theorem spectrum_pos_iff (n : ℕ) : 0 < P.spectrum n ↔ n < P.b + P.k - 3 := by
  constructor
  · intro h
    by_contra! hn
    rw [P.spectrum_padded n hn] at h
    omega
  · intro h
    have hn : n < P.spectrumList.length := by rwa [P.spectrum_length]
    rw [spectrum, List.getD_eq_getElem _ _ hn]
    apply P.sourceEntries_pos
    have hm := List.getElem_mem (l := P.spectrumList) hn
    simpa only [spectrumList, List.mem_mergeSort, P.entries_eq] using hm

private theorem spectrum_multiplicity_formula (z : ℕ) :
    P.spectrumList.count z =
      (List.range (P.U - 1)).countP (fun i => P.evalBeta (i + 1) == z) +
      (List.range P.V).countP (fun j => P.evalGamma j == z) := by
  rw [spectrumList, (List.mergeSort_perm _ _).count_eq, entries, List.count_append]
  simp only [List.count_eq_countP, List.countP_map, Function.comp_def]

end Params

/-- The bounded formula computes the complete zero-padded spectrum for the named family. -/
theorem family_spectrum (a b k : ℕ) (ha : 0 < a) (hab : a < b)
    (hc : Nat.Coprime a b) (hk : 3 ≤ k) :
    let P : Params := ⟨a, b, k, ha, hab, hc, hk⟩
    (∀ n, P.spectrum n = P.sourceSpectrum n) ∧
    P.spectrumList.SortedGE ∧
    (∀ n, 0 < P.spectrum n ↔ n < b + k - 3) ∧
    (∀ z, P.spectrumList.count z =
      (List.range (P.U - 1)).countP (fun i => P.evalBeta (i + 1) == z) +
      (List.range P.V).countP (fun j => P.evalGamma j == z)) ∧
    (∀ z, P.spectrumList.count z ≤ 2) := by
  dsimp only
  exact ⟨Params.spectrum_correct _, Params.spectrum_sorted _, Params.spectrum_pos_iff _,
    Params.spectrum_multiplicity_formula _, Params.spectrum_multiplicity_le_two _⟩

end CKApery
