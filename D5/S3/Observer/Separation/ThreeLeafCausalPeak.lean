/- GID: D5/S3/Observer/Separation/ThreeLeafCausalPeak
   generality: G
   mirror-B: D5/B/S3/Observer/Separation/ThreeLeafCausalPeak
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Modular three-leaf promises have uniformly bounded cut costs and unbounded causal-tree peak. -/

import Mathlib

noncomputable section
namespace D5.S3.Observer.Separation.ThreeLeafCausalPeak

abbrev World (m : ℕ) := {p : ZMod m × ZMod m × ZMod m // p.2.2 = p.1 + p.2.1}
def point {m : ℕ} (x y : ZMod m) : World m := ⟨(x, y, x + y), rfl⟩
def xcoord {m : ℕ} (w : World m) := w.val.1
def ycoord {m : ℕ} (w : World m) := w.val.2.1
def zcoord {m : ℕ} (w : World m) := w.val.2.2

def CutAdmits {Ω L R : Type} (f : Ω → Bool) (l : Ω → L) (r : Ω → R) (n : ℕ) : Prop :=
  ∃ (A : Type) (e : L → A) (d : A → R → Bool),
    Nat.card (Set.range (e ∘ l)) ≤ n ∧ ∀ w, d (e (l w)) (r w) = f w

def cutCost {Ω L R : Type} (f : Ω → Bool) (l : Ω → L) (r : Ω → R) : ℕ :=
  sInf {n | CutAdmits f l r n}

structure Protocol (m : ℕ) where
  A : Type
  B : Type
  C : Type
  M : Type
  alpha : ZMod m → A
  beta : ZMod m → B
  gamma : ZMod m → C
  tau : A → B → M
  rho : M → C → Bool

def internal {m : ℕ} (p : Protocol m) (w : World m) : p.M :=
  p.tau (p.alpha (xcoord w)) (p.beta (ycoord w))
def Correct {m : ℕ} (p : Protocol m) (f : World m → Bool) : Prop :=
  ∀ w, p.rho (internal p w) (p.gamma (zcoord w)) = f w

def peak {m : ℕ} (p : Protocol m) : ℕ :=
  max (max (Nat.card (Set.range p.alpha)) (Nat.card (Set.range p.beta)))
    (max (Nat.card (Set.range p.gamma)) (Nat.card (Set.range (internal p))))

def peakOpt {m : ℕ} (f : World m → Bool) : ℕ :=
  sInf {n | ∃ p : Protocol m, Correct p f ∧ peak p ≤ n}

abbrev Tables (m K : ℕ) :=
  (ZMod m → Fin K) × (ZMod m → Fin K) × (ZMod m → Fin K) ×
    (Fin K → Fin K → Fin K) × (Fin K → Fin K → Bool)

def evaluate {m K : ℕ} (t : Tables m K) (w : World m) : Bool :=
  t.2.2.2.2 (t.2.2.2.1 (t.1 (xcoord w)) (t.2.1 (ycoord w))) (t.2.2.1 (zcoord w))

/-- All costs count only reachable messages. Alphabets in `Protocol` and
`CutAdmits` are arbitrary types; the internal node sees only the two leaf messages. -/
theorem result (K : ℕ) (hK : 2 ≤ K) :
    let m := 2 * K ^ 2
    ∃ f : World m → Bool,
      cutCost f xcoord (fun w => (ycoord w, zcoord w)) = 1 ∧
      cutCost f ycoord (fun w => (xcoord w, zcoord w)) = 1 ∧
      cutCost f zcoord (fun w => (xcoord w, ycoord w)) = 1 ∧
      cutCost f (fun w => (xcoord w, ycoord w)) zcoord = 2 ∧
      cutCost f (fun w => (xcoord w, zcoord w)) ycoord ≤ 2 ∧
      cutCost f (fun w => (ycoord w, zcoord w)) xcoord ≤ 2 ∧
      cutCost f id (fun _ => ()) = 2 ∧
      K < peakOpt f := by
  classical
  let m := 2 * K ^ 2
  have hm : 0 < m := by dsimp [m]; positivity
  let : NeZero m := ⟨hm.ne'⟩
  let G := ZMod m
  let W := World m
  let w0 : W := point 0 0
  let : Nonempty W := ⟨w0⟩
  let equiv : (G × G) ≃ W :=
    { toFun := fun p => point p.1 p.2
      invFun := fun w => (xcoord w, ycoord w)
      left_inv := fun _ => rfl
      right_inv := by
        intro w
        apply Subtype.ext
        exact Prod.ext rfl (Prod.ext rfl w.property.symm) }
  have hcardW : Fintype.card W = m ^ 2 := by
    rw [← Fintype.card_congr equiv]
    simp [G, pow_two]
  have xyFull : Function.Surjective (fun w : W => (xcoord w, ycoord w)) :=
    fun p => ⟨point p.1 p.2, rfl⟩
  have xzFull : Function.Surjective (fun w : W => (xcoord w, zcoord w)) := by
    rintro ⟨x, z⟩
    exact ⟨point x (z - x), by simp [point, xcoord, zcoord]⟩
  have yzFull : Function.Surjective (fun w : W => (ycoord w, zcoord w)) := by
    rintro ⟨y, z⟩
    exact ⟨point (z - y) y, by simp [point, ycoord, zcoord]⟩
  have reconstruct (w : W) : point (xcoord w) (ycoord w) = w := equiv.right_inv w
  have reconstructX (w : W) : point (zcoord w - ycoord w) (ycoord w) = w := by
    rw [show zcoord w - ycoord w = xcoord w by
      change w.val.2.2 - w.val.2.1 = w.val.1
      rw [w.property]; simp]
    exact reconstruct w
  have reconstructY (w : W) : point (xcoord w) (zcoord w - xcoord w) = w := by
    rw [show zcoord w - xcoord w = ycoord w by
      change w.val.2.2 - w.val.1 = w.val.2.1
      rw [w.property]; simp]
    exact reconstruct w
  have relabel : ∀ p : Protocol m, peak p ≤ K →
      ∃ t : Tables m K, ∀ w, evaluate t w = p.rho (internal p w) (p.gamma (zcoord w)) := by
    intro p hp
    have bounds := max_le_iff.mp hp
    have ha := (max_le_iff.mp bounds.1).1
    have hb := (max_le_iff.mp bounds.1).2
    have hc := (max_le_iff.mp bounds.2).1
    have hd := (max_le_iff.mp bounds.2).2
    let RA : Type := Set.range p.alpha
    let RB : Type := Set.range p.beta
    let RC : Type := Set.range p.gamma
    let RM : Type := Set.range (internal p)
    let : Fintype RA := Fintype.ofFinite RA
    let : Fintype RB := Fintype.ofFinite RB
    let : Fintype RC := Fintype.ofFinite RC
    let : Fintype RM := Fintype.ofFinite RM
    obtain ⟨ea⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card RA ≤ Fintype.card (Fin K) by simpa [RA, Nat.card_eq_fintype_card] using ha)
    obtain ⟨eb⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card RB ≤ Fintype.card (Fin K) by simpa [RB, Nat.card_eq_fintype_card] using hb)
    obtain ⟨ec⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card RC ≤ Fintype.card (Fin K) by simpa [RC, Nat.card_eq_fintype_card] using hc)
    obtain ⟨ed⟩ := Function.Embedding.nonempty_of_card_le
      (show Fintype.card RM ≤ Fintype.card (Fin K) by simpa [RM, Nat.card_eq_fintype_card] using hd)
    let : Nonempty RA := ⟨⟨p.alpha 0, 0, rfl⟩⟩
    let : Nonempty RB := ⟨⟨p.beta 0, 0, rfl⟩⟩
    let : Nonempty RC := ⟨⟨p.gamma 0, 0, rfl⟩⟩
    let : Nonempty RM := ⟨⟨internal p w0, w0, rfl⟩⟩
    let da := Function.invFun ea
    let db := Function.invFun eb
    let dc := Function.invFun ec
    let dd := Function.invFun ed
    have hda := Function.leftInverse_invFun ea.injective
    have hdb := Function.leftInverse_invFun eb.injective
    have hdc := Function.leftInverse_invFun ec.injective
    have hdd := Function.leftInverse_invFun ed.injective
    have coreach (a : RA) (b : RB) : p.tau a.val b.val ∈ Set.range (internal p) := by
      obtain ⟨x, hx⟩ := a.property
      obtain ⟨y, hy⟩ := b.property
      obtain ⟨w, hw⟩ := xyFull (x, y)
      refine ⟨w, ?_⟩
      dsimp [internal]
      rw [show xcoord w = x from congrArg Prod.fst hw,
        show ycoord w = y from congrArg Prod.snd hw, hx, hy]
    let merge (a : RA) (b : RB) : RM := ⟨p.tau a.val b.val, coreach a b⟩
    let t : Tables m K :=
      (fun x => ea ⟨p.alpha x, x, rfl⟩,
       fun y => eb ⟨p.beta y, y, rfl⟩,
       fun z => ec ⟨p.gamma z, z, rfl⟩,
       fun a b => ed (merge (da a) (db b)),
       fun d c => p.rho (dd d).val (dc c).val)
    refine ⟨t, ?_⟩
    intro w
    let a : RA := ⟨p.alpha (xcoord w), xcoord w, rfl⟩
    let b : RB := ⟨p.beta (ycoord w), ycoord w, rfl⟩
    let c : RC := ⟨p.gamma (zcoord w), zcoord w, rfl⟩
    change p.rho (dd (ed (merge (da (ea a)) (db (eb b))))).val
      (dc (ec c)).val = p.rho (internal p w) (p.gamma (zcoord w))
    have ha' : da (ea a) = a := hda a
    have hb' : db (eb b) = b := hdb b
    have hc' : dc (ec c) = c := hdc c
    rw [ha', hb', hc']
    have hd' : dd (ed (merge a b)) = merge a b := hdd _
    rw [hd']
    rfl
  have htablecard : Fintype.card (Tables m K) = K ^ (3 * m + K ^ 2) * 2 ^ (K ^ 2) := by
    simp only [Tables, Fintype.card_prod, Fintype.card_fun, ZMod.card, Fintype.card_fin,
      Fintype.card_bool]
    rw [show 3 * m + K ^ 2 = m + m + m + K * K by ring]
    simp only [pow_add, pow_mul, pow_two]
    ring
  have hsmall : Fintype.card (Tables m K) < Fintype.card (W → Bool) := by
    rw [htablecard, Fintype.card_fun, Fintype.card_bool, hcardW]
    have hpow : K ≤ 2 ^ K := (Nat.lt_pow_self (by decide : 1 < 2)).le
    have hpoly : 7 * K + 1 < 4 * K ^ 2 := by
      have hsq : 2 * K ≤ K * K := Nat.mul_le_mul_right K hK
      nlinarith
    have hexp : K * (3 * m + K ^ 2) + K ^ 2 < m ^ 2 := by
      have hh := Nat.mul_lt_mul_of_pos_right hpoly (pow_pos (by omega : 0 < K) 2)
      dsimp [m]
      nlinarith [hh]
    calc
      K ^ (3 * m + K ^ 2) * 2 ^ (K ^ 2)
          ≤ (2 ^ K) ^ (3 * m + K ^ 2) * 2 ^ (K ^ 2) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hpow _)
      _ = 2 ^ (K * (3 * m + K ^ 2) + K ^ 2) := by rw [← pow_mul, ← pow_add]
      _ < 2 ^ (m ^ 2) := Nat.pow_lt_pow_right (by decide) hexp
  have notonto : ¬ Function.Surjective (@evaluate m K) := by
    intro h
    exact (not_le_of_gt hsmall) (Fintype.card_le_of_surjective _ h)
  obtain ⟨f, hf⟩ : ∃ f : W → Bool, ∀ t : Tables m K, evaluate t ≠ f := by
    simpa only [Function.Surjective, not_forall, not_exists] using notonto
  have impossible : ∀ p : Protocol m, Correct p f → K < peak p := by
    intro p hp
    by_contra hn
    obtain ⟨t, ht⟩ := relabel p (by omega)
    apply hf t
    funext w
    exact (ht w).trans (hp w)
  have hasProtocol : ∃ p : Protocol m, Correct p f := by
    let p : Protocol m :=
      ⟨G, G, Unit, G × G, id, id, fun _ => (), fun x y => (x,y),
        fun q _ => f (point q.1 q.2)⟩
    exact ⟨p, fun w => congrArg f (reconstruct w)⟩
  have peakLower : K < peakOpt f := by
    have hne : {n | ∃ p : Protocol m, Correct p f ∧ peak p ≤ n}.Nonempty := by
      obtain ⟨p, hp⟩ := hasProtocol
      exact ⟨peak p, p, hp, le_rfl⟩
    obtain ⟨p, hp, hle⟩ := Nat.sInf_mem hne
    exact (impossible p hp).trans_le hle
  have notZ : ¬ ∃ h : G → Bool, ∀ w, f w = h (zcoord w) := by
    rintro ⟨h, hh⟩
    let p : Protocol m :=
      ⟨Unit, Unit, Bool, Unit, fun _ => (), fun _ => (), h,
        fun _ _ => (), fun _ b => b⟩
    have correct : Correct p f := fun w => (hh w).symm
    have hpeak : peak p ≤ 2 := by
      dsimp [peak, p]
      simp only [max_le_iff]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      all_goals
        exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
          (by simp)
    exact (not_lt_of_ge (hpeak.trans hK)) (impossible p correct)
  have notConstant : ¬ ∃ b : Bool, ∀ w, f w = b := by
    rintro ⟨b, hb⟩
    exact notZ ⟨fun _ => b, hb⟩
  have basicCut {L R : Type} (l : W → L) (r : W → R)
      (h : CutAdmits f l r 1) : ∃ d : R → Bool, ∀ w, f w = d (r w) := by
    obtain ⟨A, e, d, hc, hd⟩ := h
    let E := Set.range (e ∘ l)
    let : Fintype E := Fintype.ofFinite E
    have hs : Subsingleton E := Fintype.card_le_one_iff_subsingleton.mp (by
      simpa only [E, Nat.card_eq_fintype_card] using hc)
    refine ⟨d (e (l w0)), ?_⟩
    intro w
    have he : e (l w) = e (l w0) :=
      congrArg Subtype.val (@Subsingleton.elim E hs ⟨_, w, rfl⟩ ⟨_, w0, rfl⟩)
    rw [← hd w, he]
  have cutLower {L R : Type} (l : W → L) (r : W → R)
      (hne : ∃ n, CutAdmits f l r n) : 1 ≤ cutCost f l r := by
    obtain ⟨A, e, d, hc, hd⟩ := Nat.sInf_mem hne
    have : Nonempty (Set.range (e ∘ l)) := ⟨⟨e (l w0), w0, rfl⟩⟩
    have := Nat.card_pos (α := Set.range (e ∘ l))
    exact le_trans (by omega) hc
  have single {L R : Type} (l : W → L) (r : W → R)
      (back : R → W) (hb : ∀ w, back (r w) = w) : cutCost f l r = 1 := by
    have h : CutAdmits f l r 1 := by
      refine ⟨Unit, fun _ => (), fun _ q => f (back q), ?_, ?_⟩
      · exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
          (by simp)
      · intro w; exact congrArg f (hb w)
    exact le_antisymm (Nat.sInf_le h) (cutLower l r ⟨1,h⟩)
  have double {L R : Type} (l : W → L) (r : W → R)
      (back : L → W) (hb : ∀ w, back (l w) = w) : CutAdmits f l r 2 := by
    refine ⟨Bool, fun q => f (back q), fun b _ => b, ?_, ?_⟩
    · exact (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans
        (by simp)
    · intro w; exact congrArg f (hb w)
  have hxy := double (fun w => (xcoord w, ycoord w)) zcoord
    (fun q => point q.1 q.2) reconstruct
  have hxz := double (fun w => (xcoord w, zcoord w)) ycoord
    (fun q => point q.1 (q.2 - q.1)) reconstructY
  have hyz := double (fun w => (ycoord w, zcoord w)) xcoord
    (fun q => point (q.2 - q.1) q.1) reconstructX
  have hall := double id (fun _ => ()) id (fun _ => rfl)
  refine ⟨f, single _ _ (fun q => point (q.2-q.1) q.1) reconstructX,
    single _ _ (fun q => point q.1 (q.2-q.1)) reconstructY,
    single _ _ (fun q => point q.1 q.2) reconstruct, ?_,
    Nat.sInf_le hxz, Nat.sInf_le hyz, ?_, peakLower⟩
  · apply le_antisymm (Nat.sInf_le hxy)
    by_contra h
    have hle : cutCost f (fun w => (xcoord w, ycoord w)) zcoord ≤ 1 :=
      Nat.le_of_lt_succ (Nat.lt_of_not_ge h)
    have hmin := Nat.sInf_mem (show ∃ n, CutAdmits f (fun w => (xcoord w,ycoord w)) zcoord n from ⟨2,hxy⟩)
    have hone : CutAdmits f (fun w => (xcoord w,ycoord w)) zcoord 1 := by
      obtain ⟨A,e,d,hc,hd⟩ := hmin
      exact ⟨A,e,d,le_trans hc hle,hd⟩
    exact notZ (basicCut _ _ hone)
  · apply le_antisymm (Nat.sInf_le hall)
    by_contra h
    have hle : cutCost f id (fun _ => ()) ≤ 1 :=
      Nat.le_of_lt_succ (Nat.lt_of_not_ge h)
    have hmin := Nat.sInf_mem (show ∃ n, CutAdmits f id (fun _ => ()) n from ⟨2,hall⟩)
    have hone : CutAdmits f id (fun _ => ()) 1 := by
      obtain ⟨A,e,d,hc,hd⟩ := hmin
      exact ⟨A,e,d,le_trans hc hle,hd⟩
    obtain ⟨d, hd⟩ := basicCut _ _ hone
    exact notConstant ⟨d (), hd⟩

end D5.S3.Observer.Separation.ThreeLeafCausalPeak
