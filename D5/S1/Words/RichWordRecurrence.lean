/- GID: D5/S1/Words/RichWordRecurrence
   generality: I
   mirror-B: D5/B/S1/Words/RichWordRecurrence
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: Uniform recurrence and exclusion of eventual tail periods for the actual rich words. -/
import D5.S1.Words.RichWordOutputDecoder
import D5.S1.Words.Complexity.MorseHedlund
import Mathlib.Data.Nat.Periodic

/-! Bounded source blocks, recurrent extensions, and literal marker decoding. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RichWordRecurrence

open RankOneMorphismIterationBound (subst image subst_append image_add)
open AbelianBorders.AbelianBorderQuestionDefs (factor)
open MBonacciSentinelDesubstitution (factor_len factor_add factor_get)
open RichWordTypeIOccurrence (word phi boundary typeI phase)
open RichWordTypeIIOccurrence (cut)

private theorem subst_lower {α β : Type*} (f : α → List β) (c : ℕ)
    (h : ∀ a, c ≤ (f a).length) (w : List α) :
    c * w.length ≤ (subst f w).length := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have := h a
    simp only [RankOneMorphismIterationBound.subst_cons, List.length_append,
      List.length_cons, Nat.mul_add, Nat.mul_one]
    omega

private theorem image_subst {α : Type*} (f : α → List α) (k : ℕ) (w : List α) :
    subst (image f (k+1)) w = subst f (subst (image f k) w) := by
  induction w with
  | nil => simp
  | cons a w ih => simp [ih]

private theorem cut_image (k i n : ℕ) :
    factor word (cut k i) (subst (image phi k) (factor word i n)).length =
      subst (image phi k) (factor word i n) := by
  induction k with
  | zero => simp [cut, subst, image, factor_len]
  | succ k ih =>
    rw [image_subst]
    have h := RichWordTypeIOccurrence.actual_fixed_point.2.2.2.2.1
      (cut k i) (subst (image phi k) (factor word i n)).length
    rw [ih] at h
    exact h

private theorem cut_control (k : ℕ) :
    StrictMono (cut k) ∧ cut k 0 = 0 ∧
      ∀ i d, cut k (i+d) ≤ cut k i + 3^k*d := by
  have hb := RichWordTypeIOccurrence.actual_fixed_point.2.1
  have hz := RichWordTypeIOccurrence.actual_fixed_point.2.2.1
  have hup (i d : ℕ) : boundary (i+d) ≤ boundary i + 3*d := by
    induction d with
    | zero => simp
    | succ d ih =>
      have hl : (phi (word (i+d))).length ≤ 3 := by unfold phi; split <;> simp
      rw [show i+(d+1) = (i+d)+1 by omega, RichWordTypeIOccurrence.boundary_succ]
      omega
  induction k with
  | zero => exact ⟨strictMono_id, rfl, by intro i d; simp [cut]⟩
  | succ k ih =>
    refine ⟨hb.comp ih.1, by simpa only [cut, ih.2.1] using hz, ?_⟩
    intro i d
    have h := hb.monotone (ih.2.2 i d)
    have h' := hup (cut k i) (3^k*d)
    simp only [cut, pow_succ]
    nlinarith

private theorem cut_window (g : ℕ → ℕ) (hs : StrictMono g) (hz : g 0 = 0)
    (q : ℕ) : ∃ j, g j ≤ q ∧ q < g (j+1) := by
  induction q with
  | zero => exact ⟨0, by omega, by simpa only [hz] using hs (Nat.zero_lt_succ 0)⟩
  | succ q ih =>
    obtain ⟨j,hj,hk⟩ := ih
    by_cases h : q+1 < g (j+1)
    · exact ⟨j, by omega, h⟩
    · have := hs (show j+1 < j+1+1 by omega)
      exact ⟨j+1, by omega, by omega⟩

private theorem factor_prefix {m : ℕ} (y : ℕ → Fin m) (A : ℕ)
    (w : List (Fin m)) (L i n : ℕ) (hp : w <+: factor y A L)
    (h : i+n ≤ w.length) : factor y (A+i) n = (w.drop i).take n := by
  apply List.ext_getElem
  · simp only [factor_len, List.length_take, List.length_drop]
    omega
  · intro j hj hj'
    have hjn : j < n := by simpa only [factor_len] using hj
    have hij : i+j < w.length := by omega
    have he := hp.getElem hij
    rw [factor_get _ _ _ _ hjn]
    simp only [List.getElem_take, List.getElem_drop]
    rw [he, factor_get _ _ _ _ (by have := hp.length_le; rw [factor_len] at this; omega)]
    congr 1
    omega

/-- Every source factor, including the empty factor, occurs in every sufficiently long window. -/
theorem source_uniform_recurrence (i n : ℕ) :
    ∃ B, ∀ q, ∃ j, q ≤ j ∧ j+n ≤ q+B ∧
      factor word j n = factor word i n := by
  let k := i+n
  have hg : i+n ≤ (image phi k 0).length := by
    have := RichWordTypeIOccurrence.iterate_growth k
    omega
  have hp (a : Fin 7) : image phi k 0 <+: image phi (k+1) a := by
    rw [image_add phi k 1, RankOneMorphismIterationBound.image_one]
    unfold phi
    split <;> simp only [subst, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    · exact List.prefix_append _ _
    · exact List.prefix_append _ _
  refine ⟨3^(k+1)+i+n, ?_⟩
  intro q
  obtain ⟨j,hj,hq⟩ := cut_window (cut (k+1)) (cut_control (k+1)).1
    (cut_control (k+1)).2.1 q
  have hb := (cut_control (k+1)).2.2 j 1
  refine ⟨cut (k+1) (j+1)+i, by omega, by omega, ?_⟩
  have hc : factor word (cut (k+1) (j+1)) (image phi (k+1) (word (j+1))).length =
      image phi (k+1) (word (j+1)) := by
    simpa [factor, subst] using cut_image (k+1) (j+1) 1
  have he := factor_prefix word (cut (k+1) (j+1)) (image phi k 0)
    (image phi (k+1) (word (j+1))).length i n (hc.symm ▸ hp _) hg
  have he' := factor_prefix word 0 (image phi k 0) (image phi k 0).length i n
    (by rw [RichWordTypeIOccurrence.actual_fixed_point.1]) hg
  simpa using he.trans he'.symm

private theorem typeI_length (n : ℕ) : n+1 ≤ (typeI n).length := by
  induction n with
  | zero => simp [typeI]
  | succ n ih =>
    have h := subst_lower phi 2 (by intro a; unfold phi; split <;> simp) (typeI n)
    rw [typeI]
    split <;> simp only [List.length_append, List.length_cons, List.length_nil] <;> omega

private theorem extended_factor {m : ℕ} (y : ℕ → Fin m) (w : List (Fin m))
    (c : Fin m) (a : ℕ) (h : factor y a (w++[c]).length = w++[c]) :
    factor y a w.length = w ∧ y (a+w.length) = c := by
  have ht := congrArg (List.take w.length) h
  have hd := congrArg (List.drop w.length) h
  simp only [List.length_append, List.length_singleton, factor_add] at ht hd
  refine ⟨by simpa [factor_len] using ht, ?_⟩
  have : [y (a+w.length)] = [c] := by simpa [factor_len, factor] using hd
  exact List.cons.inj this |>.1

/-- No positive period works on any eventual tail of the actual seven-letter source. -/
theorem source_no_tail : ¬ Complexity.EventuallyPeriodicWord word := by
  rintro ⟨s,p,hp,hperiod⟩
  have htail (a : ℕ) (ha : s ≤ a) : Function.Periodic (fun t => word (a+t)) p := by
    intro t
    have h := hperiod (a-s+t)
    simpa only [show s+(a-s+t)=a+t by omega, Nat.add_assoc] using h
  have hL : p ≤ (typeI p).length := by have := typeI_length p; omega
  have he := (RichWordTypeIOccurrence.typeI_extensions p).2
  have hfirst : phase p ∈ RichWordTypeIOccurrence.Rext (typeI p) := by rw [he]; simp
  have hsecond : (6 : Fin 7) ∈ RichWordTypeIOccurrence.Rext (typeI p) := by rw [he]; simp
  obtain ⟨a,ha⟩ := hfirst
  obtain ⟨b,hb⟩ := hsecond
  obtain ⟨Ba,hBa⟩ := source_uniform_recurrence a (typeI p++[phase p]).length
  obtain ⟨Bb,hBb⟩ := source_uniform_recurrence b (typeI p++[6]).length
  obtain ⟨c,hc,_,hca⟩ := hBa s
  obtain ⟨d,hd,_,hdb⟩ := hBb s
  obtain ⟨hcw,hcr⟩ := extended_factor word (typeI p) (phase p) c (hca.trans ha)
  obtain ⟨hdw,hdr⟩ := extended_factor word (typeI p) 6 d (hdb.trans hb)
  have hm : (typeI p).length % p < (typeI p).length :=
    (Nat.mod_lt _ hp).trans_le hL
  have heq := congrArg (fun w : List (Fin 7) => w[(typeI p).length % p]?)
    (hcw.trans hdw.symm)
  have hmiddle : word (c+(typeI p).length % p) = word (d+(typeI p).length % p) := by
    simpa [List.getElem?_eq_getElem, factor_len, factor_get, hm] using heq
  have hlast : word (c+(typeI p).length) = word (d+(typeI p).length) :=
    ((htail c hc).map_mod_nat _).symm.trans
      (hmiddle.trans ((htail d hd).map_mod_nat _))
  rw [hcr,hdr] at hlast
  have hv := congrArg Fin.val hlast
  dsimp [phase] at hv
  omega

private theorem length_cut_control (g l : ℕ → ℕ) (D : ℕ)
    (hs : ∀ j, g (j+1) = g j + l j)
    (hl : ∀ j, 0 < l j) (hu : ∀ j, l j ≤ D) :
    StrictMono g ∧ ∀ i n, g i+n ≤ g (i+n) ∧ g (i+n) ≤ g i+D*n := by
  refine ⟨strictMono_nat_of_lt_succ (by intro j; rw [hs]; have := hl j; omega), ?_⟩
  intro i n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show i+(n+1) = (i+n)+1 by omega, hs]
    have := hl (i+n)
    have := hu (i+n)
    simp only [Nat.mul_add, Nat.mul_one]
    constructor <;> omega

private theorem output_control :
    StrictMono RichWordOutputDecoder.E ∧ ∀ i n,
      RichWordOutputDecoder.E i+n ≤ RichWordOutputDecoder.E (i+n) ∧
      RichWordOutputDecoder.E (i+n) ≤ RichWordOutputDecoder.E i+13*n := by
  apply length_cut_control RichWordOutputDecoder.E
    (fun j => (RichWordOutputDecoder.eta (word j)).length) 13 (by intro j; rfl)
  · intro j
    generalize word j = a
    fin_cases a <;> decide
  · intro j
    generalize word j = a
    fin_cases a <;> decide

private theorem output_core (w : List (Fin 7)) (j : ℕ)
    (h : RichWordTypeIOccurrence.Occ w j) :
    RichWordOutputDecoder.Occ (subst RichWordOutputDecoder.eta w++[0])
      (RichWordOutputDecoder.E j) := by
  have he := RichWordOutputDecoder.occurrence_decoder w [] []
    (RichWordOutputDecoder.E j) (by simp) (by simp)
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.add_zero] at he
  apply he.mpr
  refine ⟨j, ⟨by simp, h, Or.inl rfl, ?_⟩, ?_⟩
  · exact List.nil_prefix
  · intro k hk
    exact output_control.1.injective (by simpa using hk.1.symm)

/-- Uniform recurrence of every literal output window, without a boundary-alignment restriction. -/
theorem output_uniform_recurrence (A n : ℕ) :
    ∃ B, ∀ q, ∃ C, q ≤ C ∧ C+n ≤ q+B ∧
      factor RichWordOutputDecoder.x C n = factor RichWordOutputDecoder.x A n := by
  obtain ⟨j,hj,hA⟩ := cut_window RichWordOutputDecoder.E output_control.1 rfl A
  let d := A-RichWordOutputDecoder.E j
  let w := factor word j (n+13)
  have hd : d < 13 := by
    have := (output_control.2 j 1).2
    dsimp [d]
    omega
  have hlen : d+n ≤ (subst RichWordOutputDecoder.eta w).length := by
    have h := subst_lower RichWordOutputDecoder.eta 1
      (by intro a; fin_cases a <;> decide) w
    have hw : w.length = n+13 := factor_len _ _ _
    omega
  have hfull := output_core w j (by simp only [RichWordTypeIOccurrence.Occ, w, factor_len])
  have horig : factor RichWordOutputDecoder.x A n =
      ((subst RichWordOutputDecoder.eta w).drop d).take n := by
    have h := factor_prefix RichWordOutputDecoder.x (RichWordOutputDecoder.E j)
      (subst RichWordOutputDecoder.eta w) (subst RichWordOutputDecoder.eta w++[0]).length
      d n (by rw [hfull]; exact List.prefix_append _ _) hlen
    simpa only [show RichWordOutputDecoder.E j+d=A by dsimp [d]; omega] using h
  obtain ⟨B,hB⟩ := source_uniform_recurrence j (n+13)
  refine ⟨13+13*B+d+n, ?_⟩
  intro q
  obtain ⟨t,ht,hq⟩ := cut_window RichWordOutputDecoder.E output_control.1 rfl q
  obtain ⟨k,hk,hend,hw⟩ := hB (t+1)
  have he0 : k ≤ RichWordOutputDecoder.E k := output_control.1.id_le k
  have hek : RichWordOutputDecoder.E k ≤ RichWordOutputDecoder.E (t+1)+13*B := by
    exact (output_control.1.monotone (by omega : k ≤ t+1+B)).trans
      (output_control.2 (t+1) B).2
  have het := (output_control.2 t 1).2
  have hstart : q < RichWordOutputDecoder.E k :=
    hq.trans_le (output_control.1.monotone hk)
  refine ⟨RichWordOutputDecoder.E k+d, by omega,
    by omega, ?_⟩
  have hfull' := output_core w k (by simpa only [RichWordTypeIOccurrence.Occ,
    show w.length=n+13 from factor_len _ _ _] using hw)
  have h := factor_prefix RichWordOutputDecoder.x (RichWordOutputDecoder.E k)
    (subst RichWordOutputDecoder.eta w) (subst RichWordOutputDecoder.eta w++[0]).length
    d n (by rw [hfull']; exact List.prefix_append _ _) hlen
  exact h.trans horig.symm

private theorem periodic_marker_successor {m : ℕ} (y : ℕ → Fin m) (a : Fin m)
    (g : ℕ → ℕ) (hg : StrictMono g)
    (hmark : ∀ q, y q = a ↔ ∃! j, q = g j)
    (s p j k : ℕ) (hper : ∀ q, s ≤ q → y (q+p) = y q)
    (hs : s ≤ g j) (hk : g k = g j+p) : g (k+1) = g (j+1)+p := by
  have atcut (i : ℕ) : y (g i) = a :=
    (hmark _).mpr ⟨i,rfl,by intro l hl; exact hg.injective hl.symm⟩
  have htranslated : y (g (j+1)+p) = a := by
    rw [hper _ (hs.trans (hg.monotone (by omega))), atcut]
  obtain ⟨l,hl,_⟩ := (hmark _).mp htranslated
  have hkl : k < l := by
    apply hg.lt_iff_lt.mp
    have := hg (show j < j+1 by omega)
    omega
  have hupper : g (k+1) ≤ g (j+1)+p := by
    rw [hl]
    exact hg.monotone (by omega)
  by_contra hne
  have hlt : g (k+1) < g (j+1)+p := by omega
  have hlow := hg (show k < k+1 by omega)
  have hback : y (g (k+1)-p) = a := by
    have h := hper (g (k+1)-p) (by omega)
    rw [show g (k+1)-p+p=g (k+1) by omega, atcut] at h
    exact h.symm
  obtain ⟨v,hv,_⟩ := (hmark _).mp hback
  have hjv : j < v := by apply hg.lt_iff_lt.mp; omega
  have hvj : v < j+1 := by apply hg.lt_iff_lt.mp; omega
  omega

/-- Every positive eventual output period would induce a positive eventual source period. -/
theorem output_no_tail : ¬ Complexity.EventuallyPeriodicWord RichWordOutputDecoder.x := by
  classical
  rintro ⟨s,p,hp,hper⟩
  have htail (q : ℕ) (hq : s ≤ q) :
      RichWordOutputDecoder.x (q+p) = RichWordOutputDecoder.x q := by
    simpa only [show s+(q-s)=q by omega] using hper (q-s)
  have hge (i : ℕ) : i ≤ RichWordOutputDecoder.E i := by
    exact output_control.1.id_le i
  have hshift (t : ℕ) : ∃ k, RichWordOutputDecoder.E k =
      RichWordOutputDecoder.E (s+t)+p := by
    have hm : RichWordOutputDecoder.x (RichWordOutputDecoder.E (s+t)) = 0 :=
      (RichWordOutputDecoder.marker_boundary _).mpr
        ⟨s+t,rfl,by intro k hk; exact output_control.1.injective hk.symm⟩
    have h := htail (RichWordOutputDecoder.E (s+t)) (by have := hge (s+t); omega)
    rw [hm] at h
    obtain ⟨k,hk,_⟩ := (RichWordOutputDecoder.marker_boundary _).mp h
    exact ⟨k,hk.symm⟩
  choose T hT using hshift
  have hsucc (t : ℕ) : T (t+1) = T t+1 := by
    apply output_control.1.injective
    have h := periodic_marker_successor RichWordOutputDecoder.x 0
      RichWordOutputDecoder.E output_control.1 RichWordOutputDecoder.marker_boundary
        s p (s+t) (T t)
      htail (by have := hge (s+t); omega) (hT t)
    rw [hT (t+1)]
    simpa only [Nat.add_assoc] using h.symm
  have hindices (t : ℕ) : T t = T 0+t := by
    induction t with
    | zero => simp
    | succ t ih => rw [hsucc, ih]; omega
  have hpos : s < T 0 := by
    apply output_control.1.lt_iff_lt.mp
    have := hT 0
    simp only [Nat.add_zero] at this
    omega
  apply source_no_tail
  refine ⟨s,T 0-s,by omega,?_⟩
  intro t
  have hw := output_core [word (s+t)] (s+t) (by simp [RichWordTypeIOccurrence.Occ, factor])
  have htranslated : RichWordOutputDecoder.Occ
      (subst RichWordOutputDecoder.eta [word (s+t)]++[0])
      (RichWordOutputDecoder.E (T t)) := by
    unfold RichWordOutputDecoder.Occ at hw ⊢
    rw [hT]
    apply List.ext_getElem
    · simpa only [factor_len] using congrArg List.length hw
    · intro r hr hr'
      have hrn : r < (subst RichWordOutputDecoder.eta [word (s+t)]++[0]).length := by
        simpa only [factor_len] using hr
      rw [factor_get _ _ _ _ hrn]
      rw [show RichWordOutputDecoder.E (s+t)+p+r=
        (RichWordOutputDecoder.E (s+t)+r)+p by omega,
        htail _ (by have := hge (s+t); omega)]
      have he := congrArg (fun w : List (Fin 4) => w[r]?) hw
      rw [List.getElem?_eq_getElem (by rw [factor_len]; exact hrn),
        List.getElem?_eq_getElem hrn] at he
      exact (factor_get _ _ _ _ hrn).symm.trans (Option.some.inj he)
  have hd := RichWordOutputDecoder.marked_core_recovery _ _ htranslated
  have hletter : word (T t) = word (s+t) := by
    simpa [RichWordTypeIOccurrence.Occ, factor] using hd
  rw [hindices t] at hletter
  simpa only [show s+t+(T 0-s)=T 0+t by omega] using hletter

end D5.S1.Words.RichWordRecurrence
