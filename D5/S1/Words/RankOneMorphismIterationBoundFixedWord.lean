/- GID: D5/S1/Words/RankOneMorphismIterationBoundFixedWord
   generality: G
   mirror-B: D5/B/S1/Words/RankOneMorphismIterationBoundFixedWord
   mirror-E: none(waiver:consumed-actual-fixed-word)
   anchors: []
   utility: none
   digest: Actual prolongable binary fixed word and exact one-sided prefix semantics. -/
import D5.S1.Words.RankOneMorphismIterationBoundPresentation
import D5.S1.Words.RankOneMorphismIterationBoundCyclic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.RankOneMorphismIterationBound
open AbelianBorders.AbelianBorderQuestionDefs (factor)

/-- Exact consecutive factors, using the public source word representation. -/
theorem factor_append (x : ℕ → Letter) (i m n : ℕ) :
    factor x i (m+n) = factor x i m ++ factor x (i+m) n := by
  simp only [factor, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_apply]
  congr 1
  omega

@[simp] theorem factor_length (x : ℕ → Letter) (i n : ℕ) : (factor x i n).length = n := by
  simp [factor]

theorem factor_take (x : ℕ → Letter) (i n r : ℕ) (hr : r ≤ n) :
    (factor x i n).take r = factor x i r := by
  simp [factor, ← List.map_take, List.take_range, Nat.min_eq_left hr]

/-- Prefix compatibility follows from the actual first-letter prolongability. -/
theorem image_prefix_succ {f : Morphism} (hp : Prolongable f) (k : ℕ) :
    image f k 0 <+: image f (k+1) 0 := by
  obtain ⟨v,hv,hf⟩ := hp
  rw [image_add f k 1, image_one, hf, subst_cons]
  exact List.prefix_append _ _

theorem image_prefix {f : Morphism} (hp : Prolongable f) {k t : ℕ} (hkt : k ≤ t) :
    image f k 0 <+: image f t 0 := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le hkt
  induction s with
  | zero => simp
  | succ s ih => exact (ih (by omega)).trans (image_prefix_succ hp (k+s))

namespace Parameters
variable {f : Morphism} (p : Parameters f)

include p in
theorem image_growth (i : ℕ) : i < (image f (i+1) 0).length := by
  rw [p.iterated_length]
  have hp : i < p.lam^i := (Nat.lt_two_pow_self : i < 2^i).trans_le (Nat.pow_le_pow_left p.lam_ge_two i)
  have hm : 0 < p.mult (0 : Letter) := by simpa [mult] using p.n_pos
  have hd := p.d_pos
  have hpow : 0 < p.lam^i := pow_pos (by have := p.lam_ge_two; omega) _
  have hprod : p.lam^i ≤ p.mult 0 * (p.d*p.lam^i) := by
    have hmul : 1 ≤ p.mult 0*p.d := Nat.mul_pos hm hd
    simpa only [one_mul, Nat.mul_assoc] using Nat.mul_le_mul_right (p.lam^i) hmul
  omega

/-- A direct, total computation at a growing actual iterate; no proxy automatic
    word is chosen or postulated. -/
def fixedWord (i : ℕ) : Letter := (image f (i+1) 0)[i]'(p.image_growth i)

theorem fixedWord_eq_image (hp : Prolongable f) (k i : ℕ)
    (hi : i < (image f k 0).length) :
    p.fixedWord i = (image f k 0)[i] := by
  let T := max k (i+1)
  have hk := image_prefix hp (Nat.le_max_left k (i+1))
  have hi' := image_prefix hp (Nat.le_max_right k (i+1))
  dsimp [fixedWord]
  exact (hi'.getElem (p.image_growth i)).trans (hk.getElem hi).symm

/-- Every actual finite iterate agrees with this infinite word. -/
theorem fixedWord_prefix (hp : Prolongable f) (k : ℕ) :
    factor p.fixedWord 0 (image f k 0).length = image f k 0 := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [factor, List.getElem_map, List.getElem_range, zero_add]
    exact p.fixedWord_eq_image hp k i hj

theorem fixedWord_semantics (hp : Prolongable f) : IsFixedWord f p.fixedWord :=
  p.fixedWord_prefix hp

/-- Growth rules out another infinite word agreeing with all actual iterates. -/
theorem fixedWord_unique (hp : Prolongable f) {x : ℕ → Letter}
    (hx : IsFixedWord f x) : x = p.fixedWord := by
  funext i
  have h := hx (i+1)
  have hget := congrArg (fun w : Word => w[i]?) h
  have hi := p.image_growth i
  simp only [factor, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    zero_add, List.getElem?_eq_getElem hi, Option.some.injEq] at hget
  exact hget

/-- Exact height of the actual word, with its arbitrary one-sided phase. -/
def height (x : ℕ → Letter) (i : ℕ) : ℤ := p.charge (factor x 0 i)

theorem height_add (x : ℕ → Letter) (i j : ℕ) :
    p.height x (i+j) = p.height x i + p.charge (factor x i j) := by
  rw [height, factor_append, p.charge_append]
  simp only [height, zero_add]

/-- Every prefix height of the actual fixed word is in the finite image-state coding. -/
theorem fixedWord_height_range (hp : Prolongable f) :
    Set.range (p.height p.fixedWord) ⊆ Set.range p.coding := by
  rintro _ ⟨i,rfl⟩
  have hi := p.image_growth i
  have hprefix : (image f (i+1) 0).take i = factor p.fixedWord 0 i := by
    rw [← p.fixedWord_prefix hp (i+1), factor_take _ _ _ _ (by omega)]
  have hm : p.height p.fixedWord i ∈ p.heights (image f (i+1) 0) := by
    exact List.mem_map.mpr ⟨i,List.mem_range.mpr hi,by simp only [heights, height, hprefix]⟩
  rw [← p.finite_height_identity i 0] at hm
  obtain ⟨q,hq,he⟩ := List.mem_map.mp hm
  exact ⟨q,he⟩

theorem fixedWord_height_finite (hp : Prolongable f) :
    (Set.range (p.height p.fixedWord)).Finite :=
  Set.finite_range p.coding |>.subset (p.fixedWord_height_range hp)

/-- Constancy on an arithmetic ray is sufficient for full ultimate abelian
    periodicity, with the exact given preperiod. -/
theorem uap_of_height_ray {x : ℕ → Letter} {r P : ℕ} (hP : 0 < P)
    (h : ∀ j, p.height x (r+j*P) = p.height x r) : UltimatelyAbelianPeriodic x := by
  refine ⟨r,P,hP,?_⟩
  intro j
  apply (p.charge_eq_iff (by simp)).mp
  have hz (j : ℕ) : p.charge (factor x (r+j*P) P) = 0 := by
    have he := p.height_add x (r+j*P) P
    rw [show r+j*P+P = r+(j+1)*P by ring, h (j+1), h j] at he
    omega
  rw [hz j]
  simpa using (hz 0).symm

/-- Finite range forces the common block charge of a UAP ray to be zero. -/
theorem height_ray_of_uap {x : ℕ → Letter} (hfin : (Set.range (p.height x)).Finite)
    (huap : UltimatelyAbelianPeriodic x) :
    ∃ r P : ℕ, 0 < P ∧ ∀ j, p.height x (r+j*P) = p.height x r := by
  obtain ⟨r,P,hP,hblocks⟩ := huap
  have he (j : ℕ) : p.height x (r+j*P) =
      p.height x r + (j : ℤ)*p.charge (factor x r P) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show r+(j+1)*P = (r+j*P)+P by ring, p.height_add, ih]
      have hc := (p.charge_eq_iff (by simp)).mpr (hblocks j)
      rw [hc, Nat.cast_add, Nat.cast_one]
      ring
  have hnotinj : ¬ Function.Injective (fun j : ℕ => p.height x (r+j*P)) := by
    intro hinj
    have hm : Set.range (fun j : ℕ => p.height x (r+j*P)) ⊆ Set.range (p.height x) := by
      rintro _ ⟨j,rfl⟩; exact ⟨r+j*P,rfl⟩
    have hf := hfin.subset hm
    exact Set.infinite_range_of_injective hinj hf
  obtain ⟨i,j,hij,hneq⟩ := Function.not_injective_iff.mp hnotinj
  rw [he i, he j] at hij
  have hdiff : (i : ℤ) - j ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hneq
  have hc : p.charge (factor x r P) = 0 := by
    have hpz : ((i : ℤ)-j)*p.charge (factor x r P) = 0 := by nlinarith
    exact (mul_eq_zero.mp hpz).resolve_left hdiff
  refine ⟨r,P,hP,?_⟩
  intro j; rw [he j,hc,mul_zero,add_zero]

end Parameters
end D5.S1.Words.RankOneMorphismIterationBound
