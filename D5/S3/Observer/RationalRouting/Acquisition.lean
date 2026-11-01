/- GID: D5/S3/Observer/RationalRouting/Acquisition
   generality: I
   mirror-B: D5/B/S3/Observer/RationalRouting/Acquisition
   mirror-E: none(waiver:exact-symbolic-source)
   anchors: []
   utility: none
   digest: Actual dyadic reads recover every original rational on the two-band prior with bounded motion. -/

import D5.S3.Observer.RationalRouting.LowerBounds

/-! Finite actual acquisition on both rational accumulation tails and endpoints. -/

set_option autoImplicit false

namespace D5.S3.Observer.RationalRouting

/-- Preset mode uses LLRL; acquired mode uses LL or RL. -/
def route (preset i : Bool) : List Bool :=
  if i then (if preset then [false,false,true,false] else [true,false]) else [false,false]

def gridScale (preset i : Bool) : ℕ := if preset && i then 4 else 3

def gridValue (preset i : Bool) : ℤ := if i then (if preset then 9 else 5) else 1

/-- Public midpoints between consecutive transformed tail candidates. -/
def threshold (i : Bool) (w : List Bool) (j : ℕ) : ℚ :=
  (attain w (tail i j) + attain w (tail i (j+1)))/2

inductive AcquisitionState
  | start
  | routing (band : Bool) (remaining : List Bool)
  | scan (band : Bool) (candidate scale : ℕ)
  | done (original : ℚ)

/-- A single finite instruction function. Only its read continuations receive
unknown-dependent data; every rational arithmetic operand is public or acquired. -/
def acquisitionCode (preset : Bool) : AcquisitionState → Command AcquisitionState ℚ
  | .start => .read 1 (fun k => .routing (decide (k ≠ 0)) (route preset (decide (k ≠ 0))))
  | .routing i (b :: w) => .move b (.routing i w)
  | .routing i [] => .read (gridScale preset i) (fun k =>
      if k = gridValue preset i then .done (endpoint i) else .scan i 12 0)
  | .scan i j s => .read s (fun k =>
      if ((k+1 : ℤ) : ℚ)/(2 : ℚ)^s ≤ threshold i (route preset i) j then
        .done (tail i j)
      else if threshold i (route preset i) j < (k : ℚ)/(2 : ℚ)^s then
        .scan i (j+1) 0
      else .scan i j (s+1))
  | .done x => .halt x

private theorem step_strict {y r : ℚ} (hy : 0 < y) (hyr : y < r) (b : Bool) :
    step b y < step b r ∧ 0 < step b y := by
  have hr : 0 < r := hy.trans hyr
  cases b
  · dsimp [step]
    constructor
    · apply (div_lt_div_iff₀ (by positivity : 0 < 1+y) (by positivity : 0 < 1+r)).mpr
      nlinarith
    · positivity
  · dsimp [step]
    constructor <;> linarith

private theorem attain_strict {y r : ℚ} (hy : 0 < y) (hyr : y < r) (w : List Bool) :
    attain w y < attain w r := by
  induction w generalizing y r with
  | nil => exact hyr
  | cons b w ih =>
    have h := step_strict hy hyr b
    exact ih h.2 h.1

private theorem band_bounds (i : Bool) {x : ℚ} (hx : Band i x) :
    (if i then (7/12 : ℚ) else 1/12) ≤ x ∧ x ≤ endpoint i := by
  rcases hx with rfl | ⟨n,hn,rfl⟩
  · cases i <;> norm_num [endpoint]
  · have hn' : (12 : ℚ) ≤ n := by exact_mod_cast hn
    have hn0 : 0 < (n : ℚ) := by linarith
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℚ) < 12) hn'
    have hi0 : 0 < 1/(n : ℚ) := by positivity
    cases i <;> dsimp [tail,endpoint] <;> constructor <;> linarith

private theorem band_positive (i : Bool) {x : ℚ} (hx : Band i x) : 0 < x := by
  have h := (band_bounds i hx).1
  cases i <;> norm_num at h ⊢ <;> linarith

private theorem band_report (i : Bool) {x : ℚ} (hx : Band i x) :
    port [] 1 x = if i then 1 else 0 := by
  obtain ⟨hlo,hhi⟩ := band_bounds i hx
  cases i <;> dsimp [port,attain,endpoint] at * <;>
    apply Int.floor_eq_iff.mpr <;> constructor <;> norm_num at * <;> linarith

private theorem route_endpoint (preset i : Bool) :
    (2 : ℚ)^(gridScale preset i) * attain (route preset i) (endpoint i) =
      (gridValue preset i : ℚ) := by
  cases preset <;> cases i <;>
    norm_num [route,gridScale,gridValue,attain,step,endpoint]

private theorem endpoint_report (preset i : Bool) {x : ℚ} (hx : Band i x) :
    port (route preset i) (gridScale preset i) x = gridValue preset i ↔ x = endpoint i := by
  constructor
  · intro h
    by_contra hne
    have hlt : x < endpoint i := lt_of_le_of_ne (band_bounds i hx).2 hne
    have htrans := attain_strict (band_positive i hx) hlt (route preset i)
    have hpow : 0 < (2 : ℚ)^(gridScale preset i) := by positivity
    have hfloor := Int.floor_le ((2 : ℚ)^(gridScale preset i)*attain (route preset i) x)
    rw [show ⌊(2 : ℚ)^(gridScale preset i)*attain (route preset i) x⌋ = gridValue preset i from h] at hfloor
    have hh := route_endpoint preset i
    nlinarith
  · rintro rfl
    dsimp [port]
    rw [route_endpoint]
    exact Int.floor_intCast _

private theorem tail_increasing (i : Bool) {j n : ℕ} (hj : 12 ≤ j) (hjn : j < n) :
    0 < tail i j ∧ tail i j < tail i n := by
  have hj0 : (0 : ℚ) < j := by exact_mod_cast (by omega : 0 < j)
  have hjn' : (j : ℚ) < n := by exact_mod_cast hjn
  have hi := one_div_lt_one_div_of_lt hj0 hjn'
  have hp := band_positive i (Or.inr ⟨j,hj,rfl⟩)
  exact ⟨hp, by dsimp [tail]; linarith⟩

private theorem threshold_position (i : Bool) (w : List Bool) {j n : ℕ}
    (hj : 12 ≤ j) (hjn : j ≤ n) :
    if j = n then attain w (tail i n) < threshold i w j
    else threshold i w j < attain w (tail i n) := by
  have hnext := tail_increasing i hj (Nat.lt_succ_self j)
  have ht := attain_strict hnext.1 hnext.2 w
  by_cases heq : j = n
  · subst n
    simp only [if_pos rfl]
    dsimp [threshold]
    linarith
  · simp only [if_neg heq]
    have hsucc : j+1 ≤ n := by omega
    have hm : attain w (tail i (j+1)) ≤ attain w (tail i n) := by
      rcases eq_or_lt_of_le hsucc with he | he
      · rw [he]
      · have h := tail_increasing i (by omega : 12 ≤ j+1) he
        exact (attain_strict h.1 h.2 w).le
    dsimp [threshold]
    linarith

/-- A cell supplies the exact inequalities needed by the two finite stopping tests. -/
private theorem cell_bounds (w : List Bool) (s : ℕ) (x : ℚ) :
    (port w s x : ℚ)/(2 : ℚ)^s ≤ attain w x ∧
    attain w x < ((port w s x : ℚ)+1)/(2 : ℚ)^s := by
  have hp : 0 < (2 : ℚ)^s := by positivity
  constructor
  · exact (div_le_iff₀ hp).mpr (by simpa [mul_comm,port] using Int.floor_le ((2 : ℚ)^s*attain w x))
  · exact (lt_div_iff₀ hp).mpr (by simpa [mul_comm,port] using Int.lt_floor_add_one ((2 : ℚ)^s*attain w x))

private theorem fine_cell {z t : ℚ} (hne : z ≠ t) (s0 : ℕ) :
    ∃ S : ℕ, s0 ≤ S ∧ ∀ s : ℕ, S ≤ s →
      1/(2 : ℚ)^s < |z-t| := by
  have hgap : 0 < |z-t| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one hgap (by norm_num : (1/2 : ℚ) < 1)
  have hn' : 1/(2 : ℚ)^n < |z-t| := by simpa [div_pow] using hn
  refine ⟨max s0 n, le_max_left _ _, ?_⟩
  intro s hs
  have hns : n ≤ s := (le_max_right _ _).trans hs
  have hpow : (2 : ℚ)^n ≤ (2 : ℚ)^s := pow_le_pow_right₀ (by norm_num) hns
  exact (one_div_le_one_div_of_le (by positivity) hpow).trans_lt hn'

theorem run_unique {State Output : Type} {code : State → Command State Output}
    {x : ℚ} {st : State} {w : List Bool} {out out' : Output} {v v' : List Bool}
    {reads reads' : List (List Bool × ℕ)} (r : Run code x st w out v reads)
    (r' : Run code x st w out' v' reads') : out = out' ∧ v = v' ∧ reads = reads' := by
  induction r generalizing out' v' reads' with
  | halt h => cases r' <;> simp_all
  | work h r ih =>
    cases r' <;> simp_all
    exact ih (by assumption)
  | move h r ih =>
    cases r' <;> simp_all
    exact ih (by assumption)
  | read h r ih =>
    cases r' <;> simp_all
    obtain ⟨ho,hv,hr⟩ := ih (by assumption)
    exact ⟨ho,hv,hr⟩

private theorem sufficiently_fine_stops (w : List Bool) (s : ℕ) (x t : ℚ)
    (hf : 1/(2 : ℚ)^s < |attain w x-t|) :
    ((port w s x : ℚ)+1)/(2 : ℚ)^s ≤ t ∨ t < (port w s x : ℚ)/(2 : ℚ)^s := by
  obtain ⟨hlo,hhi⟩ := cell_bounds w s x
  have hid : ((port w s x : ℚ)+1)/(2 : ℚ)^s =
      (port w s x : ℚ)/(2 : ℚ)^s+1/(2 : ℚ)^s := by ring
  rcases lt_or_ge (attain w x) t with hlt | hge
  · left
    rw [abs_of_neg (sub_neg.mpr hlt)] at hf
    linarith
  · right
    rw [abs_of_nonneg (sub_nonneg.mpr hge)] at hf
    linarith

private theorem scan_finishes (preset i : Bool) (x : ℚ) (j s0 : ℕ) (out : ℚ)
    (hne : attain (route preset i) x ≠ threshold i (route preset i) j)
    (below : attain (route preset i) x < threshold i (route preset i) j →
      ∃ reads, Run (acquisitionCode preset) x (.done (tail i j)) (route preset i)
        out (route preset i) reads)
    (above : threshold i (route preset i) j < attain (route preset i) x →
      ∃ reads, Run (acquisitionCode preset) x (.scan i (j+1) 0) (route preset i)
        out (route preset i) reads) :
    ∃ reads, Run (acquisitionCode preset) x (.scan i j s0) (route preset i)
      out (route preset i) reads := by
  let w := route preset i
  let t := threshold i w j
  obtain ⟨S,hS,hfine⟩ := fine_cell hne s0
  have finish : ∀ s : ℕ,
      ((port w s x : ℚ)+1)/(2 : ℚ)^s ≤ t ∨ t < (port w s x : ℚ)/(2 : ℚ)^s →
      ∃ reads, Run (acquisitionCode preset) x (.scan i j s) w out w reads := by
    intro s hstop
    obtain ⟨hlo,hhi⟩ := cell_bounds w s x
    by_cases hb : ((port w s x : ℚ)+1)/(2 : ℚ)^s ≤ t
    · obtain ⟨reads,run⟩ := below (by dsimp [t,w] at *; linarith)
      refine ⟨(w,s)::reads, Run.read rfl ?_⟩
      simpa [acquisitionCode, hb, w, t, Int.cast_add, Int.cast_one] using run
    · have ha : t < (port w s x : ℚ)/(2 : ℚ)^s := hstop.resolve_left hb
      obtain ⟨reads,run⟩ := above (by dsimp [t,w] at *; linarith)
      refine ⟨(w,s)::reads, Run.read rfl ?_⟩
      simpa [acquisitionCode, hb, ha, w, t, Int.cast_add, Int.cast_one] using run
  have atS : ∃ reads, Run (acquisitionCode preset) x (.scan i j S) w out w reads := by
    apply finish
    exact sufficiently_fine_stops w S x t (hfine S le_rfl)
  have back : ∀ s, s < S →
      (∃ reads, Run (acquisitionCode preset) x (.scan i j (s+1)) w out w reads) →
      ∃ reads, Run (acquisitionCode preset) x (.scan i j s) w out w reads := by
    intro s hs next
    by_cases hb : ((port w s x : ℚ)+1)/(2 : ℚ)^s ≤ t
    · exact finish s (Or.inl hb)
    by_cases ha : t < (port w s x : ℚ)/(2 : ℚ)^s
    · exact finish s (Or.inr ha)
    obtain ⟨reads,run⟩ := next
    refine ⟨(w,s)::reads, Run.read rfl ?_⟩
    simpa [acquisitionCode, hb, ha, w, t, Int.cast_add, Int.cast_one] using run
  exact Nat.decreasingInduction (fun s hs ih => back s hs ih) atS hS

private theorem tail_scan (preset i : Bool) (n : ℕ) (hn : 12 ≤ n) :
    ∃ reads, Run (acquisitionCode preset) (tail i n) (.scan i 12 0)
      (route preset i) (tail i n) (route preset i) reads := by
  let w := route preset i
  have atN : ∀ j, j ≤ n → 12 ≤ j →
      ∃ reads, Run (acquisitionCode preset) (tail i n) (.scan i j 0) w (tail i n) w reads := by
    apply Nat.decreasingInduction
    · intro j hj ih h12
      have hjn : j ≤ n := by omega
      have hneq : j ≠ n := by omega
      have hpos := threshold_position i w h12 hjn
      simp only [if_neg hneq] at hpos
      apply scan_finishes preset i (tail i n) j 0 (tail i n) (ne_of_gt hpos)
      · intro h; exact (not_lt_of_gt hpos h).elim
      · intro _; exact ih (by omega)
    · intro _
      have hpos := threshold_position i w hn (le_refl n)
      simp only [if_pos rfl] at hpos
      apply scan_finishes preset i (tail i n) n 0 (tail i n) (ne_of_lt hpos)
      · intro _; exact ⟨[], Run.halt rfl⟩
      · intro h; exact (not_lt_of_gt hpos h).elim
  exact atN 12 hn le_rfl

private theorem route_run (preset i : Bool) {x : ℚ} (hx : Band i x) :
    ∃ reads, Run (acquisitionCode preset) x (.routing i []) (route preset i)
      x (route preset i) reads := by
  by_cases he : x = endpoint i
  · subst x
    have hg := (endpoint_report preset i (Or.inl rfl)).mpr rfl
    refine ⟨[(route preset i,gridScale preset i)], Run.read rfl ?_⟩
    simpa [acquisitionCode,hg] using
      (Run.halt (code := acquisitionCode preset) (x := endpoint i)
        (w := route preset i) (by rfl) :
          Run (acquisitionCode preset) (endpoint i) (.done (endpoint i))
            (route preset i) (endpoint i) (route preset i) [])
  · have hg : port (route preset i) (gridScale preset i) x ≠ gridValue preset i := by
      intro h; exact he ((endpoint_report preset i hx).mp h)
    rcases hx with hx | ⟨n,hn,rfl⟩
    · exact (he hx).elim
    obtain ⟨reads,run⟩ := tail_scan preset i n hn
    refine ⟨(route preset i,gridScale preset i)::reads, Run.read rfl ?_⟩
    simpa [acquisitionCode,hg] using run

private theorem routing_prefix (preset i : Bool) (x out : ℚ) (todo w v : List Bool)
    (reads : List (List Bool × ℕ))
    (run : Run (acquisitionCode preset) x (.routing i []) (w++todo) out v reads) :
    Run (acquisitionCode preset) x (.routing i todo) w out v reads := by
  induction todo generalizing w with
  | nil => simpa using run
  | cons b todo ih =>
    apply Run.move (code := acquisitionCode preset) rfl
    apply ih
    simpa [List.append_assoc] using run

private theorem acquisition_run (preset i : Bool) {x : ℚ} (hx : Band i x) :
    ∃ reads, Run (acquisitionCode preset) x .start [] x (route preset i) reads := by
  obtain ⟨reads,run⟩ := route_run preset i hx
  have hr := routing_prefix preset i x x (route preset i) [] (route preset i) reads (by simpa using run)
  have hb := band_report i hx
  refine ⟨([],1)::reads, Run.read rfl ?_⟩
  cases i <;> simpa [acquisitionCode,hb] using hr

/-- Actual same-source acquisition of the whole original rational. The endpoint
is settled by a finite grid read; every tail member uses finitely many stationary
midpoint comparisons. No equality is inferred from infinite refinement. -/
theorem actual_rational_acquisition :
    Correct (acquisitionCode false) .start id ∧
    ActionCap (acquisitionCode false) .start 2 ∧
    Correct (acquisitionCode true) .start id ∧
    ActionCap (acquisitionCode true) .start 4 ∧
    Preset (acquisitionCode true) .start (fun k => [false,false,true,false][k]?.getD false) ∧
    (∀ x, Prior x → 0 < x) := by
  have correct : ∀ preset, Correct (acquisitionCode preset) .start id := by
    intro preset x hx
    obtain ⟨i,hi⟩ := hx
    obtain ⟨reads,run⟩ := acquisition_run preset i hi
    refine ⟨⟨x,route preset i,reads,run⟩,?_⟩
    intro out v reads' run'
    exact (run_unique run' run).1
  have cap : ∀ preset, ActionCap (acquisitionCode preset) .start (if preset then 4 else 2) := by
    intro preset x hx out v reads run
    obtain ⟨i,hi⟩ := hx
    obtain ⟨reads',run'⟩ := acquisition_run preset i hi
    have hv := (run_unique run run').2.1
    rw [hv]
    cases preset <;> cases i <;> norm_num [route]
  refine ⟨correct false,cap false,correct true,cap true,?_,?_⟩
  · intro x hx out v reads run
    obtain ⟨i,hi⟩ := hx
    obtain ⟨reads',run'⟩ := acquisition_run true i hi
    have hv := (run_unique run run').2.1
    rw [hv]
    intro k hk
    cases i <;> norm_num [route] at hk ⊢ <;> interval_cases k <;> rfl
  · rintro x ⟨i,hi⟩
    exact band_positive i hi

#print axioms actual_rational_acquisition

end D5.S3.Observer.RationalRouting
