/- GID: D5/S0/Certificates/Games/PekalaOnlineMajorityFourColourRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/Games/PekalaOnlineMajorityFourColourRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S0/Certificates/Games/PekalaOnlineMajorityFourColourRefutation.claim; result=D5/S0/Certificates/Games/PekalaOnlineMajorityFourColourRefutation.result; claim=D5/S0/Certificates/Games/PekalaOnlineMajorityFourColourRefutation.claim
   digest: A checked finite Presenter strategy refutes a universal four-colour online majority strategy for vertex counts five through seven. -/

/- proof_shape: result: content
   escape_witness: The live certValid computation checks every reply to the
     479-node Presenter strategy and every terminal minimum-degree condition.
   admission_basis: open-problem-resolution (issue #11457) -/

/-
Pekala, arXiv:2609.37973v1, Problem 11 asks whether four colours suffice
online when the final graph has n in {5,6,7} vertices and minimum degree
exactly two. The claim below is the joint affirmative assertion.

Edges are indexed by unordered vertex pairs. A state uses zero for an
unrevealed edge and positive integers for colour classes. Normalization
numbers colour classes by first appearance; choosing any existing class or
one fresh class represents every possible response with four named colours,
up to a permutation of the palette. This symmetry reduction preserves
majority and edge-incidence properties.

The certificate checks an adaptive five-vertex Presenter strategy. Its
bad leaves all have minimum degree exactly two, and its checks range over
every available colour class. The finite strategy refutes the joint
affirmative assertion by its five-vertex instance. The combinatorial
extension to six and seven vertices is recorded in the Problems dossier:
after a bad five-vertex terminal graph, choose one vertex at which majority
fails and connect each new vertex to two other old vertices. The bad
vertex is unchanged; each new vertex has degree two.
-/

import Mathlib.Data.List.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace D5.S0.Certificates.Games.PekalaOnlineMajorityFourColourRefutation

abbrev State := List Nat

def edges : List (Nat × Nat) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4),
   (2, 3), (2, 4), (3, 4)]

def edgesFor (n : Nat) : List (Nat × Nat) :=
  if n = 5 then edges else
    (List.range n).flatMap fun u =>
      ((List.range n).filter fun v => u < v).map fun v => (u, v)

def colourAt (s : State) (e : Nat) : Nat := s[e]?.getD 0

def incidentFor (n e v : Nat) : Bool :=
  let pair := (edgesFor n)[e]?.getD (0, 0)
  pair.1 == v || pair.2 == v

def degreeFor (n : Nat) (s : State) (v : Nat) : Nat :=
  ((List.range (edgesFor n).length).filter fun e =>
    colourAt s e != 0 && incidentFor n e v).length

def frequencyFor (n : Nat) (s : State) (v c : Nat) : Nat :=
  ((List.range (edgesFor n).length).filter fun e =>
    colourAt s e == c && incidentFor n e v).length

def terminalBadFor (n : Nat) (s : State) : Bool :=
  ((List.range n).all fun v => 2 <= degreeFor n s v) &&
  ((List.range n).any fun v => degreeFor n s v == 2) &&
  ((List.range n).any fun v =>
    (List.range 4).any fun c =>
      degreeFor n s v < 2 * frequencyFor n s v (c + 1))

def terminalBad (s : State) : Bool := terminalBadFor 5 s

def normalizeAux (seen : List Nat) : List Nat → List Nat
  | [] => []
  | c :: cs =>
    if c == 0 then 0 :: normalizeAux seen cs
    else
      let i := seen.idxOf c
      if i < seen.length then (i + 1) :: normalizeAux seen cs
      else (seen.length + 1) :: normalizeAux (seen ++ [c]) cs

def normalize (s : State) : State := normalizeAux [] s

def update (s : State) (e c : Nat) : State := normalize (s.set e c)

def initialFor (n : Nat) : State := List.replicate (edgesFor n).length 0

def initial : State := initialFor 5

def replyCount (s : State) : Nat := min 4 (s.foldl max 0 + 1)

inductive PresenterWins : Nat → State → Prop where
  | stop {fuel : Nat} {s : State} (h : terminalBad s = true) :
      PresenterWins fuel s
  | step {fuel : Nat} {s : State} (e : Nat) (hbound : e < 10)
      (hfree : colourAt s e = 0)
      (h : ∀ c : Fin (replyCount s),
        PresenterWins fuel (update s e (c.val + 1))) :
      PresenterWins (fuel + 1) s

def AlgorithmWinsFor (n : Nat) : Nat → State → Prop
  | 0, s => terminalBadFor n s = false
  | fuel + 1, s =>
      terminalBadFor n s = false ∧
      ∀ e : Nat, e < (edgesFor n).length → colourAt s e = 0 →
        ∃ c : Fin (replyCount s),
          AlgorithmWinsFor n fuel (update s e (c.val + 1))

abbrev AlgorithmWins : Nat → State → Prop := AlgorithmWinsFor 5

def claim : Prop :=
  ∀ n : Nat, n ∈ [5, 6, 7] →
    AlgorithmWinsFor n (edgesFor n).length (initialFor n)

inductive Cert where
  | stop
  | step (edge : Nat) (children : List Cert)

def certValid : Nat → State → Cert → Bool
  | _, s, .stop => terminalBad s
  | 0, _, .step _ _ => false
  | fuel + 1, s, .step edge children =>
      decide (edge < 10) && (colourAt s edge == 0) &&
      (List.range (replyCount s)).all (fun c =>
        certValid fuel (update s edge (c + 1))
          (children[c]?.getD .stop))

private theorem cert_sound :
    ∀ fuel s cert, certValid fuel s cert = true → PresenterWins fuel s := by
  intro fuel
  induction fuel with
  | zero =>
    intro s cert h
    cases cert with
    | stop => exact PresenterWins.stop h
    | step edge children => simp [certValid] at h
  | succ fuel ih =>
    intro s cert h
    cases cert with
    | stop => exact PresenterWins.stop h
    | step edge children =>
      simp only [certValid, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hbound, hfree⟩, hchildren⟩ := h
      exact PresenterWins.step edge (by simpa only [decide_eq_true_eq] using hbound) hfree
        (fun c => ih _ _ ((List.all_eq_true.mp hchildren) c.val
          (List.mem_range.mpr c.isLt)))

def certificate : Cert :=
  Cert.step 0 [
    Cert.step 1 [
      Cert.step 5 [
        Cert.step 8 [
          Cert.step 9 [
            Cert.stop,
            Cert.stop
          ],
          Cert.step 9 [
            Cert.stop,
            Cert.stop,
            Cert.stop
          ]
        ],
        Cert.step 8 [
          Cert.step 9 [
            Cert.stop,
            Cert.stop,
            Cert.stop
          ],
          Cert.step 9 [
            Cert.stop,
            Cert.stop,
            Cert.stop
          ],
          Cert.step 9 [
            Cert.stop,
            Cert.stop,
            Cert.stop,
            Cert.stop
          ]
        ]
      ],
      Cert.step 2 [
        Cert.step 4 [
          Cert.step 3 [
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop,
              Cert.stop
            ]
          ],
          Cert.step 3 [
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop,
              Cert.stop
            ]
          ],
          Cert.step 6 [
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop,
              Cert.stop
            ]
          ]
        ],
        Cert.step 4 [
          Cert.step 3 [
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop,
              Cert.stop
            ]
          ],
          Cert.step 3 [
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop,
              Cert.stop
            ]
          ],
          Cert.step 6 [
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop,
              Cert.stop
            ]
          ]
        ],
        Cert.step 3 [
          Cert.step 6 [
            Cert.step 7 [
              Cert.stop,
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 5 [
              Cert.step 7 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 7 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 4 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 4 [
                Cert.step 7 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ],
                Cert.stop,
                Cert.step 9 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ],
                Cert.step 9 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ]
              ]
            ],
            Cert.step 4 [
              Cert.step 7 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 5 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 7 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 5 [
                Cert.step 7 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ],
                Cert.step 8 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ],
                Cert.stop,
                Cert.step 8 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ]
              ]
            ],
            Cert.step 4 [
              Cert.step 7 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 5 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 5 [
                Cert.step 8 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ],
                Cert.step 8 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ],
                Cert.stop,
                Cert.step 8 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ]
              ],
              Cert.step 7 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ]
            ]
          ],
          Cert.step 8 [
            Cert.step 7 [
              Cert.step 5 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 5 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 4 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 4 [
                Cert.stop,
                Cert.step 5 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ],
                Cert.step 9 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ],
                Cert.step 9 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ]
              ]
            ],
            Cert.step 5 [
              Cert.stop,
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 4 [
              Cert.step 5 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 5 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 5 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 7 [
                Cert.step 6 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ],
                Cert.step 5 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ],
                Cert.stop,
                Cert.step 6 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ]
              ]
            ],
            Cert.step 4 [
              Cert.step 5 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 5 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 7 [
                Cert.step 6 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ],
                Cert.step 6 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ],
                Cert.stop,
                Cert.step 6 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ]
              ],
              Cert.step 5 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ]
            ]
          ],
          Cert.step 9 [
            Cert.step 7 [
              Cert.step 4 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 4 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 4 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 5 [
                Cert.stop,
                Cert.step 8 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ],
                Cert.step 4 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ],
                Cert.step 8 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ]
              ]
            ],
            Cert.step 5 [
              Cert.step 4 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 4 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 4 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 7 [
                Cert.step 6 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ],
                Cert.stop,
                Cert.step 4 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ],
                Cert.step 6 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ]
              ]
            ],
            Cert.step 4 [
              Cert.stop,
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 5 [
              Cert.step 4 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 7 [
                Cert.step 6 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ],
                Cert.stop,
                Cert.step 6 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ],
                Cert.step 6 [
                  Cert.stop,
                  Cert.stop,
                  Cert.stop,
                  Cert.stop
                ]
              ],
              Cert.step 4 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 4 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ]
            ]
          ],
          Cert.step 4 [
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 9 [
              Cert.stop,
              Cert.stop,
              Cert.stop,
              Cert.stop
            ],
            Cert.step 9 [
              Cert.step 8 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 6 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.stop,
              Cert.stop
            ],
            Cert.step 9 [
              Cert.step 7 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.step 5 [
                Cert.stop,
                Cert.stop,
                Cert.stop,
                Cert.stop
              ],
              Cert.stop,
              Cert.stop
            ]
          ]
        ]
      ]
    ]
  ]

theorem result : ¬ claim := by
  intro positive
  have incompatible : ∀ fuel s, PresenterWins fuel s → ¬ AlgorithmWins fuel s := by
    intro fuel s hw ha
    induction fuel generalizing s with
    | zero =>
      cases hw with
      | stop h =>
        change terminalBad s = false at ha
        simp [h] at ha
    | succ fuel ih =>
      cases hw with
      | stop h =>
        have hf := ha.1
        change terminalBad s = false at hf
        simp [h] at hf
      | step edge hbound hfree h =>
        obtain ⟨_, hresp⟩ := ha
        obtain ⟨c, hc⟩ := hresp edge hbound hfree
        exact ih _ (h c) hc
  have hv : certValid 10 initial certificate = true := by decide
  have five : AlgorithmWins 10 initial := by
    simpa [AlgorithmWins, initial, initialFor, edgesFor, edges] using
      positive 5 (by decide)
  exact incompatible 10 initial (cert_sound 10 initial certificate hv) five

#print axioms claim
#print axioms result

end D5.S0.Certificates.Games.PekalaOnlineMajorityFourColourRefutation
