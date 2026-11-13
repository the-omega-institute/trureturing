---
bibkey: arunachalam2015robustness
authors: Srinivasan Arunachalam; Vlad Gheorghiu; Tomas Jochym-O'Connor; Michele Mosca; Priyaa Varshinee Srinivasan
year: 2015
title: "On the robustness of bucket brigade quantum RAM"
doi: 10.1088/1367-2630/17/12/123010
url: https://arxiv.org/abs/1502.03450
claim: "Section IV constructs Boolean routing with Toffoli and CNOT gates, describes the addressed one-hot output after n levels, reads the selected classical memory into a bus, and reverses the routing gates to restore the routing ancillas."
strata_touched:
  - D5/S3/Quantum/Routing/ReversibleQram
license: citation-only
triage: anchor
---

# Boolean routing and clean readout

## Verified locator

- DOI: https://doi.org/10.1088/1367-2630/17/12/123010
- URL: https://arxiv.org/abs/1502.03450
- Full text: https://arxiv.org/pdf/1502.03450
- Section IV, printed pages 7–8, Figure 9 and equation (11).

Section IV describes copying the first address bit to a zero ancilla and using
a routing CNOT with an input prepared in one. At subsequent levels, a parent
enable controls a Toffoli into a fresh zero wire; the resulting wire controls
a CNOT into the parent wire. It states:

> Therefore, after two routing node levels, the output of the routing qubits
> is composed of 2² qubits, with only a single branch being excited depending
> on the state of the first two address qubits.

Equation (11) lists the four resulting one-hot basis states. The following
paragraph repeats the procedure for n levels. The final two paragraphs of
Section IV describe leaf-controlled memory readout and reversal of the
routing gates to decouple the routing ancillas.

## Mathematical correspondence

`ReversibleQram.split` uses the parent wire as the left output and a scratch
wire as the right output. For address bit b it first sends
`(l,r)` to `(l,r XOR (b AND l))`, then applies the routing CNOT to obtain
`(l XOR r',r')`. On input `(e,0)` these are `(e AND NOT b,e AND b)`.
The first level at e = true is the paper's address-copy CNOT followed by
the routing CNOT. Recursive products implement the successive levels.
Left and right addresses have leading bits false and true, respectively;
the displayed string order in equation (11) lists the corresponding leaf
basis vectors in reverse visual order.

Each intermediate enabled wire is reused as one of its two outputs. Thus
`Wires n` stores the live routing register in place, and the input is a
single root wire with value e and all remaining scratch wires zero. This
register layout does not assert a count of physical nodes or primitive gates.
The induction proves the operational invariant for all natural n, including
the empty address. The gate permutations also act on every dirty register.

The paper's classical Boolean readout is extended here to classical data in
any additive commutative group: each active leaf adds its fixed datum to the
bus. Reversing the routing restores every routing wire. The matrix result
uses finite data groups and the pinned permutation-matrix action on complex
amplitudes. The group extension and explicit dirty-state semantics are the
mathematical formulation used here, rather than additional claims of the paper.

## Scope

The text explicitly warns that the bus may not be physically realistic
because it interacts with all memory bits. No physical bus locality,
gate-count or depth bound, noise robustness, three-state router implementation,
or copying of an unknown quantum memory is established by this result.
The earlier proposal at https://arxiv.org/abs/0708.1879 supplies historical
context for the bucket-brigade architecture; its qutrit implementation is a
separate construction. No Page–Wootters conclusion follows from Boolean
routing correctness.
