---
bibkey: nearywoodsmurphyglaschick2014wang
authors: "Turlough Neary; Damien Woods; Niall Murphy; Rainer Glaschick"
year: 2014
title: "Wang's B machines are efficiently universal, as is Hasenjaeger's small universal electromechanical toy"
doi: 10.48550/arXiv.1304.0053
url: https://arxiv.org/pdf/1304.0053v2
claim: A deterministic single binary tape Turing computation has an effective non-erasing Wang B simulation; the supplied tape-time bound is cubic in the simulated time under the paper's tape-length convention.
strata_touched: []
license: citation-only
triage: anchor
---

# Non-erasing tape simulation supply

The primary version is arXiv:1304.0053v2. Pages 4–5, Definitions 3–4
and Lemma 5, give an overview of copying successive encoded Turing
configurations to fresh tape, using a head bit followed by the 10/01
value pair. They do not list a copier transition table, a delimiter
protocol or an executable output decoder. Pages 5–9, Definition 6 and Theorem 7, give the bilateral
Wang B tape, instructions L, R, M, J, the 10/11 encoding, blank-pair
extension, thirteen-instruction state blocks and at most eight B
instructions per non-erasing Turing step. Section 3.1.3 treats halting.
Theorem 1 composes these simulations. This is `literature-attested`
intermediate supply, rather than a new universality result.

M leaves an already marked cell unchanged. J jumps on one and falls
through on zero. The tape is bi-infinite and initially blank away from
the finite supplied encoding. The simulation construction is effective on machine
descriptions and input configurations; it does not supply input
acquisition, physical pointers, a source port, a material allocator or a
finite output connection. The time estimate counts abstract tape
instructions. For an initial nonblank window of length n, the copying
argument must retain n as well as the simulated time; it cannot assume
an arbitrary long input fits in t cells when t is small.

The cubic-time quotation uses the self-contained construction in this
paper, without relying on the proof in Wang's original paper.
No claim concerning the three-tape electromechanical device is used.
The explicit eight-bit monotone metadata, finite block expansion,
record handoff and decoder in ML-N are a refinement for the owned LAB
consumer, not additional details attributed to the primary paper.
Their cursor flags and old copies must be retained and charged.
The LAB realization and its indexed-law application have their separate
installation and simultaneous-resource premises in
[Monotone LAB Indexed Execution](../../docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MONOTONE_LAB_INDEXED_EXECUTION.md).


## Finite stack compiler used before the Wang construction

The Boolean-stack algebra and its four-symbol tape controller are a
separate licensed supplier, RBarish-UTokyo/NPCompleteness-Lean4 revision
`3e603e795b44fedcf7d6dd65b7d1e30547ead925`, under Apache-2.0. The exact
repository content-port correspondence and full license are in
[Binary machine supply](../../docs/reports/licenses/RBarishBinaryMachine.md).
`StackProgram.compile_run` requires a finite injective label encoding;
`StackSimulation.controller_simulates` requires an actual terminating
stack run, finite represented registers and a sufficient finite room
bound. `StackCompile.simulate` also includes its own input initializer;
the selected ML-S route instead loads `StackEncoding.homeTape` explicitly
and uses the controller theorem. Given a finite terminating run, initial
maximum stack length plus its instruction count supplies the room bound.
No polynomial bound is asserted for the UJB evaluator.

The supplied alphabet is blank, bit-zero, bit-one and separator, with
bilateral left/stay/right movement. The two-bit adapter, the complete
ML-S client, its accepted ML-F correspondence and the closed copier/Wang
block encoding are separate ordinary constructions in §§10–13 of the
owning theory volume. The generic supplier does not prove an absent
client, and the executable content port is not a fresh Lean client or
an invocation of NWMG on a four-symbol machine without an alphabet bridge.
