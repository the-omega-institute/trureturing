---
bibkey: wheeler1999informationphysics
authors: John Archibald Wheeler
year: 1999
title: "Information, Physics, Quantum: The Search for Links"
doi: 10.1201/9780429500459-19
url: https://cqi.inf.usi.ch/qic/wheeler.pdf
claim: "Section 19.2 presents 'it from bit' as a working hypothesis and describes apparatus-elicited answers to yes-or-no physical questions."
strata_touched:
  - D5/S3/QuantumChannels/FibonacciBathObservation
  - D5/S3/Quantum/Decoherence/FourLevelBathObserver
  - D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier
  - D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget
license: citation-only
triage: anchor
---

# Wheeler on apparatus-elicited answers

## Verified locator

John Archibald Wheeler, *Information, Physics, Quantum: The Search for Links*,
in Anthony J. G. Hey (ed.), *Feynman and Computation: Exploring the Limits of
Computers*, first edition (Perseus Books, 1999), Chapter 19, pp. 309–336.
Section 19.2, “It from Bit” as Guide in Search for Link Connecting Physics,
Quantum and Information, spans printed pp. 310–313 (PDF pages 2–3). It
introduces the working hypothesis on p. 310 and uses a photodetector's
yes-or-no count as its first illustration on p. 311. The opening-page
footnote identifies the original as the 1989 Tokyo proceedings of the Third
International Symposium on Foundations of Quantum Mechanics, pp. 354–368.
The publisher's 2018 electronic edition gives the same chapter pagination.
[Chapter scan](https://cqi.inf.usi.ch/qic/wheeler.pdf) ·
[Section 19.2](https://cqi.inf.usi.ch/qic/wheeler.pdf#page=2) ·
[Publisher's chapter record](https://doi.org/10.1201/9780429500459-19)

## Operational scope

Wheeler's discussion provides historical context for the question about the
terminal qutrit, “Is it in its ground state?” The repository derives the
joint law of that binary answer and the outgoing bath basis readout from
an independent Gibbs preparation and an explicit energy-conserving
permutation. Preserving the conditional law of the answer requires a record
with at least three positive-probability outcomes. The information criterion
uses finite Shannon entropy and the repository's Markov equality theorem.
[Shannon's finite entropy](../Estimation/shannon1948communication.md) ·
[The finite thermal-operation model](../Resource/vomende2022thermaloperations.md)

## Yes-or-no readout of a purified bath record

Section 19.2 motivates an apparatus question for each prescribed qutrit
basis label j. The question “Was the input label j?” has the record
projector for j as its yes effect and the complementary effect as its no
effect. In the repository's fixed-bath model, the Born probability of yes
on basis input i is one if i = j and zero otherwise. This follows from
orthogonality of the records obtained by applying the phase unitary on the
system and bath and tracing out the system. The binary question is an
operational use of Wheeler's historical framing.

The preparation supplies a coherent purification of the prescribed Gibbs
law on the bath B and a spectator reference R, initially independent of
the qutrit. Each conditional record has the same Gibbs weights on either
factor, and the law of the joint coordinate readout is p(b) on (b,b).
Equal-modulus amplitudes in those correlated coordinates connect the
construction to fixed-modulus masking. Energy conservation is imposed
on the system–bath interaction in the finite thermal-operation model.
[Ding and Hu on masking](../HilbertOperators/dinghu2020masking.md) ·
[vom Ende on finite thermal operations](../Resource/vomende2022thermaloperations.md)

Readout requires access to both B and R, with phase-sensitive
measurements. The two observers can measure separately. Measure R in the
four-point Fourier basis and send its outcome k to the bath observer,
who uses the corresponding phase-adjusted projectors. Each k occurs
with probability 1/4, and the conditional bath readout gives the input
label with certainty. Testing that result against j yields the same
yes-or-no answer.

## Information of the measured label

The same apparatus question can be asked after an arbitrary qutrit
density evolves with the bath and its spectator reference. Measuring the
qutrit in its coordinate basis gives a classical label X with Born law
aᵢ = ρᵢᵢ. Each local record density is independent of this label.
The phase-sensitive measurement on BR identifies the label exactly,
as does the one-way Fourier protocol above. The repository computes
I(X:B) = I(X:R) = 0 and I(X:BR) = H(a) for the corresponding
classical–quantum record state. Section 19.2 supplies historical context
for the yes-or-no question about X.
[Section 19.2](https://cqi.inf.usi.ch/qic/wheeler.pdf#page=2)
