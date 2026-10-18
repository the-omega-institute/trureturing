# Sequential Occupation History

## Abstract

Actual occupation transitions prepare the uniform word state, and every exact finite chain factors its cut matrix through its actual memory.

A is an alphabet; each statement records its finiteness and decidable-equality assumptions. a is a multiset of symbols, t and n are natural numbers, and Word(A,n) is Fin n to A. B(a,t) is the existing Boundary subtype: val(b)<=a and card(val(b))=t. Subtraction of multisets removes occupation counts. M(n,r) counts actual words with occupation r; V(n,r,w) is the existing sectorVector, equal to the complex inverse of sqrt(M(n,r)) on legal words and zero elsewhere.

S(a,t) denotes nextStep, a complex matrix with rows (i,c) in A x B(a,t+1) and columns b in B(a,t). Its entry is sqrt(count(a-val(b),i)/(card(a)-t)) when val(c)=val(b)+{i}, and zero otherwise. The subtraction card(a)-t is in natural numbers, and numerator and denominator are included in the reals before division. The nonnegative real square root is then included in C. Dagger denotes conjugate transpose, and 1 denotes the identity matrix.

**Theorem 1.1 (The first symbol separates a normalized occupation vector).**

$$\forall A \in Type,\; [Fintype\left(A\right)] [DecidableEq\left(A\right)] \forall r \in Multiset\left(A\right),\; \forall n \in \mathbb{N},\; \operatorname{Multiset}.\operatorname{card}\left(r\right) = n + 1 \Rightarrow \left(\forall w \in Fin\left(n + 1\right) \to A,\; \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{OccupancyWordSectors}.\operatorname{sectorVector}\left(n + 1, r, w\right) = \operatorname{if} (w\left(0\right) \in r) \operatorname{then} (\operatorname{Real}.\operatorname{sqrt}\left(\frac{(\operatorname{Multiset}.\operatorname{count}\left(w\left(0\right), r\right):\mathbb{R})}{((n + 1:\mathbb{N}):\mathbb{R})}\right):\mathbb{C}) \cdot \operatorname{D5}.\operatorname{S3}.\operatorname{Quantum}.\operatorname{Entanglement}.\operatorname{OccupancyWordSectors}.\operatorname{sectorVector}\left(n, \operatorname{Multiset}.\operatorname{erase}\left(r, w\left(0\right)\right), \operatorname{Fin}.\operatorname{tail}\left(w\right)\right) \operatorname{else} 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.sector_head` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

A normalized occupation amplitude factors into the square root of the first-symbol frequency and the amplitude for the remaining occupation. The amplitude vanishes when the first symbol is absent.

**Theorem 1.2 (Legal extensions are exactly positive remaining counts).**

$$\forall A \in Type,\; DecidableEq\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; \forall b \in B\left(a, t\right),\; \forall i \in A,\; \left(\exists c \in B\left(a, t + 1\right),\; val\left(c\right) = val\left(b\right) + singleton\left(i\right)\right) \Leftrightarrow count\left(val\left(b\right), i\right) < count\left(a, i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.extension_exists_iff` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The extension is an actual member of the next occupation carrier. This criterion does not need finiteness of the alphabet or an active-step hypothesis.

**Theorem 1.3 (Every active step has identity Gram matrix).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; t < card\left(a\right) \Rightarrow conjTranspose\left(S\left(a, t\right)\right) \cdot S\left(a, t\right) = 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.next_step_gram` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The columns have unit norm and are mutually orthogonal. Different prefixes cannot reach the same next occupation after emitting the same symbol. Summing all remaining symbol counts gives card(a)-t, which is positive on an active step.

**Theorem 1.4 (The step induces the canonical quantum channel).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; t < card\left(a\right) \Rightarrow \left(\exists channel \in QuantumChannel\left(B\left(a, t\right), Prod\left(A, B\left(a, t + 1\right)\right)\right),\; \forall rho \in Matrix\left(B\left(a, t\right), B\left(a, t\right), \mathbb{C}\right),\; toMatrix\left(toCompletelyPositiveMap\left(channel, ofMatrix\left(rho\right)\right)\right) = S\left(a, t\right) \cdot rho \cdot conjTranspose\left(S\left(a, t\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.next_step_quantum_channel` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

QuantumChannel is FiniteStateChannel.QuantumChannel. ofMatrix is CStarMatrix.ofMatrix and toMatrix is its inverse. The singleton Unit Kraus family uses the frozen finite_kraus_quantum_channel theorem; the action holds on every complex input matrix.

F(a,n,t,w,b) denotes contraction. For n=0 it is 1 when val(b)=a and 0 otherwise. For n+1 it is the finite sum over c in B(a,t+1) of S(a,t)((w(0),c),b) times F(a,n,t+1,Fin.tail(w),c). Thus it multiplies and sums the actual step entries and caps the final memory by the total-occupation basis vector. The initial memory b0(a) is initialBoundary, whose multiset value is empty.

**Theorem 1.5 (Every remaining contraction is the normalized suffix state).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; \forall n \in \mathbb{N},\; card\left(a\right) = t + n \Rightarrow \left(\forall w \in Word\left(A, n\right),\; \forall b \in B\left(a, t\right),\; F\left(a, n, t, w, b\right) = V\left(n, a - val\left(b\right), w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.contraction_eq_sector` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The proof follows the unique legal occupation path and uses the actual word-count erasure recurrence for its conditional amplitude. Illegal words give zero. No orthogonality, normalization, or exact-preparation premise is assumed.

**Theorem 1.6 (Sequential contraction prepares the actual uniform history).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall w \in Word\left(A, card\left(a\right)\right),\; F\left(a, card\left(a\right), 0, w, b0\left(a\right)\right) = V\left(card\left(a\right), a, w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.history_sequential_preparation` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

This includes the empty alphabet and zero time. At the final time the only feasible occupation is a. The result is an exact equality at every actual word of the original fixed output length.

**Theorem 1.7 (A cut factorization bounds rank by its bond size).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; \forall s \in \mathbb{N},\; \forall beta \in Type,\; Fintype\left(beta\right) \Rightarrow \left(\forall P \in Matrix\left(Word\left(A, t\right), beta, \mathbb{C}\right),\; \forall Q \in Matrix\left(beta, Word\left(A, s\right), \mathbb{C}\right),\; coefficientMatrix\left(a, t, s\right) = P \cdot Q \Rightarrow rank\left(coefficientMatrix\left(a, t, s\right)\right) \le FintypeCard\left(beta\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.coefficient_rank_le_bond` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

This companion applies Matrix.rank_mul_le_left and rank_le_card_width. Its factorization premise must be established for any proposed sequential representation before using it as a memory lower bound.

FiniteChain(A,beta) is an actual finite linear chain starting in beta. A terminal constructor stores a covector beta to C. A step stores an arbitrary finite next carrier gamma, a transition A to Matrix(beta,gamma,C), and a remaining chain starting in gamma. Each step emits one symbol. length(c) counts steps; cutBond(c,t) is the actual memory after t steps. All carriers may differ; they need not be nonempty or have a common dimension. No isometry or physical normalization is required of a general chain. Function(X,Y) means maps X to Y.

K(c,v,i) denotes FiniteChain.contract on a list v and initial basis index i. For a terminal chain on the empty list it is the terminal covector at i. For a step with transition T and remaining chain r on x::xs it is the sum over j in the actual next carrier of T(x,i,j) K(r,xs,j). Other constructor/list length mismatches give zero. L(c,t,u,i,b) denotes left: at t=0 it is delta(i,b), and for a step chain at cut t+1 on x::xs it sums T(x,i,j) L(r,t,xs,j,b). R(c,t,v,b) denotes right: it drops t step constructors and contracts v from b with the remaining cap. Only cuts t<=length(c) are asserted below. List append is written append; wordAppend denotes Fin.append on the existing Fin-indexed words, and ofFn lists their entries.

**Theorem 1.8 (Actual contraction splits through every cut memory).**

$$\forall A \in Type,\; \forall beta \in Type,\; Fintype\left(beta\right) \Rightarrow \left(\forall c \in FiniteChain\left(A, beta\right),\; \forall t \in \mathbb{N},\; t \le length\left(c\right) \Rightarrow \left(\forall u \in List\left(A\right),\; \forall v \in List\left(A\right),\; length\left(u\right) = t \Rightarrow \left(\forall i \in beta,\; K\left(c, append\left(u, v\right), i\right) = \sum_{b:cutBond\left(c, t\right)}{L\left(c, t, u, i, b\right) \cdot R\left(c, t, v, b\right)}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.chain_contract_append` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

Induction on the cut, generalized over the starting carrier and prefix, derives this identity from the actual recursive sums. The successor step exchanges the next-memory and cut-memory sums; the zero cut uses the delta identity. The suffix list is unrestricted, so incompatible lengths are also handled.

amp(c,initial,w) denotes amplitude, the sum of initial(i) K(c,ofFn(w),i) over i. P(c,initial,t) denotes prefixMatrix with entry P(u,b) equal to the sum of initial(i) L(c,t,ofFn(u),i,b). Q(c,t,s) denotes suffixMatrix with entry Q(b,v)=R(c,t,ofFn(v),b). Their row and column types are respectively Word(A,t) x cutBond(c,t) and cutBond(c,t) x Word(A,s). entry(M,u,v) is M(u,v).

**Theorem 1.9 (The word amplitude is the product entry).**

$$\forall A \in Type,\; \forall beta \in Type,\; Fintype\left(beta\right) \Rightarrow \left(\forall c \in FiniteChain\left(A, beta\right),\; \forall initial \in Function\left(beta, \mathbb{C}\right),\; \forall t \in \mathbb{N},\; \forall s \in \mathbb{N},\; t \le length\left(c\right) \Rightarrow \left(\forall u \in Word\left(A, t\right),\; \forall v \in Word\left(A, s\right),\; amp\left(c, initial, wordAppend\left(u, v\right)\right) = entry\left(P\left(c, initial, t\right) \cdot Q\left(c, t, s\right), u, v\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.chain_amplitude_append` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

List.ofFn_fin_append connects the existing actual word concatenation to the proved contraction split. Summing the initial vector and exchanging the two finite sums gives exactly matrix multiplication at every pair of words.

**Theorem 1.10 (Every exact chain factors the existing coefficient matrix).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall beta \in Type,\; Fintype\left(beta\right) \Rightarrow \left(\forall c \in FiniteChain\left(A, beta\right),\; \forall initial \in Function\left(beta, \mathbb{C}\right),\; \forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; \forall s \in \mathbb{N},\; length\left(c\right) = t + s \Rightarrow \left(\left(\forall w \in Word\left(A, t + s\right),\; amp\left(c, initial, w\right) = V\left(t + s, a, w\right)\right) \Rightarrow coefficientMatrix\left(a, t, s\right) = P\left(c, initial, t\right) \cdot Q\left(c, t, s\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.sequential_coefficient_factorization` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

Exactness quantifies over every full word and equates the computed amplitude with sectorVector. It assumes no cut factorization. The existing definition of coefficientMatrix on Fin.append and the proved product entries establish the matrix equality. The chain has the explicit fixed length t+s.

**Theorem 1.11 (Every exact chain has a sufficiently large actual cut bond).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall beta \in Type,\; Fintype\left(beta\right) \Rightarrow \left(\forall c \in FiniteChain\left(A, beta\right),\; \forall initial \in Function\left(beta, \mathbb{C}\right),\; \forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; \forall s \in \mathbb{N},\; length\left(c\right) = t + s \Rightarrow \left(\left(\forall w \in Word\left(A, t + s\right),\; amp\left(c, initial, w\right) = V\left(t + s, a, w\right)\right) \Rightarrow rank\left(coefficientMatrix\left(a, t, s\right)\right) \le FintypeCard\left(cutBond\left(c, t\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.sequential_rank_necessity` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The preceding constructed factorization supplies the equality premise of coefficient_rank_le_bond. The bound uses the cardinality of this chain's actual cut carrier, for every finite model satisfying the stated output equality.

**Theorem 1.12 (The necessary memory is at least the feasible occupation count).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall beta \in Type,\; Fintype\left(beta\right) \Rightarrow \left(\forall c \in FiniteChain\left(A, beta\right),\; \forall initial \in Function\left(beta, \mathbb{C}\right),\; \forall a \in Multiset\left(A\right),\; \forall t \in \mathbb{N},\; \forall s \in \mathbb{N},\; card\left(a\right) = t + s \Rightarrow \left(length\left(c\right) = t + s \Rightarrow \left(\left(\forall w \in Word\left(A, t + s\right),\; amp\left(c, initial, w\right) = V\left(t + s, a, w\right)\right) \Rightarrow card\left(boundaries\left(a, t\right)\right) \le FintypeCard\left(cutBond\left(c, t\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.sequential_memory_necessity` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The explicit occupation-cardinality condition permits coefficient_rank to identify the coefficient rank with the number of feasible boundaries. No rank equality or factorization is requested from the proposed model.

O(a,n,t) denotes occupationChain. For O(a,n+1,t), the transition is T(i,b,c)=S(a,t)((i,c),b) and the remaining chain is O(a,n,t+1). Its zero-step terminal covector is delta(val(b),a). I0(a) denotes occupationInitial, the delta at initialBoundary(a). Thus this is the already proved occupation construction in the general finite-chain carrier.

**Theorem 1.13 (The occupation chain has its declared number of steps).**

$$\forall A \in Type,\; DecidableEq\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall n \in \mathbb{N},\; \forall t \in \mathbb{N},\; length\left(O\left(a, n, t\right)\right) = n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.occupation_chain_length` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

This structural identity holds for all n and t; the alphabet need only have decidable equality.

**Theorem 1.14 (Every occupation chain cut has the actual boundary size).**

$$\forall A \in Type,\; DecidableEq\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall n \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall k \in \mathbb{N},\; k \le n \Rightarrow FintypeCard\left(cutBond\left(O\left(a, n, t\right), k\right)\right) = card\left(boundaries\left(a, t + k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.occupation_chain_bond_card` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

Induction selects the stored carrier at the requested legal cut. This counts the actual dependent memory type, including empty carriers when the occupation constraints have no solution.

**Theorem 1.15 (The generic chain computes the existing occupation contraction).**

$$\forall A \in Type,\; DecidableEq\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall n \in \mathbb{N},\; \forall t \in \mathbb{N},\; \forall w \in Word\left(A, n\right),\; \forall b \in B\left(a, t\right),\; K\left(O\left(a, n, t\right), ofFn\left(w\right), b\right) = F\left(a, n, t, w, b\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.occupation_chain_contract` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The recursive finite sums agree at every word and every starting occupation. No cardinality or active-step hypothesis is needed for this identification.

**Theorem 1.16 (The actual occupation chain is an exact model).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall w \in Word\left(A, card\left(a\right)\right),\; amp\left(O\left(a, card\left(a\right), 0\right), I0\left(a\right), w\right) = V\left(card\left(a\right), a, w\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.occupation_chain_preparation` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The initial delta selects the existing history_sequential_preparation theorem. The exactness premise of the universal chain theorems is therefore realized by the proved occupation construction, including length zero.

**Definition 1.17 (Maximum of the actual chain bonds).**

$$\forall A \in Type,\; \forall beta \in Type,\; Fintype\left(beta\right) \Rightarrow \left(\forall c \in FiniteChain\left(A, beta\right),\; maximumBond\left(c\right) = FinsetSup\left(range\left(length\left(c\right) + 1\right), t \mapsto FintypeCard\left(cutBond\left(c, t\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.maximumBond` (`✓ std3`).

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

FinsetSup(range(length(c)+1),f) includes every cut from zero through length(c). In particular a zero-step chain still has its actual initial/terminal bond.

**Theorem 1.18 (Every exact chain needs the target maximum bond).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall beta \in Type,\; Fintype\left(beta\right) \Rightarrow \left(\forall c \in FiniteChain\left(A, beta\right),\; \forall initial \in Function\left(beta, \mathbb{C}\right),\; \forall a \in Multiset\left(A\right),\; length\left(c\right) = card\left(a\right) \Rightarrow \left(\left(\forall w \in Word\left(A, card\left(a\right)\right),\; amp\left(c, initial, w\right) = V\left(card\left(a\right), a, w\right)\right) \Rightarrow boundaryMaximum\left(a\right) \le maximumBond\left(c\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.maximum_bond_necessity` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The starting finite type may lie in any universe, independent of the alphabet. Every legal cut uses sequential_memory_necessity with remaining length card(a)-t. No factorization, isometry, normalized cap, or attaining chain is assumed.

**Theorem 1.19 (The occupation chain attains the target maximum).**

$$\forall A \in Type,\; DecidableEq\left(A\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; maximumBond\left(O\left(a, card\left(a\right), 0\right)\right) = boundaryMaximum\left(a\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.occupation_chain_maximum_bond` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

occupation_chain_bond_card identifies every actual carrier in the same finite supremum, and occupation_chain_length identifies the endpoint.

**Definition 1.20 (Achievable maximum bonds include actual exact preparations).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; \forall m \in \mathbb{N},\; m \in achievableMaximumBonds\left(a\right) \Leftrightarrow \left(\exists beta \in Type,\; \exists finite \in Fintype\left(beta\right),\; \exists c \in FiniteChain\left(A, beta\right),\; \exists initial \in Function\left(beta, \mathbb{C}\right),\; length\left(c\right) = card\left(a\right) \land \left(\left(\forall w \in Word\left(A, card\left(a\right)\right),\; amp\left(c, initial, w\right) = V\left(card\left(a\right), a, w\right)\right) \land maximumBond\left(c\right) = m\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.achievableMaximumBonds` (`✓ std3`).

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

The existential beta ranges over types in the alphabet's universe. Its finite instance, chain, initial vector, length equality, pointwise exact output, and actual maximumBond value are all part of the witness. The universal necessity theorem also applies to carriers in any other universe.

**Theorem 1.21 (The least achievable maximum is attained).**

$$\forall A \in Type,\; \left(Fintype\left(A\right) \land DecidableEq\left(A\right)\right) \Rightarrow \left(\forall a \in Multiset\left(A\right),\; IsLeast\left(achievableMaximumBonds\left(a\right), boundaryMaximum\left(a\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.minimum_maximum_bond_characterization` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

IsLeast includes membership and a lower bound for every member. Membership is witnessed here by beta=B(a,0), occupationChain(a,card(a),0), and the actual occupationInitial delta. occupation_chain_preparation supplies the exact output, and the previous theorem supplies its maximum. This holds also for empty occupation and the empty alphabet.

**Theorem 1.22 (The concrete attained minimum is twelve).**

$$IsLeast\left(achievableMaximumBonds\left(ast\right), 12\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.history_5040_minimum_maximum_bond` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

ast is the existing occupation5040 on Option(Fin(3)), with actual counts (4;2,1,1). This specializes the general attained theorem using the transported landed maximum.

**Theorem 1.23 (An actual eight-step preparation attains twelve).**

$$length\left(O\left(ast, card\left(ast\right), 0\right)\right) = 8 \land \left(maximumBond\left(O\left(ast, card\left(ast\right), 0\right)\right) = 12 \land \left(\forall w \in Word\left(Option\left(Fin\left(3\right)\right), card\left(ast\right)\right),\; amp\left(O\left(ast, card\left(ast\right), 0\right), I0\left(ast\right), w\right) = V\left(card\left(ast\right), ast, w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.history_5040_occupation_chain_attainment` (`✓ std3`). ∎

*Citation.* David Raveh and Rafael I. Nepomechie (2024). *Dicke states as matrix product states*. DOI: [10.1103/PhysRevA.110.052438](https://doi.org/10.1103/PhysRevA.110.052438).

*Commentary.*

ConcreteChain is O(ast,card(ast),0). The actual initial carrier is Boundary(ast,0), with its empty-occupation delta, and the terminal cap selects ast in the full boundary carrier. Both have one element. Every full word has exactly the target amplitude, and card(ast)=8.

The necessity theorem concerns arbitrary algebraic FiniteChains with complex caps. The attaining occupation construction additionally has the active-step identity Gram matrices and canonical quantum channels proved above. This establishes the source's finite MPS and variable-bond sequential-isometry scope. A unitary implementation on one fixed twelve-dimensional physical register would also need compatible embeddings and unitary extensions; those are not constructed. No time-homogeneous prediction-memory claim, or identification with dimension sixteen from the different prediction model, follows. These are known Dicke-state constructions from Raveh and Nepomechie, with no novelty claim.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.achievableMaximumBonds`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.chain_amplitude_append`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.chain_contract_append`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.coefficient_rank_le_bond`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.contraction_eq_sector`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.extension_exists_iff`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.history_5040_minimum_maximum_bond`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.history_5040_occupation_chain_attainment`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.history_sequential_preparation`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.maximumBond`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.maximum_bond_necessity`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.minimum_maximum_bond_characterization`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.next_step_gram`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.next_step_quantum_channel`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.occupation_chain_bond_card`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.occupation_chain_contract`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.occupation_chain_length`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.occupation_chain_maximum_bond`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.occupation_chain_preparation`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.sector_head`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.sequential_coefficient_factorization`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.sequential_memory_necessity`
- Truth anchor: `D5/S3/Quantum/Entanglement/SequentialOccupationHistory.sequential_rank_necessity`
- Dependency: [D5/S3/Quantum/Entanglement/CoherentHistorySchmidt](CoherentHistorySchmidt.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
