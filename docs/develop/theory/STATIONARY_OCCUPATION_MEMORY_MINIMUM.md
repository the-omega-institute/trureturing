# Exact stationary occupation-memory minimum: 56

Reference input, not the repository's Lean truth source. All claims below remain open for canonical formalization; the ordinary audit is not kernel admission. The final paragraph's historical formalization status describes the retained source's recording time.

Author kind: AI. Source author: NyxID oracle, reported model GPT-6 Astra; task 2260c8d2-e53d-40b0-8fe6-1401a8bda816, conversation conv_f0cb5286379a9c82, completed 2026-09-07T19:41:29.771Z. Source conversation: https://chatgpt.com/c/6a9f10ad-d51c-83ec-af58-b2f5a4f72166. Model identity is task metadata, not independent backend verification. The retained corrected note's editor model is unknown; no human mathematical coauthorship is asserted. This intake was normalized by Codex on 2026-09-08 from stationary-minimum56.md, SHA-256 654a826f9fa4b2808487380cb33345f6e42839aff5adcb64699c63aec3b39270. Only headings and this provenance paragraph are added; claim sentences are retained. No novelty claim is made.

Status (2026-09-08): ordinary mathematical proof, independently reviewed by
CLI flight boundary5040-a-nullity-audit-20260908, attempt1, verdict approve,
carrier exit0 at2026-09-07T20:03:37Z. The reviewer derived the required notation
corrections and found no remaining mathematical gap. This is not Lean/kernel
verification, full sshx consensus, or a novelty claim.

## theorem 1: Exact stationary occupation-memory minimum

For a finite nonempty alphabet and capacities a_i>=0, the exact minimum is

    D_min = product_i(a_i+1) - max_i a_i.

For a=(4,2,1,1), this gives60-4=56. It replaces the earlier ordinary interval
20<=D_min<=56 for this specific model. Time-dependent controls still belong
to the separate minimum12 problem.

## Physical contract

One finite complex memory H, one unit initial vector, and one fixed isometry
V:H -> C^k tensor H are used for |a| emissions. The output is exactly the
uniform equal-phase superposition of all words of occupation a, tensor one
common unit final memory. No postselection, uncounted memory, or varying
external control is allowed. The final memory need not be a prescribed reset.
For5040, there are840 words and each has amplitude1/sqrt(840).

## proposition 2: Lower bound

Set R={r:0<=r<=a} and M(r)=|r|!/product_i(r_i!). Actual legal prefixes define
unit residual memories phi_r: apply the remaining isometric evolution to a
prefix memory and use injectivity to see that its normalization depends only
on r, including phase. With phi_0=f and z_d=<phi_d,f>, their Gram entries are

    G_rs = sqrt(M(s) M(r-s)/M(r)) z_(r-s)  if s<=r,

zero for incomparable indices, with conjugate reverse entries and z_0=1.
Thus G is PSD and rank G<=dim H. This necessity was also independently audited
in the earlier Gram characterization.

Let D_rr=sqrt(M(r)) and B=DGD. On nonzero r,s,

    B_rs = sum_i B_(r-e_i,s-e_i),

omitting zero coordinates. Define T_i e_r=e_(r-e_i) when r_i>0 and0 otherwise.
For u_0=0 the recurrence gives the sesquilinear identity

    u^* B u = sum_i (T_i u)^* B(T_i u).

PSD therefore implies T_i u in ker B whenever u in ker B and u_0=0.
The invertible coefficient map J(e_r)=x^r/product_i(r_i!) intertwines T_i with
partial_i. Hence L=J(ker B) contains no nonzero constant and has conditional
derivative closure: p in L and p(0)=0 imply partial_i p in L.

Polynomial rigidity: if dim L>=2, then L is contained in C[ell] for one
nonzero homogeneous linear form ell. To prove this, choose a nonzero p in L
of minimum degree m. Its value at0 is nonzero, since otherwise all partials
would have smaller degree in L and vanish. Choose nonzero q of minimum degree
n in the kernel of evaluation at0. Then n>m, and every element of L below
degree n is a multiple of p. Thus partial_i q=c_i p, not all c_i zero.
Commuting mixed derivatives shows p,q depend only on ell=sum_i c_i x_i.

If h outside C[ell] exists in L, take its minimum degree and subtract
h(0)p/p(0). This cannot increase degree and leaves h outside C[ell] with zero
constant term. All its partials lie in L intersect C[ell]. For a tangent
direction v with ell(v)=0 and u with ell(u)=1, commutation gives
D_u D_v h=D_v D_u h=0. Thus D_v h is constant; membership in L makes it zero.
All tangent derivatives vanish, contradicting h outside C[ell]. This uses
complex directions and characteristic zero, with no positivity of c_i assumed.

If ell has nonzero coefficient c_i, a degree-n polynomial F(ell) has a nonzero
x_i^n coefficient. Rectangular support forces n<=b=min_(c_i!=0)a_i. Excluding
the constant direction bounds dim L<=b<=max_i a_i. Nullity0/1 satisfies the
same bound for a nontrivial box; the all-zero box has G=[1]. Hence

    rank G >= |R|-max_i a_i.

## proposition 3: Attainment

Choose a head coordinate of maximum capacity A. Set z_(h e_head)=1 for
1<=h<=A and every other nonzero z_d=0. B splits into blocks by the remaining
tail occupation b. Each block has entries m_min(j,k), where m_j=M(j,b), and
the exact factorization

    B_b = L diag(m_0,m_1-m_0,...,m_A-m_(A-1)) L^T,

where L has ones on and below its diagonal. The zero-tail block has rank1;
each other block has full rank A+1 because m_j/m_(j-1)=(j+|b|)/j>1.
Thus total rank is product_i(a_i+1)-A, or1+11*5=56 in the concrete case.

Its Gram vectors define the same fixed isometry through
V phi_r=sum_i sqrt(r_i/|r|)|i> tensor phi_(r-e_i). The Gram recurrence preserves
all dependencies. In this construction phi_0=phi_e_head, so the nonterminal
vectors already span H when A>0. Iteration telescopes to the required word
amplitudes and common final vector. The all-zero occupation uses memory C.
The separately audited last-tail padding construction gives the same bound.

## Evidence and corrections

Producer: stationary-minimality-oracle-result.json, via NyxID task
2260c8d2-e53d-40b0-8fe6-1401a8bda816. Independent review and exact checks:
stationary-minimum56-audit-result.json. The reviewer used exact integer and
Gaussian-integer probes, including all65536 words and3136 isometry entries.
The universal lower bound rests on the ordinary proof, not those finite probes.

The producer's unannotated uBu expression omitted conjugate transposes; the
correct sesquilinear formula is given above. Its optional Cayley formula also
omitted adjoints: with A=I+P and C=P A^(-1), the correct identity is
G=A(I-CC^*)A^*. That formula is not used by the lower bound. The printed
arithmetic1+115=56 was corrected to1+11*5=56. The original envelope is retained
unchanged so these defects are not erased.

The dispatcher retained and reran the independent exact checker with exit0:
stationary-minimum56-exact-check.py, SHA256
ac1bb764eb1ad30615aeca5af58114ddc7f916fa74457ad9146a202ea1d849c3.
Its JSON output matches the reviewer's retained report, SHA256
cffb081ab03cc8ca41de7cfaa0005fa169e5b0febfc7ae86a10554c57e3ad294.
The existing sub56 GPU runs now provide numerical approximation research.
They cannot establish an exact sub56 construction in this model, and their
best fidelities are not proved global optima. A separately audited exact55
machine attains approximate fidelity279/280; see
stationary-approximation55-audit-proof.md. Formalization remains future work
separate from the ongoing time-dependent history atom.
