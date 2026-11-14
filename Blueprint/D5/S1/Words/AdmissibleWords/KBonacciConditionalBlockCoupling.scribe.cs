using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class KBonacciConditionalBlockCouplingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional next-bit couplings and zero screening for forbidden-run words.",
        H("Full exterior and sampled prefix"),
        Blocks(
            Paragraph(Text(
                "Write W(n) for Fin n to Bool and A(k,n,w) for the original "
                + "DBonacciAdmissible scanner. C(k,n,F,x) is the finite set of "
                + "legal full words w satisfying w(i)=x(i) for every i in F. "
                + "The fixed set F can contain the entire exterior of a contiguous "
                + "block and any sampled prefix. Both ends remain fixed. "
                + "L(F,x,h) is completionLaw, the uniform PMF on this fiber, "
                + "where h states that the fiber is nonempty.")),
            Paragraph(Text(
                "For PMFs p and q on Bool, J(p,q) denotes bitCoupling. Set "
                + "a=p(false) and b=q(false). If a is at most b, its masses at "
                + "(false,false), (false,true), (true,false), (true,true) are "
                + "a, zero, b-a, one-b. Otherwise exchange the two coordinates "
                + "of the same construction with a and b interchanged. "
                + "This is the finite shared-threshold next-bit law.")),
            Describe.Lean(
                DescribeId.Create("kbonacci-conditional-step-coupling"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.conditional_step_coupling"),
                H("Exact conditional-bit marginals and a common zero"),
                StatementSource.FromAuthor(Disp(StepFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The laws p and q in the formula are the pushforwards of "
                    + "L(F,x,h) and L(F,y,g) by evaluation at i. Deleting the "
                    + "one at an unfixed coordinate gives an injection from "
                    + "one-completions into zero-completions while preserving "
                    + "all other bits. Thus each actual conditional zero mass "
                    + "is at least one half. The displayed joint law has exact "
                    + "marginals and common-zero mass equal to their minimum. "
                    + "No lower bound on word length relative to k is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kbonacci-zero-screening"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.zero_screening"),
                H("A common zero screens the earlier prefix"),
                StatementSource.FromAuthor(Disp(ScreenFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Define S(x,z,t)(i) to be x(i) when i is at most z and "
                    + "t(i) otherwise. A forbidden window is either contained "
                    + "in the legal prefix, contained in the shared later "
                    + "assignment, or crosses z. The last possibility contains "
                    + "the specified zero. Hence replacing the legal prefix "
                    + "preserves the entire suffix-completion condition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kbonacci-reset-law-transport"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.reset_law_transport"),
                H("Uniform suffix laws agree after reset"),
                StatementSource.FromAuthor(Disp(ResetFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "All coordinates through z are fixed. The two legal exterior "
                    + "words have a zero at z and agree at every fixed coordinate "
                    + "strictly after z. Prefix replacement S(y,z,w) is a bijection "
                    + "between their full completion fibers, with inverse S(x,z,w). "
                    + "It therefore transports the uniform conditional laws exactly. "
                    + "R(F,x,y,z) samples w from L(F,x) and returns the pair "
                    + "(w,S(y,z,w)); its two marginal pushforwards are exactly "
                    + "L(F,x) and L(F,y). Every coordinate strictly after z is preserved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kbonacci-prefix-coupling-marginals"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.prefix_coupling_marginals"),
                H("Stopped conditional recursion has exact full-word marginals"),
                StatementSource.FromAuthor(Disp(PrefixFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "P(s,F,x,y,h,g) denotes prefixCoupling. At each listed site, "
                    + "the finite next-bit joint law is bound to the recursively refined "
                    + "completion law. Its supported bit pairs have nonempty refined "
                    + "fibers. The marginal weight of a bit times its refined uniform "
                    + "completion mass is the original mass on that bit fiber; summing "
                    + "over Bool proves exact disintegration. If the fixed histories "
                    + "already contain a common screening zero and agree at all farther "
                    + "fixed sites, the recursion instead uses resetCoupling, with legal "
                    + "representatives chosen from the actual nonempty fibers. Uniform "
                    + "prefix transport proves both marginals in this stopped branch."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kbonacci-right-scan-hamming"),
                DeclarationHandle.Create(
                    "D5/S1/Words/AdmissibleWords/KBonacciConditionalBlockCoupling.right_scan_hamming"),
                H("Expected internal Hamming cost for an increasing scan"),
                StatementSource.FromAuthor(Disp(CostFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "ExpectedHamming(J,s) is the sum over full-word pairs w of J(w)H(s,w). "
                    + "Before(s,i,j) means that i occurs strictly before j in the list s. "
                    + "H(s,w) denotes scanHamming: the sum of the zero-one disagreement "
                    + "indicators at the listed sites. The list is strictly increasing "
                    + "and lists the entire complement of F without repetitions. The "
                    + "fixed histories agree at every fixed site farther right than any "
                    + "scanned site. A supported common-zero branch has zero remaining "
                    + "cost, by screening and the reset law. In every other branch the "
                    + "current indicator is at most one, and the recursive expected "
                    + "remaining cost is at most one. Those branches have total mass "
                    + "at most one half, derived from conditional_step_coupling. "
                    + "Their weighted cost is therefore at most one. This estimate "
                    + "uses the same full-word joint law as the marginal theorem. "
                    + "The theorem covers short words and arbitrary nonempty completion "
                    + "fibers; it does not assert reflection, the geometric survival "
                    + "tail, or the final two-orientation contiguous-block assembly."))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(
                H("Application: actual legal-state refresh, projection and complex energy"),
                Blocks(
                    Paragraph(Text(
                        "Fix integers k >= 2 and n >= 0. The state set S is the actual finite subtype "
                        + "DBonacciName k n: its elements x are full words x.val : Fin n to Bool with proof of "
                        + "DBonacciAdmissible k n x.val. Thus S consists of the legal words with no k consecutive "
                        + "true bits, with open boundaries. In the book's Chapter 39 example on a uniform parent "
                        + "gap, the parameter correspondence is K=k, N=n and the one-based book site j=i.val+1 for "
                        + "i : Fin n. The book's legal-word set W_N corresponds to S, whereas W(n) above denotes "
                        + "all Boolean words, including illegal ones. Every sum over x or y below is over S unless "
                        + "a fiber is specified.")),
                    Paragraph(Text(
                        "Put Z=card(S), pi(x)=1/Z, and pi[h]=(1/Z) sum_x h(x). The all-zero word is legal, "
                        + "including the unique empty word at n=0, so Z>0. The canonical Names suppliers "
                        + "DBonacciName, DBonacciAdmissible and dbonacci_name_card identify Z with dbonacci k "
                        + "(n+2); Values.dbonacci_level_pos supplies positivity for positive order. The uniformPmf "
                        + "supplier in DBonacci.TerminalSampling realizes pi on this actual nonempty subtype. The "
                        + "normalization is the number of legal states, not the number 2^n of unconstrained words.")),
                    Paragraph(Text(
                        "Let B be any finite subset of Fin n and take B-complement in the whole set Fin n. No "
                        + "interval or connectedness assumption is imposed. Define ext_B(x)=x.val restricted to "
                        + "B-complement and A_B(x)={y in S : ext_B(y)=ext_B(x)}. Write m_B(x)=card(A_B(x)). The "
                        + "state x belongs to its own fiber, hence m_B(x)>0. Forgetting the legality proof is a "
                        + "bijection from A_B(x) to the original C(k,n,B-complement,x.val), so these two finite "
                        + "sets have the same cardinality. Every exterior coordinate, on all sides of B, is fixed.")),
                    Paragraph(Text(
                        "The actual full-state refresh law mu_B(x) is the original "
                        + "completionLaw(B-complement,x.val,h_x) pushed to S, where h_x is completion_nonempty "
                        + "applied to x.property. More explicitly, sample a supported completion w from "
                        + "L(B-complement,x.val,h_x) and set legalWord(w) to the subtype element with value w and "
                        + "the legality proof contained in its completion membership. This conversion changes no "
                        + "bit. Equivalently, first sample the uniform PMF on the completion subtype and map this "
                        + "supported legalWord conversion. If a total map on all ambient Boolean words is used, it "
                        + "can return x off the legal support; those inputs have zero mass, so this extension has "
                        + "no effect on mu_B(x).")),
                    Paragraph(Text(
                        "Forgetting the subtype proof after this pushforward gives exactly the original "
                        + "completionLaw again. Its pushforward by restrictBlock B is the canonical "
                        + "conditionalBlockLaw B x.val x.property from KBonacciIntervalBlockCoupling. Conversely, a"
                        + " block assignment b in that law's support has an original legal completion preimage. "
                        + "Restoring b on B and x.val on every site in B-complement recovers that completion, hence"
                        + " a legal state, and pushes the block law back to mu_B(x). Restriction and restoration "
                        + "are inverse on this support because the entire exterior is fixed. An arbitrary "
                        + "unsupported assignment need not restore to a legal word.")),
                    Paragraph(Text(
                        "The canonical completionLaw_apply formula therefore gives mu_B(x)(y)=1/m_B(x) for y in "
                        + "A_B(x) and zero otherwise. Define its real transition mass and its action on any complex"
                        + " function f:S to C by T_B(x,y)=indicator(y in A_B(x))/m_B(x) and (E_B f)(x)=sum_y "
                        + "T_B(x,y)f(y). Here T_B(x,y)=(mu_B(x)(y)).toReal is the real mass at y; real weights are "
                        + "embedded in C when multiplying f(y). This identifies the matrix with the original "
                        + "legal-state law, rather than assuming a freely chosen stochastic matrix.")),
                    Paragraph(Text(
                        "The actual exterior law is q_B=(ext_B)_* pi. For any realizable exterior eta, let "
                        + "C_eta={x in S : ext_B(x)=eta} and m_eta=card(C_eta). Then q_B(eta)=m_eta/Z. In "
                        + "particular q_B(ext_B(x))=m_B(x)/Z. Impossible exteriors have q_B mass zero. For y in "
                        + "C_eta, conditional probability under pi is (1/Z)/(m_eta/Z)=1/m_eta; conditioning on "
                        + "ext_B(x) consequently gives precisely mu_B(x). Thus E_B is conditional averaging with "
                        + "respect to the full exterior, with no assumption of independent exterior bits.")),
                    Paragraph(Text(
                        "Equality of exterior data partitions S into disjoint nonempty fibers. If y is in A_B(x),"
                        + " then A_B(y)=A_B(x) and m_B(y)=m_B(x); otherwise both directed masses T_B(x,y) and "
                        + "T_B(y,x) vanish. This proves T_B(x,y)>=0 and T_B(x,y)=T_B(y,x). The equality of "
                        + "completion laws on equal fixed data is also exactly the content of the original "
                        + "completionLaw_congr. Each row has m_B(x) entries equal to 1/m_B(x), so sum_y T_B(x,y)=1."
                        + " Symmetry then gives sum_x T_B(x,y)=1. It follows that sum_x pi(x)T_B(x,y)=pi(y); the "
                        + "other marginal of pi(x)T_B(x,y) is pi(x). Uniform stationarity and reversibility have "
                        + "thus been derived from actual fibers.")),
                    Paragraph(Text(
                        "Use the conjugate-first uniform pairing <f,g>_pi=(1/Z) sum_x conj(f(x))g(x) and squared "
                        + "norm ||f||_pi^2=(1/Z) sum_x |f(x)|^2, for arbitrary complex f,g. Throughout, |z|^2 is "
                        + "the squared complex modulus conj(z)z, a nonnegative real number, not the complex square "
                        + "z^2. Let Id denote the identity operator on these functions. All sums are finite, so no "
                        + "limiting or integrability assumption is needed.")),
                    Paragraph(Text(
                        "Let C range once over the distinct nonempty exterior fibers, and put fbar_C=(1/card(C)) "
                        + "sum_{x in C} f(x). Then E_B f is fbar_C throughout C. A second fiber average changes "
                        + "nothing, proving E_B^2=E_B. Moreover E_B f=f if and only if f is constant on every "
                        + "actual exterior fiber: the forward direction follows from equality of their means and "
                        + "the reverse direction from averaging a constant. This identifies the fixed functions and"
                        + " the range of E_B.")),
                    Paragraph(Text(
                        "Grouping the finite sums by these fibers gives <f,E_B g>_pi=(1/Z) sum_C card(C) "
                        + "conj(fbar_C)gbar_C=<E_B f,g>_pi. In particular <f,E_B f>_pi=(1/Z) sum_C "
                        + "card(C)|fbar_C|^2=||E_B f||_pi^2>=0, with this real number embedded in the complex "
                        + "numbers when compared with the pairing. Thus E_B is self-adjoint and positive "
                        + "semidefinite. For any fiber-constant h, the sum over C of f-fbar_C is zero, so <h,f-E_B "
                        + "f>_pi=0. Together with idempotence this proves that E_B is the orthogonal projection "
                        + "onto the fiber-constant functions.")),
                    Paragraph(Text(
                        "Put p_x(y)=(mu_B(x)(y)).toReal. Define conditional variance independently from the "
                        + "original law's moments: V_B(f;x)=sum_y p_x(y)|f(y)|^2-|sum_y p_x(y)f(y)|^2. The mean in "
                        + "this definition is E_B f(x) by the preceding law identification. Equivalently the two "
                        + "moments can be taken over the original supported completions w, evaluating "
                        + "f(legalWord(w)); the pushforward preserves both finite sums. This variance is defined by"
                        + " the conditional law, without using a generator energy as its definition.")),
                    Paragraph(Text(
                        "For a real probability row p_y=p_x(y), let a=sum_y p_y f(y). Expand "
                        + "|f(y)-a|^2=|f(y)|^2-2 Re(conj(a)f(y))+|a|^2. Since sum_y p_y=1 and sum_y p_y f(y)=a, the"
                        + " summed cross term is -2|a|^2 and the final term is |a|^2. Hence V_B(f;x)=sum_y "
                        + "T_B(x,y)|f(y)-E_B f(x)|^2>=0. Equal exteriors have identical laws, means and variances, "
                        + "so V_B(f;x) is constant on each fiber. It is also E_B(|f-E_B f|^2)(x), since E_B "
                        + "f(y)=E_B f(x) on the row support.")),
                    Paragraph(Text(
                        "The complex energy identity can be checked inside each fiber. Write m=card(C)>0, "
                        + "S_C=sum_{x in C} f(x) and a=S_C/m. Then sum_{x in C} conj(f(x))(f(x)-a)=sum_{x in "
                        + "C}|f(x)|^2-|S_C|^2/m=sum_{x in C}|f(x)-a|^2=(1/(2m)) sum_{x in C} sum_{y in "
                        + "C}|f(x)-f(y)|^2. Indeed sum_x conj(f(x))a=conj(S_C)S_C/m, which is real. In the centered"
                        + " expansion the two conjugate cross terms total -2|S_C|^2/m and the constant terms total "
                        + "|S_C|^2/m. In the ordered pair expansion the two diagonal-square sums total 2m sum_x "
                        + "|f(x)|^2, while the cross terms total -2|S_C|^2. This finite cancellation supplies every"
                        + " equality, including its exact factor two.")),
                    Paragraph(Text(
                        "Summing the fiber identity and dividing by Z yields the complete chain: "
                        + "Re<f,(Id-E_B)f>_pi = (1/(2Z)) sum_x sum_y T_B(x,y)|f(x)-f(y)|^2 = (1/Z) sum_x sum_y "
                        + "T_B(x,y)|f(y)-E_B f(x)|^2 = (1/Z) sum_x V_B(f;x) = sum_eta q_B(eta)V_B(f;eta) = ||f-E_B "
                        + "f||_pi^2. The pair sum is over ordered pairs of legal states, including the zero "
                        + "diagonal terms. The centered conditional sum has factor 1/Z, whereas the ordered "
                        + "difference sum has factor 1/(2Z).")),
                    Paragraph(Text(
                        "Here V_B(f;eta) is V_B(f;x) for any x with exterior eta, and may be set to zero for an "
                        + "impossible exterior. It is well-defined because equal exteriors have equal laws. "
                        + "Grouping the state average gives (1/Z) sum_x V_B(f;x)=sum_C (card(C)/Z)(1/card(C)) "
                        + "sum_{x in C}|f(x)-fbar_C|^2. This is exactly expectation under the exterior pushforward "
                        + "q_B, whose weights are card(C)/Z; it is not a uniform average over distinct exteriors. "
                        + "Their fiber-size weights cancel the conditional denominators and produce the global "
                        + "factor 1/Z.")),
                    Paragraph(Text(
                        "The pairing <f,(Id-E_B)f>_pi itself is real and nonnegative: orthogonality gives <E_B "
                        + "f,f-E_B f>_pi=0 and therefore <f,(Id-E_B)f>_pi=||f-E_B f||_pi^2 as a complex number with"
                        + " zero imaginary part. Alternatively, in the centered double sum replace E_B f(x) by E_B "
                        + "f(y) on every supported pair and use sum_x T_B(x,y)=1; this directly recovers the same "
                        + "squared residual norm. These arguments apply to arbitrary complex functions, with "
                        + "conjugate cross terms retained.")),
                    Paragraph(Text(
                        "Now take any finite index set I and any family a maps to B_a of finite subsets of Fin n,"
                        + " allowing an empty index set. Set r_a=1 for every a in I, with a separate refresh clock "
                        + "for each index. Define (L_refresh f)(x)=sum_{a in I}((E_{B_a}f)(x)-f(x)), so "
                        + "-L_refresh=sum_{a in I}(Id-E_{B_a}). Define the Dirichlet energy D(f)=Re<f,-L_refresh "
                        + "f>_pi. Linearity and the single-block chain give D(f)=sum_{a in I} "
                        + "||f-E_{B_a}f||_pi^2=sum_{a in I} pi[V_{B_a}(f;.)]=(1/(2Z)) sum_{a in I} sum_x sum_y "
                        + "T_{B_a}(x,y)|f(x)-f(y)|^2. The corresponding centered and exterior-average expressions "
                        + "are summed with the same indices.")),
                    Paragraph(Text(
                        "Repeated block values contribute separately, once per clock index; they are not "
                        + "collapsed to a set of distinct blocks. There is no factor 1/M in L_refresh or D, where "
                        + "M=card(I). Only when M>0 may one also introduce the discrete-time average P=(1/M) sum_{a"
                        + " in I} E_{B_a}; then L_refresh=M(P-Id). For I empty, L_refresh and D are zero and no "
                        + "division by M is used. Under the book's parameter map, its blocks are B_a={i : "
                        + "a<=i.val+1<=a+ell-1}, ell=2k-1, indexed by all integers a=2-ell,...,n for n>=1, with "
                        + "M=n+ell-1; equal truncated intervals keep their separate indices. The identities above "
                        + "do not require this particular family.")),
                    Paragraph(Text(
                        "For B empty, every fiber is {x}, mu_B(x) is the point mass at x, E_B=Id and all "
                        + "single-block energies and conditional variances vanish. For B=Finset.univ, the only "
                        + "realized exterior is empty, the fiber is all of S, mu_B(x)=pi and E_B f=pi[f]. "
                        + "Disconnected blocks satisfy the same formulas because agreement on the whole complement "
                        + "still defines the same partition. No independence of their components is assumed. Short "
                        + "words n<k are included. At n=0 the sole legal state is the empty word, Z=1, every "
                        + "refresh is the identity and every energy vanishes. This asserts no excited eigenvalue or"
                        + " excited gap for an empty chain.")),
                    Paragraph(Text(
                        "For a realizable exterior eta, encode a completion by its true-bit subset A of B. "
                        + "Let w_eta(A) equal true exactly on A within B and equal eta on B-complement, and set "
                        + "F_eta={A subset of B : DBonacciAdmissible k n w_eta(A)}. Restriction to true bits and "
                        + "reassembly w_eta are inverse bijections between the original completion support, C_eta "
                        + "and F_eta. Thus m_eta=card(F_eta)>0 and the original conditional law becomes the uniform "
                        + "law 1/m_eta on F_eta. The actual exterior mass remains q_B(eta)=m_eta/Z.")),
                    Paragraph(Text(
                        "The family F_eta is lower under inclusion. Erasing i from A changes w_eta(A) only by "
                        + "setting its B-coordinate i to false; the original legal_delete preserves legality and "
                        + "leaves every exterior coordinate fixed. Iterating deletions gives A' in F_eta whenever "
                        + "A' is a subset of A in F_eta. This is also the direct application of the pinned "
                        + "Finset.antitone_iff_forall_insert_le and isLowerSet_setOfPred criteria. Since the fiber "
                        + "is inhabited, its empty true-bit subset belongs to F_eta, even when eta contains true "
                        + "bits outside B. For every nonnegative integer ell with card(B)<=ell, "
                        + "m_eta<=2^card(B)<=2^ell.")),
                    Paragraph(Text(
                        "Apply HereditaryFlip.Metric.flipGraph to F_eta: its vertices are these supported "
                        + "assignments and A is adjacent to R exactly when card(A symmetric-difference R)=1. "
                        + "The canonical exists_shortest_walk, connected and dist_eq suppliers give connectedness "
                        + "and graph distance card(A symmetric-difference R). Reassembly preserves this distance "
                        + "as the full-word Hamming distance because both states have exterior eta. Deleting to "
                        + "A intersect R and reversing the deletion path from R gives a legal path of that length. "
                        + "For general B this graph is on one fixed-exterior support; no states with a different "
                        + "exterior are added to its vertex set.")),
                    Paragraph(Text(
                        "For B=Finset.univ, every legal name corresponds to its full true-bit subset, and the "
                        + "inverse takes a supported subset to its legal Boolean word. The exterior is empty, so "
                        + "this is a bijection from S to the full hereditary support. Transporting flipGraph along "
                        + "this bijection gives exactly the actual legal-name graph: x and y are adjacent if and "
                        + "only if card({i : x.val(i) differs from y.val(i)})=1. The transported graph is connected "
                        + "and its native graph distance is this full Hamming distance. Both adjacency and distance "
                        + "are identified on the legal states themselves, including the single empty state at n=0.")),
                    Paragraph(Text(
                        "For i in B, fixing eta and every other B-coordinate fixes exactly the original full "
                        + "exterior of the singleton {i}, since B-complement together with B minus {i} is "
                        + "{i}-complement. In a supported state x, further conditioning the uniform C_eta law on "
                        + "those remaining coordinates therefore gives precisely mu_{ {i} }(x), by "
                        + "completionLaw_apply and completionLaw_congr. If its singleton support has size r, the "
                        + "conditioning event has mass r/m_eta; dividing each supported mass 1/m_eta by this event "
                        + "mass gives 1/r. Deletion ensures that false is supported, so the bit support is either "
                        + "{false} or {false,true}, never {true}. Every distinct legal flip has transition mass "
                        + "1/2 under the original singleton refresh. A fixed singleton fiber contributes zero "
                        + "variance; no independent replacement kernel is introduced.")),
                    Paragraph(Text(
                        "Write energy_B(f)=Re<f,(Id-E_B)f>_pi=pi[V_B(f;.)] for the original block energy, "
                        + "and energy_i(f)=energy_{ {i} }(f) for the global rate-one singleton energy. For arbitrary "
                        + "complex f, define the conditional site energy within C_eta by "
                        + "Dsite_eta(f)=(1/m_eta) sum_{x in C_eta} sum_{i in B} V_{ {i} }(f;x). Each variance "
                        + "uses the original singleton law just identified. Equivalently, its pair expression is "
                        + "(1/(2m_eta)) sum_{x in C_eta} sum_{i in B} sum_{y in C_eta} "
                        + "T_{ {i} }(x,y)|f(x)-f(y)|^2. Singleton updates stay in this same exterior fiber.")),
                    Paragraph(Text(
                        "Put g_eta(A)=f(w_eta(A)), with w_eta(A) regarded as its legal subtype element. Let "
                        + "Q_eta=sum_{A in F_eta} sum_{R in F_eta, card(A symmetric-difference R)=1} "
                        + "|g_eta(A)-g_eta(R)|^2 count ordered one-flip pairs, and let U_eta sum the same squared "
                        + "differences once per unordered edge. Then Q_eta=2U_eta. The factor 1/2 in the variance "
                        + "pair formula and the legal-flip transition mass 1/2 give exactly "
                        + "Dsite_eta(f)=Q_eta/(4m_eta)=U_eta/(2m_eta). Diagonal refreshes have zero difference. "
                        + "The squared differences are complex moduli, so these coefficients also hold for "
                        + "complex-valued f.")),
                    Paragraph(Text(
                        "For card(B)<=ell, the lower-family comparison gives Var_eta(f)<=ell*Q_eta/4. Here "
                        + "Var_eta(f)=(1/m_eta) sum_{A in F_eta}|g_eta(A)-gbar_eta|^2 and "
                        + "gbar_eta=(1/m_eta) sum_{A in F_eta}g_eta(A). In terms of the reused suppliers, a "
                        + "HereditaryFlip.Metric geodesic has length at most ell; the triangle inequality and "
                        + "the pinned sq_sum_le_card_mul_sum_sq bound each endpoint squared difference by ell "
                        + "times the path's edge sum. Both orientations of every path edge occur in Q_eta, so "
                        + "this edge sum is at most Q_eta/2 and the endpoint bound is ell*Q_eta/2. Averaging over all ordered "
                        + "endpoint pairs and using Var_eta(f)=(1/(2m_eta^2)) sum_A sum_R "
                        + "|g_eta(A)-g_eta(R)|^2 gives the displayed comparison. Substituting the actual site "
                        + "energy yields Var_eta(f)<=ell*m_eta*Dsite_eta(f)<=ell*2^ell*Dsite_eta(f). "
                        + "Dsite_eta already contains its conditional average 1/m_eta; no second such factor "
                        + "is inserted.")),
                    Paragraph(Text(
                        "Average once over distinct realizable exteriors with their actual weights m_eta/Z. "
                        + "The block identity is energy_B(f)=sum_eta (m_eta/Z)Var_eta(f). Also "
                        + "sum_eta (m_eta/Z)Dsite_eta(f)=(1/Z) sum_x sum_{i in B} V_{ {i} }(f;x) "
                        + "=sum_{i in B} energy_i(f): the factor m_eta cancels the conditional average within "
                        + "each partition fiber. Consequently the actual arbitrary-block comparison is "
                        + "energy_B(f)<=ell*2^ell*sum_{i in B} energy_i(f), for k>=2, n>=0 and card(B)<=ell. "
                        + "This uses the original uniform legal-state law and rate-one singleton clocks. It "
                        + "requires neither independent block components nor a uniform law on exterior assignments.")),
                    Paragraph(Text(
                        "For n>=1, take ell=2k-1 and the original zero-based integer starts "
                        + "a in Icc(1-ell,n-1), with B_a={i : a<=i.val<=a+ell-1}. These are the same indexed "
                        + "clocks as the book's one-based starts above after adding one to a. Each block has "
                        + "cardinality at most ell. A fixed site i belongs to exactly the ell indexed blocks "
                        + "whose starts range from i.val-ell+1 through i.val. Hence summing the preceding "
                        + "comparison gives sum_a energy_{B_a}(f)<=ell^2*2^ell*sum_i energy_i(f). For short "
                        + "chains, repeated values of B_a, including repeated full-chain blocks, remain separate "
                        + "clock indices in this sum. There is no factor 1/M. The coefficient depends on k; "
                        + "this comparison makes no optimality or K-uniform claim.")),
                    Paragraph(Text(
                        "The comparison includes empty and disconnected B and singleton completion supports. "
                        + "A singleton F_eta has Q_eta=U_eta=Var_eta=Dsite_eta=0. If B is empty, both sides of "
                        + "the block comparison are zero. At n=0 every block is empty and every indexed block "
                        + "and singleton energy sum is zero, without supplying an excited gap.")),
                    Paragraph(Text(
                        "This application gives the actual-law, conditional-projection and complex-energy "
                        + "calculation in the book's Chapter 39 example, Paper derivation: a uniform gap at fixed "
                        + "forbidden-run length. Its canonical suppliers are the original completionLaw_apply and "
                        + "completionLaw_congr, completion_nonempty, DBonacciName and its counting and positivity "
                        + "results, the restrictBlock and conditionalBlockLaw definitions, legal_delete, and "
                        + "HereditaryFlip.Metric's hereditary graph and Hamming-geodesic results. The support "
                        + "correspondence, conditional coefficients and indexed block-to-site comparison are "
                        + "applications of these suppliers and finite-sum estimates, without a claim of "
                        + "mathematical novelty.")),
                    Paragraph(Text(
                        "The coupled-generator application in CostCoupling supplies the generic route from actual"
                        + " adjacent-state couplings and a summed drift bound to a uniform Poincare inequality. The"
                        + " fiber calculation here supplies the specific legal-state kernel, its projection and its"
                        + " variance normalization, together with the actual block-to-single-site energy comparison "
                        + "and the legal-state graph/Hamming correspondence. The complete actual block Poincare "
                        + "inequality and the original uniform-gap assembly remain unfinished; these comparison "
                        + "and metric identities alone supply no complete uniform heat-bath gap. The application "
                        + "also establishes no parent-Hamiltonian or full-sector gap and"
                        + " no physical or Rauzy realization; those require their own operator identification and "
                        + "sector comparison or realization hypotheses."))
                )))));

    private static Formula StepFormula()
    {
        var k = F.Id("k"); var n = F.Id("n"); var f = F.Id("F");
        var x = F.Id("x"); var y = F.Id("y"); var i = F.Id("i");
        var h = F.Id("h"); var g = F.Id("g");
        var p = Call("evalLaw", f, x, h, i);
        var q = Call("evalLaw", f, y, g, i);
        var joint = Call("J", p, q);
        var conclusion = And(Rel(Call("mapFst", joint), Eq, p),
            Rel(Call("mapSnd", joint), Eq, q),
            Rel(Seq(D(1), Slash, D(2)), Leq,
                Call("mass", joint, Op("false"), Op("false"))));
        var unfixed = Seq(Neg, Sp, Par(Seq(i, Sp, InMacro, Sp, f)));
        var atSite = All(i, Call("Fin", n), Imp(unfixed, conclusion));
        var fibers = All(h, Call("Nonempty", Call("C", k, n, f, x)),
            All(g, Call("Nonempty", Call("C", k, n, f, y)), atSite));
        return All(Seq(k, Comma, n), Nat,
            Imp(Rel(D(0), Lt, k), All(f, Call("Finset", Call("Fin", n)),
                All(Seq(x, Comma, y), Word(n), fibers))));
    }

    private static Formula ScreenFormula()
    {
        var k = F.Id("k"); var n = F.Id("n");
        var x = F.Id("x"); var y = F.Id("y");
        var z = F.Id("z"); var t = F.Id("t");
        var condition = And(Rel(Call("at", x, z), Eq, Op("false")),
            Rel(Call("at", y, z), Eq, Op("false")));
        var conclusion = All(t, Word(n), Rel(Call("A", k, n, Call("S", x, z, t)),
            Iff, Call("A", k, n, Call("S", y, z, t))));
        var atZero = All(z, Call("Fin", n), Imp(condition, conclusion));
        return All(Seq(k, Comma, n), Nat, Imp(Rel(D(0), Lt, k),
            All(Seq(x, Comma, y), Word(n), Imp(
                And(Call("A", k, n, x), Call("A", k, n, y)), atZero))));
    }

    private static Formula ResetFormula()
    {
        var k = F.Id("k"); var n = F.Id("n"); var f = F.Id("F");
        var x = F.Id("x"); var y = F.Id("y"); var z = F.Id("z");
        var i = F.Id("i"); var w = F.Id("w");
        var fixedLeft = All(i, Call("Fin", n), Imp(Rel(Call("val", i), Leq, Call("val", z)),
            Seq(i, Sp, InMacro, Sp, f)));
        var farSame = All(i, Call("Fin", n), Imp(
            And(Seq(i, Sp, InMacro, Sp, f), Rel(Call("val", z), Lt, Call("val", i))),
            Rel(Call("at", x, i), Eq, Call("at", y, i))));
        var unchanged = All(w, Word(n), All(i, Call("Fin", n),
            Imp(Rel(Call("val", z), Lt, Call("val", i)),
                Rel(Call("at", Call("S", y, z, w), i), Eq, Call("at", w, i)))));
        var marginals = And(
            Rel(Call("mapFst", Call("R", f, x, y, z)), Eq, Call("L", f, x)),
            Rel(Call("mapSnd", Call("R", f, x, y, z)), Eq, Call("L", f, y)));
        var conclusion = And(
            Rel(Call("mapReset", Call("L", f, x), y, z), Eq, Call("L", f, y)),
            unchanged, marginals);
        var assumptions = And(Rel(Call("at", x, z), Eq, Op("false")),
            Rel(Call("at", y, z), Eq, Op("false")), fixedLeft, farSame);
        return All(Seq(k, Comma, n), Nat, Imp(Rel(D(0), Lt, k),
            All(f, Call("Finset", Call("Fin", n)), All(Seq(x, Comma, y), Word(n),
                Imp(And(Call("A", k, n, x), Call("A", k, n, y)),
                    All(z, Call("Fin", n), Imp(assumptions, conclusion)))))));
    }

    private static Formula PrefixFormula()
    {
        var k = F.Id("k"); var n = F.Id("n"); var f = F.Id("F");
        var s = F.Id("s"); var x = F.Id("x"); var y = F.Id("y");
        var h = F.Id("h"); var g = F.Id("g"); var i = F.Id("i");
        var joint = Call("P", s, f, x, y, h, g);
        var free = All(i, Call("Fin", n), Imp(Seq(i, Sp, InMacro, Sp, s),
            Seq(Neg, Sp, Par(Seq(i, Sp, InMacro, Sp, f)))));
        var conclusion = And(Rel(Call("mapFst", joint), Eq, Call("L", f, x, h)),
            Rel(Call("mapSnd", joint), Eq, Call("L", f, y, g)));
        var fibers = All(Seq(x, Comma, y), Word(n),
            All(h, Call("Nonempty", Call("C", k, n, f, x)),
                All(g, Call("Nonempty", Call("C", k, n, f, y)), conclusion)));
        var fixedSet = All(f, Call("Finset", Call("Fin", n)), Imp(free, fibers));
        var lists = All(s, Call("List", Call("Fin", n)), Imp(Call("Nodup", s), fixedSet));
        return All(Seq(k, Comma, n), Nat, Imp(Rel(D(0), Lt, k), lists));
    }

    private static Formula CostFormula()
    {
        var k = F.Id("k"); var n = F.Id("n"); var f = F.Id("F");
        var s = F.Id("s"); var x = F.Id("x"); var y = F.Id("y");
        var h = F.Id("h"); var g = F.Id("g");
        var i = F.Id("i"); var j = F.Id("j");
        var inS = Seq(i, Sp, InMacro, Sp, s);
        var notF = Seq(Neg, Sp, Par(Seq(i, Sp, InMacro, Sp, f)));
        var free = All(i, Call("Fin", n), Imp(inS, notF));
        var cover = All(i, Call("Fin", n), Imp(notF, inS));
        var order = All(i, Call("Fin", n), All(j, Call("Fin", n),
            Imp(Call("Before", s, i, j), Rel(Call("val", i), Lt, Call("val", j)))));
        var far = All(i, Call("Fin", n), All(j, Call("Fin", n), Imp(
            And(inS, Seq(j, Sp, InMacro, Sp, f), Rel(Call("val", i), Lt, Call("val", j))),
            Rel(Call("at", x, j), Eq, Call("at", y, j)))));
        var cost = Rel(Call("ExpectedHamming", Call("P", s, f, x, y, h, g), s), Leq, D(1));
        var fibers = All(Seq(x, Comma, y), Word(n),
            All(h, Call("Nonempty", Call("C", k, n, f, x)),
                All(g, Call("Nonempty", Call("C", k, n, f, y)), Imp(far, cost))));
        var fixedSet = All(f, Call("Finset", Call("Fin", n)), Imp(And(free, cover), fibers));
        var lists = All(s, Call("List", Call("Fin", n)), Imp(And(Call("Nodup", s), order), fixedSet));
        return All(Seq(k, Comma, n), Nat, Imp(Rel(D(0), Lt, k), lists));
    }

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Word(Formula n) => Seq(Open, Call("Fin", n), Sp, To, Sp, Op("Bool"), Close);
    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Op(name), [.. args]);
    private static Formula Rel(Formula a, Formula r, Formula b) => Seq(a, Sp, r, Sp, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(Formula v, Formula t, Formula b) => Par(Seq(Forall, Sp, Open, v, Colon, t, Close, Comma, Sp, Par(b)));
    private static Formula Imp(Formula a, Formula b) => Par(Rel(Par(a), Implies, Par(b)));
    private static Formula And(params Formula[] parts)
    {
        var result = new System.Collections.Generic.List<Formula>();
        for (var i = 0; i < parts.Length; ++i)
        {
            if (i > 0) result.Add(Seq(Sp, Land, Sp));
            result.Add(Par(parts[i]));
        }
        return Par(Seq([.. result]));
    }
}
