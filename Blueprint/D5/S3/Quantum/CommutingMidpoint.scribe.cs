using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class CommutingMidpointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/CommutingMidpoint.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/rajaei2026generalized");
    private static Formula V(string name) => F.Id(name);
    private static Formula Sq(Formula a) => Seq(a, Caret, Grp(D(2)));
    private static Formula U(Formula a, Formula b) => Call("U", a, b);
    private static Formula Hf(Formula a, Formula b) => Call("H", a, b);
    private static Formula Fr(Formula r, Formula a, Formula b) => Call("F", r, a, b);
    private static Formula Br(Formula r, Formula a, Formula b) => Call("B", r, a, b);
    private static Formula X(Formula z) => Call("X", z);
    private static Formula Half => Seq(Frac, Grp(D(1)), Grp(D(2)));
    private static Formula Rat(byte numerator, params byte[] denominator) =>
        Seq(Frac, Grp(D(numerator)), Grp(D(denominator)));
    private static Formula SqrtOf(Formula a) => Seq(Sqrt, Grp(a));
    private static Formula ReOf(Formula a) => Seq(Re, Open, a, Close);
    private static Formula Names(string names) => Seq(System.Linq.Enumerable.ToArray(
        System.Linq.Enumerable.SelectMany(names.Split(','),
            (name, index) => index == 0 ? new[] { V(name) } : new[] { Comma, Sp, V(name) })));
    private static Formula All(string names, Formula conclusion) =>
        Seq(Forall, Sp, Names(names), Comma, Quad, conclusion);
    private static DocumentBlock Entry(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create("commuting-midpoint-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Commuting qubit density inputs contract generalized Bures distance at the scalar midpoint reference.",
        H("Commuting Qubit Midpoint Contraction"),
        Blocks(
            Paragraph(Text(
                "All matrices are complex. A density matrix is positive semidefinite with trace one. "
                + "Except for the dimension-independent norm identity, the matrices are two by two. "
                + "Every square root is the positive functional-calculus root; F is the ordered "
                + "generalized fidelity, B(R,P,Q)=Re tr(P+Q)-2 Re F(R,P,Q), and the distance is sqrt(B). "
                + "Only P and Q commute in the channel theorem. Their outputs can have arbitrary complex coherence. "
                + "The transported reference must be positive definite.")),
            Paragraph(Text(
                "Ma, Rajaei and Zhang, Generalized Fidelity, the Data Processing Inequality, and Convexity, "
                + "arXiv:2609.09753v3, give the ordered-root quotient, Pauli and Bloch identities, "
                + "the weighted-root norm formula and scalar sufficient criteria. Their unrestricted-DPI "
                + "counterexample supersedes the unresolved unrestricted question in v1. "
                + "Afham and Ferrie, arXiv:2410.04937v2, supply the generalized-fidelity and squared-Bures "
                + "conventions and transported-reference question. Vuong, arXiv:2605.28885v1, "
                + "recomputes pair-dependent polar references; these need not equal the transported midpoint. "
                + "The results below concern this positive commuting-input family and the failure of "
                + "scalar-balance necessity. They give no full classification of Good triples.")),
            Entry("rootFidelity", "Root fidelity",
                All("S,T", Seq(U(V("S"), V("T")), Eq,
                    ReOf(Call("tr", SqrtOf(Seq(SqrtOf(V("S")), V("T"), SqrtOf(V("S")))))))),
                "For matrices on any finite decidable index type, U(S,T) is the real trace of "
                + "sqrt(sqrt(S) T sqrt(S)). This is root fidelity, without a final square.", DescribeRole.Definition, true),
            Entry("bures_eq_weighted_root_norm_sq", "The weighted-root norm identity",
                All("S,V,T", Seq(Call("PSD", V("S")), Land, Call("PSD", V("V")), Land,
                    Call("PD", V("T")), Rightarrow,
                    Br(V("T"), V("S"), V("V")), Eq,
                    Sq(Seq(Vert, Call("inv", SqrtOf(V("T"))), Open,
                        SqrtOf(Seq(SqrtOf(V("T")), V("S"), SqrtOf(V("T")))), Minus,
                        SqrtOf(Seq(SqrtOf(V("T")), V("V"), SqrtOf(V("T")))), Close, Vert)))),
                "For every finite decidable index type, PSD S,V and PD T, B(T,S,V) equals the "
                + "squared Frobenius norm displayed above. No trace normalization is required. "
                + "Expand the norm using the Frobenius trace identity. The diagonal terms are tr(S), "
                + "tr(V); the two cross terms have equal real parts because they are conjugate traces. "
                + "This proves nonnegativity even for singular S or V.", literature: true),
            Entry("qubit_root_fidelity_quotient", "The actual qubit quotient",
                All("S,V,T", Seq(Call("State", V("S")), Land, Call("State", V("V")), Land,
                    Call("PD", V("T")), Land, Call("tr", V("T")), Eq, D(1), Rightarrow,
                    D(0), Lt, V("a"), Land, D(0), Lt, V("b"), Land,
                    ReOf(Fr(V("T"), V("S"), V("V"))), Eq,
                    Frac, Grp(Sq(V("a")), Plus, Sq(V("b")), Plus, Sq(V("c")), Minus, D(1)),
                    Grp(D(2), V("a"), V("b")))),
                "Put a=U(T,S), b=U(T,V), c=U(S,V). For every pair of qubit density matrices "
                + "and every trace-one PD reference T, a and b are strictly positive and the real "
                + "ordered fidelity is the stated quotient. The proof uses the two-dimensional "
                + "trace recurrence for actual matrix square roots and determinants, including singular S,V.", literature: true),
            Entry("binaryFidelity", "Binary root fidelity",
                All("p,q", Seq(Hf(V("p"), V("q")), Eq,
                    SqrtOf(Seq(V("p"), V("q"))), Plus,
                    SqrtOf(Seq(Open, D(1), Minus, V("p"), Close, Open, D(1), Minus, V("q"), Close)))),
                "H(p,q)=sqrt(pq)+sqrt((1-p)(1-q)); its probabilistic uses have p,q in [0,1].",
                DescribeRole.Definition),
            Entry("fidelity_sq_lower_bound_from_half_order", "A half-order lower bound",
                All("S,T", Seq(Call("State", V("S")), Land, Call("PSD", V("T")), Land,
                    Call("PSD", Seq(V("T"), Minus, Half, V("S"))), Rightarrow,
                    Half, Le, Sq(U(V("T"), V("S"))))),
                "For every density S and PSD T with T-S/2 PSD, U(T,S) squared is at least one half. "
                + "Congruence by sqrt(S), operator monotonicity of sqrt, and positivity of trace give "
                + "U(S,T)>=sqrt(1/2). The actual qubit formula proves symmetry U(S,T)=U(T,S). "
                + "There is no invertibility assumption on S and no trace-one requirement on T."),
            Entry("classical_binary_preparation_fidelity", "Classical binary preparation",
                All("p,q,x,y", Seq(Call("UnitInterval", V("p"), V("q"), V("x"), V("y")), Rightarrow,
                    Hf(V("p"), V("q")), Le,
                    Hf(Seq(V("p"), V("x"), Plus, Open, D(1), Minus, V("p"), Close, V("y")),
                        Seq(V("q"), V("x"), Plus, Open, D(1), Minus, V("q"), Close, V("y"))))),
                "For all p,q,x,y in the closed unit interval, preparing binary probabilities x,y "
                + "with mixing probabilities p,q cannot decrease H. Apply Cauchy-Schwarz to each "
                + "coordinate and add the two inequalities. Zero probabilities are included."),
            Entry("chordVector", "A full Bloch chord",
                All("d,e,z", Seq(Call("r", V("z")), Eq, V("d"), Plus,
                    SqrtOf(Seq(D(1), Minus, Sq(Seq(Vert, V("d"), Vert)))),
                    Open, D(2), V("z"), Minus, D(1), Close, V("e"))),
                "For d,e in Euclidean three-space and real z, r(z)=d+sqrt(1-||d|| squared)(2z-1)e. "
                + "The full physical chord has d perpendicular to e, ||e||=1, ||d|| squared<1 and z in [0,1].",
                DescribeRole.Definition),
            Entry("chordState", "Actual states on a chord",
                All("d,e,z", Seq(X(V("z")), Eq, Call("rho", Call("r", V("z"))))),
                "X(z) is blochMatrix(1,r(z)), the canonical complex qubit matrix. "
                + "On the full physical chord it is PSD with trace one; interior parameters give PD states.",
                DescribeRole.Definition),
            Entry("qubit_chord_factorization", "The sign-sensitive chord factorization",
                All("d,e,r,s,t", Seq(Call("ChordDomain", V("d"), V("e"), V("r"), V("s"), V("t")), Rightarrow,
                    D(0), Lt, V("a"), Land, D(0), Lt, V("b"), Land,
                    D(0), Le, V("f"), Land, D(0), Le, V("w"), Land,
                    Open, Sq(V("f")), Minus, Sq(V("w")), Close, Sq(V("a")), Sq(V("b")), Eq,
                    Tau, Open, D(1), Minus, Sq(V("w")), Close,
                    Open, Sq(V("a")), Plus, Sq(V("b")), Minus, D(1), Close, Land,
                    Open, D(1), Le, Seq(Sq(V("a")), Plus, Sq(V("b"))), Rightarrow, V("w"), Le, V("f"), Close)),
                "ChordDomain means d perpendicular to e, ||e||=1, tau=||d|| squared<1, "
                + "0<r<1 and s,t in [0,1]. Put a=U(X(r),X(s)), b=U(X(r),X(t)), "
                + "f=Re F(X(r),X(s),X(t)), w=H(s,t). All signs in the display hold. "
                + "The binary Gram identity and U(X(x),X(y)) squared=tau+(1-tau)H(x,y) squared "
                + "give the factorization. Since a,b>0 and f,w>=0, a squared+b squared>=1 implies f>=w."),
            Entry("qubit_chord_strict_sign_and_boundary", "Strict comparison and degenerate boundaries",
                All("d,e,r,s,t", Seq(Call("ChordDomain", V("d"), V("e"), V("r"), V("s"), V("t")), Rightarrow,
                    Open, D(0), Lt, Tau, Land, V("s"), Neq, V("t"), Rightarrow,
                    Open, V("w"), Le, V("f"), Leftrightarrow,
                    D(1), Le, Seq(Sq(V("a")), Plus, Sq(V("b"))), Close, Land,
                    Open, V("f"), Eq, V("w"), Leftrightarrow,
                    Seq(Sq(V("a")), Plus, Sq(V("b"))), Eq, D(1), Close, Close, Land,
                    Open, Tau, Eq, D(0), Rightarrow, V("f"), Eq, V("w"), Close, Land,
                    Open, V("s"), Eq, V("t"), Rightarrow, V("f"), Eq, V("w"), Eq, D(1), Close)),
                "Use the same chord domain and a,b,f,w,tau as above. If tau>0 and s differs from t, "
                + "1-w squared is strictly positive, giving both exact equivalences. On a diameter, "
                + "tau=0 gives f=w. Equal states s=t give f=w=1. These are fixed-chord statements, "
                + "without a classification of arbitrary channel triples."),
            Entry("mixture", "Mixtures of actual matrices",
                All("p,A,B", Seq(Call("mix", V("p"), V("A"), V("B")), Eq,
                    V("p"), V("A"), Plus, Open, D(1), Minus, V("p"), Close, V("B"))),
                "mixture(p,A,B)=p A+(1-p)B, with real scalar multiplication on complex matrices.", DescribeRole.Definition),
            Entry("prepared_qubit_midpoint_fidelity", "Arbitrary prepared outputs",
                All("A,B,p,q", Seq(Call("State", V("A")), Land, Call("State", V("B")), Land,
                    Call("UnitInterval", V("p"), V("q")), Land, Call("PD", V("T")), Rightarrow,
                    Hf(V("p"), V("q")), Le, ReOf(Fr(V("T"), V("S"), V("V"))), Land,
                    D(0), Le, Br(V("T"), V("S"), V("V")), Le,
                    D(2), Minus, D(2), Hf(V("p"), V("q")))),
                "For arbitrary complex qubit densities A,B set T=(A+B)/2, S=pA+(1-p)B and "
                + "V=qA+(1-q)B, with p,q in [0,1]. If T is PD then the full displayed conclusion holds. "
                + "The Bloch line through distinct A,B extends to a full chord. The midpoint dominates "
                + "each prepared state by one half, so the chord comparison applies; classical preparation "
                + "then gives H(p,q). Equal A,B are treated directly. No output commutation is required."),
            Entry("midpointReference", "The scalar midpoint reference",
                Seq(V("R"), Underscore, Grp(D(0)), Eq, Half, V("I")),
                "R0=I/2 as a complex two-by-two matrix; it is PD and has trace one.", DescribeRole.Definition),
            Entry("commuting_midpoint_all_positive_trace_preserving", "Every positive trace-preserving linear map",
                All("P,Q,Phi", Seq(Call("State", V("P")), Land, Call("State", V("Q")), Land,
                    V("P"), V("Q"), Eq, V("Q"), V("P"), Land, Call("PositiveTP", V("Phi")), Land,
                    Call("PD", Call("Phi", V("R0"))), Rightarrow,
                    U(V("P"), V("Q")), Eq, ReOf(Fr(V("R0"), V("P"), V("Q"))), Le,
                    ReOf(Fr(Call("Phi", V("R0")), Call("Phi", V("P")), Call("Phi", V("Q")))), Land,
                    Br(Call("Phi", V("R0")), Call("Phi", V("P")), Call("Phi", V("Q"))), Le,
                    Br(V("R0"), V("P"), V("Q")))),
                "Phi ranges over every complex-linear map on all complex qubit matrices that maps "
                + "each PSD matrix to a PSD matrix and preserves trace on every matrix. R0=I/2. "
                + "For commuting density P,Q and PD Phi(R0), root fidelity equals the input ordered "
                + "fidelity and is bounded by the output ordered fidelity; B contracts. "
                + "For distinct inputs, the exact squared commutator trace forces their full Bloch chord "
                + "to be a diameter. Its endpoints E1,E0 satisfy R0=(E1+E0)/2. Complex linearity sends "
                + "the same three inputs to mixtures of Phi(E1),Phi(E0), so the prepared-output theorem applies. "
                + "Equal inputs follow from the norm identity."),
            Entry("commuting_midpoint_canonical_CPTP", "Canonical physical channels",
                All("P,Q,Phi", Seq(Call("State", V("P")), Land, Call("State", V("Q")), Land,
                    V("P"), V("Q"), Eq, V("Q"), V("P"), Land, Call("CPTP", V("Phi")), Land,
                    Call("PD", Call("Phi", V("R0"))), Rightarrow,
                    D(0), Le, V("Bout"), Land, D(0), Le, V("Bin"), Land,
                    V("Bout"), Le, V("Bin"), Land, SqrtOf(V("Bout")), Le, SqrtOf(V("Bin")))),
                "Phi is every existing QuantumChannel(Fin 2,Fin 2); its action is GeneralizedFidelity.rawMatrix. "
                + "Here Bin=B(R0,P,Q) and Bout=B(Phi(R0),Phi(P),Phi(Q)). The input hypotheses are PSD "
                + "trace-one P,Q with PQ=QP, and the only output-reference restriction is PD Phi(R0). "
                + "The channel's all-amplification complete positivity implies ordinary positivity. "
                + "Its canonical trace-preserving and complex-linear action gives the previous theorem. "
                + "The norm identity establishes both nonnegativities before taking square roots."),
            Entry("Good", "Universal transported-reference contraction",
                All("P,Q,R", Seq(Call("Good", V("P"), V("Q"), V("R")), Leftrightarrow,
                    Forall, Sp, V("Phi"), Comma, Call("CPTP", V("Phi")), Land,
                    Call("PD", Call("Phi", V("R"))), Rightarrow,
                    Br(Call("Phi", V("R")), Call("Phi", V("P")), Call("Phi", V("Q"))), Le,
                    Br(V("R"), V("P"), V("Q")))),
                "Good(P,Q,R) quantifies all canonical qubit CPTP channels with PD transported reference. "
                + "Its physical uses require P,Q density matrices and R PD of trace one. "
                + "The same channel acts on all three matrices.", DescribeRole.Definition),
            Entry("faithful_Good_outside_balance", "A faithful outside-balance triple",
                Seq(Call("Good", V("P"), V("Q"), V("R0")), Land,
                    Sq(U(V("R0"), V("P"))), Eq, Rat(4,5), Land,
                    Sq(U(V("R0"), V("Q"))), Eq, Rat(9,1,0), Land,
                    Sq(U(V("P"), V("Q"))), Eq, Seq(Frac, Grp(D(4,9)), Grp(D(5,0))), Land,
                    Rat(1,5,0), Lt, Rat(1,1,0)),
                "Take P=diag(9/10,1/10), Q=diag(4/5,1/5), R0=I/2. All three matrices are PD "
                + "densities. The theorem proves Good, the three exact squared root fidelities, "
                + "absolute squared imbalance 1/10, residual 1/50 and their strict inequality. "
                + "It also gives B(R0,P,Q)=2-7 sqrt(2)/5. Good follows from the universal channel theorem; "
                + "the scalar values use the actual matrix trace-determinant root formula."),
            Entry("singular_Good_outside_balance", "A singular outside-balance triple",
                Seq(Call("rank", V("P")), Eq, D(1), Land, Call("Good", V("P"), V("Q"), V("R0")), Land,
                    Sq(U(V("R0"), V("P"))), Eq, Half, Land,
                    Sq(U(V("R0"), V("Q"))), Eq, Half, Plus, Seq(Frac, Grp(SqrtOf(D(3))), Grp(D(4))), Land,
                    Sq(U(V("P"), V("Q"))), Eq, Rat(3,4), Land,
                    Rat(1,4), Lt, Seq(Frac, Grp(SqrtOf(D(3))), Grp(D(4)))),
                "Take P=diag(1,0), Q=diag(3/4,1/4), R0=I/2. P,Q are PSD trace-one states, "
                + "R0 is PD of trace one, and rank(P)=1. The theorem proves Good, the three exact "
                + "squared root fidelities, imbalance sqrt(3)/4, residual 1/4 and the strict inequality. "
                + "It also gives B(R0,P,Q)=2-sqrt(3). The rank and root values are exact, and the "
                + "universal channel statement includes singular inputs."),
            Entry("claim", "The proposed scalar necessity",
                Seq(Call("claim"), Leftrightarrow, Forall, Sp, Names("P,Q,R"), Comma,
                    Call("State", V("P")), Land, Call("State", V("Q")), Land,
                    Call("PDState", V("R")), Land, Call("Good", V("P"), V("Q"), V("R")), Rightarrow,
                    Seq(Bar, Sq(U(V("R"), V("P"))), Minus, Sq(U(V("R"), V("Q"))), Bar), Le,
                    D(1), Minus, Sq(U(V("P"), V("Q")))),
                "The proposed necessity ranges over every PSD density pair P,Q and every PD "
                + "trace-one reference R. It says that Good implies scalar balance. "
                + "No commutation assumption occurs in this proposed global assertion.", DescribeRole.Definition),
            Entry("result", "Scalar balance is not necessary",
                Seq(Neg, Call("claim")),
                "The faithful triple above refutes claim. Thus there exist three PD density matrices "
                + "with Good and strict failure of balance. The singular triple gives an additional "
                + "boundary example. This disproves the proposed necessity and the corresponding full "
                + "iff; it does not supply a replacement necessary-and-sufficient classification."))));
}
