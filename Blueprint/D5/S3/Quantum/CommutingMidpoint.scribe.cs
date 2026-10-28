using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class CommutingMidpointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/CommutingMidpoint.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/marajaeizhang2026generalizedv3");
    private static Formula V(string name) => Seq(Sp, F.Id(name));
    private static Formula Sq(Formula a) => Seq(a, Caret, Grp(D(2)));
    private static Formula U(Formula a, Formula b) => Call("U", a, b);
    private static Formula Hf(Formula a, Formula b) => Call("H", a, b);
    private static Formula Fr(Formula r, Formula a, Formula b) => Call("F", r, a, b);
    private static Formula Br(Formula r, Formula a, Formula b) => Call("B", r, a, b);
    private static Formula X(Formula z) => Call("X", V("d"), V("e"), z);
    private static Formula Half => Seq(Frac, Grp(D(1)), Grp(D(2)));
    private static Formula Rat(byte numerator, params byte[] denominator) =>
        Seq(Frac, Grp(D(numerator)), Grp(D(denominator)));
    private static Formula SqrtOf(Formula a) => Seq(Sqrt, Grp(a));
    private static Formula ReOf(Formula a) => Seq(Re, Open, a, Close);
    private static Formula Names(string names) => Seq(System.Linq.Enumerable.ToArray(
        System.Linq.Enumerable.SelectMany(names.Split(','),
            (name, index) => index == 0 ? new[] { V(name) } : new[] { Comma, Sp, V(name) })));
    private static Formula Rzero => Seq(V("R"), Underscore, Grp(D(0)));
    private static Formula RealType => Seq(Mathbb, Grp(V("R")));
    private static Formula MatrixType => Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), Seq(Mathbb, Grp(V("C"))));
    private static Formula VectorType => Call("EuclideanSpace", RealType, Call("Fin", D(3)));
    private static Formula Bound(string names, Formula type) => Seq(Open, Names(names), Colon, type, Close);
    private static Formula For(Formula binders, Formula body) => Seq(Forall, Sp, binders, Comma, Quad, body);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula BlochCommutator => Par(Seq(
        Call("blochMatrix", D(1), V("a")), Call("blochMatrix", D(1), V("b")), Minus,
        Call("blochMatrix", D(1), V("b")), Call("blochMatrix", D(1), V("a"))));
    private static Formula Implies(Formula premise, Formula conclusion) =>
        Seq(Par(premise), Rightarrow, Sp, Par(conclusion));
    private static Formula All(string names, Formula conclusion) => For(Seq(System.Linq.Enumerable.ToArray(
        System.Linq.Enumerable.Select(names.Split(','), name => Bound(name,
            name is "d" or "e" ? VectorType :
            name is "P" or "Q" or "R" or "S" or "V" or "T" or "A" or "B" ? MatrixType :
            name == "Phi" ? Call("ComplexLinearMap", MatrixType, MatrixType) : RealType)))), conclusion);
    private static Formula And(params Formula[] clauses) => Seq(System.Linq.Enumerable.ToArray(
        System.Linq.Enumerable.SelectMany(clauses, (clause, index) => index == 0 ?
            new[] { clause } : new[] { Land, Sp, clause })));
    private static Formula State(Formula a) => And(Call("PSD", a), Seq(Call("tr", a), Eq, D(1)));
    private static Formula Mix(Formula p, Formula a, Formula b) => Call("mix", p, a, b);
    private static Formula Abs(Formula a) => Seq(Bar, a, Bar);
    private static Formula Delta => Abs(Seq(Sq(U(Rzero, V("P"))), Minus, Sq(U(Rzero, V("Q")))));
    private static Formula Residual => Seq(D(1), Minus, Sq(U(V("P"), V("Q"))));
    private static Formula DensityData(bool faithful) => And(
        Call(faithful ? "PD" : "PSD", V("P")), Call(faithful ? "PD" : "PSD", V("Q")),
        Call("PD", Rzero), Seq(Call("tr", V("P")), Eq, D(1)),
        Seq(Call("tr", V("Q")), Eq, D(1)), Seq(Call("tr", Rzero), Eq, D(1)));
    private static Formula Witness(bool faithful) => For(Seq(Bound("P,Q", MatrixType)),
        Seq(And(Seq(V("P"), Eq, Call("diag", faithful ? Rat(9,1,0) : D(1), faithful ? Rat(1,1,0) : D(0))),
                Seq(V("Q"), Eq, Call("diag", faithful ? Rat(4,5) : Rat(3,4), faithful ? Rat(1,5) : Rat(1,4)))),
            Rightarrow, Sp, And(
                faithful ? DensityData(true) : And(DensityData(false), Seq(Call("rank", V("P")), Eq, D(1))),
                Call("Good", V("P"), V("Q"), Rzero),
                Seq(Sq(U(Rzero,V("P"))), Eq, faithful ? Rat(4,5) : Half),
                Seq(Sq(U(Rzero,V("Q"))), Eq, faithful ? Rat(9,1,0) : Seq(Half, Plus, RatSqrtThree)),
                Seq(Sq(U(V("P"),V("Q"))), Eq, faithful ? Seq(Frac,Grp(D(4,9)),Grp(D(5,0))) : Rat(3,4)),
                Seq(Delta, Eq, faithful ? Rat(1,1,0) : RatSqrtThree),
                Seq(Residual, Eq, faithful ? Rat(1,5,0) : Rat(1,4)),
                Seq(Residual, Lt, Delta),
                Seq(Br(Rzero,V("P"),V("Q")), Eq, faithful ?
                    Seq(D(2), Minus, Frac, Grp(D(7),SqrtOf(D(2))),Grp(D(5))) :
                    Seq(D(2),Minus,SqrtOf(D(3)))))));
    private static Formula RatSqrtThree => Seq(Frac, Grp(SqrtOf(D(3))), Grp(D(4)));
    private static Formula ChordData => And(
        Seq(Call("inner",V("d"),V("e")), Eq, D(0)),
        Seq(Call("norm",V("e")), Eq, D(1)), Seq(Sq(Call("norm",V("d"))), Lt, D(1)),
        Seq(D(0), Lt, V("r"), Lt, D(1)), Seq(D(0), Le, V("s"), Le, D(1)),
        Seq(D(0), Le, V("t"), Le, D(1)));
    private static Formula ChordReadouts(Formula body) => For(Seq(Bound("a,b,f,w",RealType)),
        Implies(And(Seq(V("a"),Eq,U(X(V("r")),X(V("s")))),
                Seq(V("b"),Eq,U(X(V("r")),X(V("t")))),
                Seq(V("f"),Eq,ReOf(Fr(X(V("r")),X(V("s")),X(V("t"))))),
                Seq(V("w"),Eq,Hf(V("s"),V("t")))), body));
    private static Formula PhiAt(Formula a) => Call("Phi",a);
    private static Formula InputBures => Br(Rzero,V("P"),V("Q"));
    private static Formula OutputBures => Br(PhiAt(Rzero),PhiAt(V("P")),PhiAt(V("Q")));
    private static Formula PositiveTP => And(
        Par(For(Bound("M",MatrixType), Implies(Call("PSD",V("M")),Call("PSD",PhiAt(V("M")))))),
        Par(For(Bound("M",MatrixType), Seq(Call("tr",PhiAt(V("M"))),Eq,Call("tr",V("M"))))));
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
                + "The root-fidelity definition and weighted-root norm identity allow any finite decidable index type; "
                + "the remaining results concern two-by-two matrices. "
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
            Entry("chordVector", "A full Bloch chord",
                All("d,e,z", Seq(Call("r", V("d"), V("e"), V("z")), Eq, V("d"), Plus,
                    SqrtOf(Seq(D(1), Minus, Sq(Seq(Vert, Sp, V("d"), Vert)))),
                    Open, D(2), V("z"), Minus, D(1), Close, V("e"))),
                "For d,e in Euclidean three-space and real z, r(z)=d+sqrt(1-||d|| squared)(2z-1)e. "
                + "The full physical chord has d perpendicular to e, ||e||=1, ||d|| squared<1 and z in [0,1].",
                DescribeRole.Definition),
            Entry("chordState", "Actual states on a chord",
                All("d,e,z", Seq(X(V("z")), Eq, Call("rho", Call("r", V("d"), V("e"), V("z"))))),
                "X(z) is blochMatrix(1,r(z)), the canonical complex qubit matrix. "
                + "On the full physical chord it is PSD with trace one; interior parameters give PD states.",
                DescribeRole.Definition),
            Entry("bloch_commutator_gram", "The Bloch commutator Gram identity",
                For(Bound("a,b", VectorType), Seq(
                    ReOf(Call("tr", Seq(Call("conjTranspose", BlochCommutator), BlochCommutator))),
                    Eq, Half, Par(Seq(Sq(Call("norm", V("a"))), Sq(Call("norm", V("b"))), Minus,
                        Sq(Call("inner", V("a"), V("b"))))))),
                "For arbitrary real Euclidean three-vectors a,b, the real trace of C conjugate-transpose times C, "
                + "where C=blochMatrix(1,a)blochMatrix(1,b)-blochMatrix(1,b)blochMatrix(1,a), "
                + "equals (||a|| squared ||b|| squared-inner(a,b) squared)/2."),
            Entry("qubit_chord_factorization", "The sign-sensitive chord factorization",
                All("d,e,r,s,t", Seq(ChordData, Rightarrow, Sp, ChordReadouts(Seq(
                    D(0), Lt, V("a"), Land, D(0), Lt, V("b"), Land,
                    D(0), Le, V("f"), Land, D(0), Le, V("w"), Land,
                    Open, Sq(V("f")), Minus, Sq(V("w")), Close, Sq(V("a")), Sq(V("b")), Eq,
                    Sq(Call("norm",V("d"))), Open, D(1), Minus, Sq(V("w")), Close,
                    Open, Sq(V("a")), Plus, Sq(V("b")), Minus, D(1), Close, Land,
                    Open, D(1), Le, Seq(Sq(V("a")), Plus, Sq(V("b"))), Rightarrow, V("w"), Le, V("f"), Close)))),
                "ChordDomain means d perpendicular to e, ||e||=1, tau=||d|| squared<1, "
                + "0<r<1 and s,t in [0,1]. Put a=U(X(r),X(s)), b=U(X(r),X(t)), "
                + "f=Re F(X(r),X(s),X(t)), w=H(s,t). All signs in the display hold. "
                + "The binary Gram identity and U(X(x),X(y)) squared=tau+(1-tau)H(x,y) squared "
                + "give the factorization. Since a,b>0 and f,w>=0, a squared+b squared>=1 implies f>=w."),
            Entry("qubit_chord_strict_sign_and_boundary", "Strict comparison and degenerate boundaries",
                All("d,e,r,s,t", Seq(ChordData, Rightarrow, Sp, ChordReadouts(Seq(
                    Open, D(0), Lt, Sq(Call("norm",V("d"))), Land, V("s"), Neq, Sp, V("t"), Rightarrow,
                    Open, V("w"), Le, V("f"), Leftrightarrow,
                    D(1), Le, Seq(Sq(V("a")), Plus, Sq(V("b"))), Close, Land,
                    Open, V("f"), Eq, V("w"), Leftrightarrow,
                    Seq(Sq(V("a")), Plus, Sq(V("b"))), Eq, D(1), Close, Close, Land,
                    Open, Sq(Call("norm",V("d"))), Eq, D(0), Rightarrow, V("f"), Eq, V("w"), Close, Land,
                    Open, V("s"), Eq, V("t"), Rightarrow, V("f"), Eq, V("w"), Eq, D(1), Close)))),
                "Use the same chord domain and a,b,f,w,tau as above. If tau>0 and s differs from t, "
                + "1-w squared is strictly positive, giving both exact equivalences. On a diameter, "
                + "tau=0 gives f=w. Equal states s=t give f=w=1. These are fixed-chord statements, "
                + "without a classification of arbitrary channel triples."),
            Entry("mixture", "Mixtures of actual matrices",
                All("p,A,B", Seq(Call("mix", V("p"), V("A"), V("B")), Eq,
                    V("p"), V("A"), Plus, Open, D(1), Minus, V("p"), Close, V("B"))),
                "mixture(p,A,B)=p A+(1-p)B, with real scalar multiplication on complex matrices.", DescribeRole.Definition),
            Entry("prepared_qubit_midpoint_fidelity", "Arbitrary prepared outputs",
                All("A,B,p,q", Seq(And(State(V("A")),State(V("B")),
                    Seq(D(0),Le,V("p"),Le,D(1)),Seq(D(0),Le,V("q"),Le,D(1)),
                    Call("PD",Mix(Half,V("A"),V("B")))),Rightarrow,Sp,
                    And(Seq(Hf(V("p"),V("q")),Le,
                        ReOf(Fr(Mix(Half,V("A"),V("B")),Mix(V("p"),V("A"),V("B")),Mix(V("q"),V("A"),V("B"))))),
                        Seq(D(0),Le,Br(Mix(Half,V("A"),V("B")),Mix(V("p"),V("A"),V("B")),Mix(V("q"),V("A"),V("B")))),
                        Seq(Br(Mix(Half,V("A"),V("B")),Mix(V("p"),V("A"),V("B")),Mix(V("q"),V("A"),V("B"))),
                            Le,D(2),Minus,D(2),Hf(V("p"),V("q")))))),
                "For arbitrary complex qubit densities A,B set T=(A+B)/2, S=pA+(1-p)B and "
                + "V=qA+(1-q)B, with p,q in [0,1]. If T is PD then the full displayed conclusion holds. "
                + "The Bloch line through distinct A,B extends to a full chord. The midpoint dominates "
                + "each prepared state by one half, so the chord comparison applies; classical preparation "
                + "then gives H(p,q). Equal A,B are treated directly. No output commutation is required."),
            Entry("midpointReference", "The scalar midpoint reference",
                Seq(V("R"), Underscore, Grp(D(0)), Eq, Half, V("I")),
                "R0=I/2 as a complex two-by-two matrix; it is PD and has trace one.", DescribeRole.Definition),
            Entry("commuting_midpoint_all_positive_trace_preserving", "Every positive trace-preserving linear map",
                All("P,Q,Phi", Seq(And(State(V("P")),State(V("Q")),
                    Seq(V("P"),V("Q"),Eq,V("Q"),V("P")),PositiveTP,Call("PD",PhiAt(Rzero))),Rightarrow,Sp,
                    And(Seq(U(V("P"),V("Q")),Eq,ReOf(Fr(Rzero,V("P"),V("Q")))),
                        Seq(U(V("P"),V("Q")),Le,ReOf(Fr(PhiAt(Rzero),PhiAt(V("P")),PhiAt(V("Q"))))),
                        Seq(OutputBures,Le,InputBures)))),
                "Phi ranges over every complex-linear map on all complex qubit matrices that maps "
                + "each PSD matrix to a PSD matrix and preserves trace on every matrix. R0=I/2. "
                + "For commuting density P,Q and PD Phi(R0), root fidelity equals the input ordered "
                + "fidelity and is bounded by the output ordered fidelity; B contracts. "
                + "For distinct inputs, the exact squared commutator trace forces their full Bloch chord "
                + "to be a diameter. Its endpoints E1,E0 satisfy R0=(E1+E0)/2. Complex linearity sends "
                + "the same three inputs to mixtures of Phi(E1),Phi(E0), so the prepared-output theorem applies. "
                + "Equal inputs follow from the norm identity."),
            Entry("commuting_midpoint_canonical_CPTP", "Canonical physical channels",
                For(Seq(Bound("P,Q",MatrixType),Bound("Phi",Call("QuantumChannel",Call("Fin",D(2)),Call("Fin",D(2))))),
                    Seq(And(State(V("P")),State(V("Q")),Seq(V("P"),V("Q"),Eq,V("Q"),V("P")),Call("PD",PhiAt(Rzero))),
                        Rightarrow,Sp,And(Seq(D(0),Le,OutputBures),Seq(D(0),Le,InputBures),
                            Seq(OutputBures,Le,InputBures),Seq(SqrtOf(OutputBures),Le,SqrtOf(InputBures))))),
                "Phi is every existing QuantumChannel(Fin 2,Fin 2); its action is GeneralizedFidelity.rawMatrix. "
                + "Here Bin=B(R0,P,Q) and Bout=B(Phi(R0),Phi(P),Phi(Q)). The input hypotheses are PSD "
                + "trace-one P,Q with PQ=QP, and the only output-reference restriction is PD Phi(R0). "
                + "The channel's all-amplification complete positivity implies ordinary positivity. "
                + "Its canonical trace-preserving and complex-linear action gives the previous theorem. "
                + "The norm identity establishes both nonnegativities before taking square roots."),
            Entry("Good", "Universal transported-reference contraction",
                All("P,Q,R", Seq(Call("Good", V("P"), V("Q"), V("R")), Leftrightarrow, Sp,
                    Par(For(Bound("Phi",Call("QuantumChannel",Call("Fin",D(2)),Call("Fin",D(2)))),
                        Implies(Call("PD", PhiAt(V("R"))),
                            Seq(Br(PhiAt(V("R")),PhiAt(V("P")),PhiAt(V("Q"))), Le,
                                Br(V("R"),V("P"),V("Q")))))))),
                "Good(P,Q,R) quantifies all canonical qubit CPTP channels with PD transported reference. "
                + "Its physical uses require P,Q density matrices and R PD of trace one. "
                + "The same channel acts on all three matrices.", DescribeRole.Definition),
            Entry("faithful_Good_outside_balance", "A faithful outside-balance triple",
                Witness(true),
                "Take P=diag(9/10,1/10), Q=diag(4/5,1/5), R0=I/2. All three matrices are PD "
                + "densities. The theorem proves Good, the three exact squared root fidelities, "
                + "absolute squared imbalance 1/10, residual 1/50 and their strict inequality. "
                + "It also gives B(R0,P,Q)=2-7 sqrt(2)/5. Good follows from the universal channel theorem; "
                + "the scalar values use the actual matrix trace-determinant root formula."),
            Entry("singular_Good_outside_balance", "A singular outside-balance triple",
                Witness(false),
                "Take P=diag(1,0), Q=diag(3/4,1/4), R0=I/2. P,Q are PSD trace-one states, "
                + "R0 is PD of trace one, and rank(P)=1. The theorem proves Good, the three exact "
                + "squared root fidelities, imbalance sqrt(3)/4, residual 1/4 and the strict inequality. "
                + "It also gives B(R0,P,Q)=2-sqrt(3). The rank and root values are exact, and the "
                + "universal channel statement includes singular inputs."),
            Entry("claim", "The proposed scalar necessity",
                Seq(Call("claim"), Leftrightarrow, Sp, Par(All("P,Q,R",
                    Implies(And(State(V("P")),State(V("Q")),Call("PD",V("R")),
                        Seq(Call("tr",V("R")),Eq,D(1)),Call("Good",V("P"),V("Q"),V("R"))),
                        Seq(Abs(Seq(Sq(U(V("R"),V("P"))),Minus,Sq(U(V("R"),V("Q"))))),
                            Le,D(1),Minus,Sq(U(V("P"),V("Q")))))))),
                "The proposed necessity ranges over every PSD density pair P,Q and every PD "
                + "trace-one reference R. It says that Good implies scalar balance. "
                + "No commutation assumption occurs in this proposed global assertion.", DescribeRole.Definition),
            Entry("result", "Scalar balance is not necessary",
                Seq(Neg, Sp, Call("claim")),
                "The faithful triple above refutes claim. Thus there exist three PD density matrices "
                + "with Good and strict failure of balance. The singular triple gives an additional "
                + "boundary example. This disproves the proposed necessity and the corresponding full "
                + "iff; it does not supply a replacement necessary-and-sufficient classification."))));
}
