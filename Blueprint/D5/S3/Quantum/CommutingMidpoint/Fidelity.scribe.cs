using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.CommutingMidpoint;

internal sealed class FidelityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/CommutingMidpoint/Fidelity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/marajaeizhang2026generalizedv3");
    private static Formula V(string name) => Seq(Sp, F.Id(name));
    private static Formula Sq(Formula a) => Seq(a, Caret, Grp(D(2)));
    private static Formula U(Formula a, Formula b) => Call("U", a, b);
    private static Formula Hf(Formula a, Formula b) => Call("H", a, b);
    private static Formula Fr(Formula r, Formula a, Formula b) => Call("F", r, a, b);
    private static Formula Br(Formula r, Formula a, Formula b) => Call("B", r, a, b);
    private static Formula Half => Seq(Frac, Grp(D(1)), Grp(D(2)));
    private static Formula SqrtOf(Formula a) => Seq(Sqrt, Grp(a));
    private static Formula ReOf(Formula a) => Seq(Re, Open, a, Close);
    private static Formula Names(string names) => Seq(System.Linq.Enumerable.ToArray(
        System.Linq.Enumerable.SelectMany(names.Split(','),
            (name, index) => index == 0 ? new[] { V(name) } : new[] { Comma, Sp, V(name) })));
    private static Formula RealType => Seq(Mathbb, Grp(V("R")));
    private static Formula MatrixType => Call("Matrix", Call("Fin", D(2)), Call("Fin", D(2)), Seq(Mathbb, Grp(V("C"))));
    private static Formula VectorType => Call("EuclideanSpace", RealType, Call("Fin", D(3)));
    private static Formula Bound(string names, Formula type) => Seq(Open, Names(names), Colon, type, Close);
    private static Formula For(Formula binders, Formula body) => Seq(Forall, Sp, binders, Comma, Quad, body);
    private static Formula All(string names, Formula conclusion) => For(Seq(System.Linq.Enumerable.ToArray(
        System.Linq.Enumerable.Select(names.Split(','), name => Bound(name,
            name is "d" or "e" ? VectorType :
            name is "P" or "Q" or "R" or "S" or "V" or "T" or "A" or "B" ? MatrixType :
            name == "Phi" ? Call("ComplexLinearMap", MatrixType, MatrixType) : RealType)))), conclusion);
    private static Formula And(params Formula[] clauses) => Seq(System.Linq.Enumerable.ToArray(
        System.Linq.Enumerable.SelectMany(clauses, (clause, index) => index == 0 ?
            new[] { clause } : new[] { Land, Sp, clause })));
    private static Formula State(Formula a) => And(Call("PSD", a), Seq(Call("tr", a), Eq, D(1)));
    private static DocumentBlock Entry(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create("commuting-midpoint-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Matrix root-fidelity identities and binary preparation estimates used by commuting midpoint contraction.",
        H("Root Fidelity and Binary Preparation"),
        Blocks(
            Paragraph(Text("These matrix identities and preparation estimates are the foundation of commuting qubit midpoint contraction. The weighted-root norm identity has arbitrary finite decidable indices and no trace normalization. The qubit quotient allows singular density inputs; only its reference is positive definite. The half-order estimate needs no trace normalization on its second PSD matrix.")),
            Entry("rootFidelity", "Root fidelity",
                For(Seq(Bound("n",V("Type")), OpenBracket,Call("Fintype",V("n")),CloseBracket,
                    OpenBracket,Call("DecidableEq",V("n")),CloseBracket,
                    Bound("S,T",Call("Matrix",V("n"),V("n"),Seq(Mathbb,Grp(V("C")))))),
                    Seq(U(V("S"),V("T")),Eq,ReOf(Call("tr",SqrtOf(Seq(SqrtOf(V("S")),V("T"),SqrtOf(V("S")))))))),
                "For matrices on any finite decidable index type, U(S,T) is the real trace of "
                + "sqrt(sqrt(S) T sqrt(S)). This is root fidelity, without a final square.", DescribeRole.Definition, true),
            Entry("bures_eq_weighted_root_norm_sq", "The weighted-root norm identity",
                For(Seq(Bound("n",V("Type")), OpenBracket,Call("Fintype",V("n")),CloseBracket,
                    OpenBracket,Call("DecidableEq",V("n")),CloseBracket,
                    Bound("S,V,T",Call("Matrix",V("n"),V("n"),Seq(Mathbb,Grp(V("C")))))),
                    Seq(And(Call("PSD",V("S")),Call("PSD",V("V")),Call("PD",V("T"))),Rightarrow,Sp,
                        Br(V("T"),V("S"),V("V")),Eq,Sq(Seq(Vert,Sp,Call("inv",SqrtOf(V("T"))),Open,
                        SqrtOf(Seq(SqrtOf(V("T")),V("S"),SqrtOf(V("T")))),Minus,
                        SqrtOf(Seq(SqrtOf(V("T")),V("V"),SqrtOf(V("T")))),Close,Vert)))),
                "For every finite decidable index type, PSD S,V and PD T, B(T,S,V) equals the "
                + "squared Frobenius norm displayed above. No trace normalization is required. "
                + "Expand the norm using the Frobenius trace identity. The diagonal terms are tr(S), "
                + "tr(V); the two cross terms have equal real parts because they are conjugate traces. "
                + "This proves nonnegativity even for singular S or V.", literature: true),
            Entry("qubit_root_fidelity_quotient", "The actual qubit quotient",
                All("S,V,T", Seq(And(State(V("S")),State(V("V")),Call("PD",V("T")),
                    Seq(Call("tr",V("T")),Eq,D(1))),Rightarrow,Sp,
                    And(Seq(D(0),Lt,U(V("T"),V("S"))),Seq(D(0),Lt,U(V("T"),V("V"))),
                    Seq(ReOf(Fr(V("T"),V("S"),V("V"))),Eq,Frac,
                        Grp(Sq(U(V("T"),V("S"))),Plus,Sq(U(V("T"),V("V"))),Plus,Sq(U(V("S"),V("V"))),Minus,D(1)),
                        Grp(D(2),U(V("T"),V("S")),U(V("T"),V("V"))))))),
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
                All("S,T", Seq(State(V("S")), Land, Call("PSD", V("T")), Land,
                    Call("PSD", Seq(V("T"), Minus, Half, V("S"))), Rightarrow,
                    Half, Le, Sq(U(V("T"), V("S"))))),
                "For every density S and PSD T with T-S/2 PSD, U(T,S) squared is at least one half. "
                + "Congruence by sqrt(S), operator monotonicity of sqrt, and positivity of trace give "
                + "U(S,T)>=sqrt(1/2). The actual qubit formula proves symmetry U(S,T)=U(T,S). "
                + "There is no invertibility assumption on S and no trace-one requirement on T."),
            Entry("classical_binary_preparation_fidelity", "Classical binary preparation",
                All("p,q,x,y", Seq(And(Seq(D(0),Le,V("p"),Le,D(1)),Seq(D(0),Le,V("q"),Le,D(1)),
                    Seq(D(0),Le,V("x"),Le,D(1)),Seq(D(0),Le,V("y"),Le,D(1))), Rightarrow,Sp,
                    Hf(V("p"), V("q")), Le,
                    Hf(Seq(V("p"), V("x"), Plus, Open, D(1), Minus, V("p"), Close, V("y")),
                        Seq(V("q"), V("x"), Plus, Open, D(1), Minus, V("q"), Close, V("y"))))),
                "For all p,q,x,y in the closed unit interval, preparing binary probabilities x,y "
                + "with mixing probabilities p,q cannot decrease H. Apply Cauchy-Schwarz to each "
                + "coordinate and add the two inequalities. Zero probabilities are included."))));
}
