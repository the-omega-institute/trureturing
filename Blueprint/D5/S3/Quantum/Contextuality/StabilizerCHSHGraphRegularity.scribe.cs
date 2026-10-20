using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Contextuality;

internal sealed class StabilizerCHSHGraphRegularityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/howard2013stabilizercontextuality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every prime p, the qudit CHSH projectors are distinct trace-one idempotents and their orthogonality graph has degree (2p-1)(p-1).",
        H("Regularity of the qudit CHSH graph"), Blocks(
            Paragraph(Text(
                "Let p be prime. All matrices have complex entries, and local basis indices and "
                + "measurement labels lie in ZMod p. The map val takes the representative in "
                + "{0,...,p-1}. The symbol i is the imaginary unit. Write omega_p for windowRoot(p), "
                + "X for shiftMatrix(p), and Z for "
                + "clockMatrix(p), the phase, shift and clock of WindowRegister. Explicitly:")),
            new DocumentBlock.DisplayFormula(Disp(PhaseFormula())),
            new DocumentBlock.DisplayFormula(Disp(ShiftFormula())),
            new DocumentBlock.DisplayFormula(Disp(ClockFormula())),
            Paragraph(Text(
                "Matrix multiplication is the usual product, scalar multiplication acts entrywise, "
                + "and kronecker denotes the tensor product. Vertex labels are triples (j,k,a), "
                + "represented as (j,(k,a)). The graph joins distinct labels when the product of "
                + "their projectors is zero. These are the measurement operators and the "
                + "orthogonality convention of Howard, Brennan and Vala, Sections 2, 3 and 5.")),
            Node("alice", "Alice's measurement operators", "aliceOp", AliceFormula(),
                "Write A_j = aliceOp(p,j). For p=2 the operators are X and Y=iXZ. "
                + "For odd primes, A_j is the Weyl operator of slope j with phase offset j(j+1). "
                + "Every exponent of omega or Z is a natural-number representative of a residue."),
            Node("bob", "Bob's measurement operators", "bobOp", BobFormula(),
                "Write B_k = bobOp(p,k). For p=2 Bob also uses X and Y=iXZ. For odd primes "
                + "put h=2 inverse in ZMod p. The slope is hk and the phase offset is "
                + "h squared times (k squared plus 2k). Multiplication by h permutes the slopes."),
            Node("eigen", "The normalized spectral sum", "eigenProj", EigenFormula(),
                "The sum runs over Fin p, so the matrix powers range from zero to p-1. "
                + "The displayed definition applies to every complex matrix M of this size. "
                + "For the measurement operators it is the projector onto the eigenvalue "
                + "omega raised to a.val. It is the spectral sum of Section 2, Equation (Qproj), "
                + "with the normalization factor 1/p, which is omitted in the printed equation."),
            Node("vertex", "The projector at a vertex", "vertexProj", VertexFormula(),
                "The outcome labels a and b=-jk-a sum to -jk. The product projector is the "
                + "rank-one summand selected by the CHSH decomposition and Equation (SumRank1). "
                + "For p=2, -jk equals jk, so the same selection applies."),
            Node("claim", "Distinctness, projector laws and degree", "claim", ClaimFormula(),
                "The first conjunct asserts injectivity on all p cubed labels. The second "
                + "asserts trace one and idempotence for every projector. The third counts "
                + "all distinct labels whose projector product with a fixed vertex is zero. "
                + "It states the regularity conjecture of Section 5 together with the "
                + "distinctness and projector properties of its construction. The displayed "
                + "subtractions in the degree are in the natural numbers."),
            Describe.Lean(
                DescribeId.Create("stabilizer-chsh-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The qudit CHSH graph is regular"),
                StatementSource.FromAuthor(Disp(Named("claim"))),
                AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text(
                        "Fix a prime p and write omega=omega_p and chi(t)=omega raised to t.val. "
                        + "For odd p, let h be the inverse of 2. "
                        + "The chirp eigenvector of omega raised to c.val times X Z raised to s.val, "
                        + "with eigenvalue omega raised to a.val, has x component "
                        + "p raised to -1/2 times chi((c-a)x+s h x(x-1)). Successive phase "
                        + "differences give the Weyl operator. Summing its powers shows that the "
                        + "normalized spectral projector is the outer product of this vector "
                        + "with its conjugate. The vector has squared length one, so the projector "
                        + "has trace one and is idempotent. Alice uses s=j and c=j(j+1); Bob uses "
                        + "s=hk and c=h squared times (k squared plus 2k).")),
                    Paragraph(Text(
                        "Within a basis, character orthogonality gives zero overlap between "
                        + "different outcomes. For odd p, across different bases the overlap is a quadratic "
                        + "character sum. Multiply that sum by its conjugate and set x=y+t. "
                        + "For every nonzero t the remaining linear character in y sums to zero; "
                        + "the zero shift contributes p. After normalization the squared overlap "
                        + "is 1/p. At p=2 the normalized vectors have x components "
                        + "2 raised to -1/2 times chi(-a x), multiplied by 1 for setting zero "
                        + "and by i raised to x.val for setting one. Direct calculation gives "
                        + "the same orthogonality and squared overlap 1/2 for the X and Y bases.")),
                    Paragraph(Text(
                        "Write v=(j,k,a), w=(j',k',a'), b=-jk-a and b'=-j'k'-a'. "
                        + "A tensor product of matrices is zero exactly when a factor is zero. "
                        + "Consequently the adjacency rule is: j=j' and a differs from a', or "
                        + "k=k' and b differs from b'. For a fixed v, the first set has "
                        + "p(p-1) elements. The second also has p(p-1), because each choice of "
                        + "j' excludes exactly one a'. Their intersection has j'=j and k'=k, "
                        + "leaving p-1 choices of a'. Inclusion-exclusion therefore gives "
                        + "2p(p-1)-(p-1)=(2p-1)(p-1). Neither set contains v.")),
                    Paragraph(Text(
                        "For distinctness, take the trace of the product of two vertex "
                        + "projectors. It is the product of the two local squared overlaps. "
                        + "Each local value is 1 for equal settings and outcomes, 0 for equal "
                        + "settings and different outcomes, and 1/p for different settings. "
                        + "Equal vertex projectors have product trace one by trace one and "
                        + "idempotence. Since p is at least two, this forces both settings "
                        + "and Alice's outcome to agree, and hence the labels are identical. "
                        + "The graph thus has p cubed distinct vertices and the asserted degree."))),
                DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose) => Describe.Lean(
            DescribeId.Create("stabilizer-chsh-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula PhaseFormula() => PrimeScope(And(
        Equal(PhaseRoot(), Call("windowRoot", P)),
        Equal(PhaseRoot(), App(Exp, new Formula.Fraction(Mul(Mul(D(2), Pi), X("i")), Typed(P, C()))))));

    private static Formula ShiftFormula() => PrimeScope(All("x", R(), All("y", R(),
        Equal(App(Shift(), X("x"), X("y")),
            Cases(D(1), Equal(X("x"), Add(X("y"), D(1))), D(0))))));

    private static Formula ClockFormula() => PrimeScope(All("x", R(), All("y", R(),
        Equal(App(Clock(), X("x"), X("y")),
            Cases(Phase(X("x")), Equal(X("x"), X("y")), D(0))))));

    private static Formula AliceFormula() => PrimeScope(All("j", R(),
        Equal(Call("aliceOp", P, X("j")), Cases(
            Cases(Shift(), Equal(X("j"), D(0)), Mul(X("i"), Parenthesized(Mul(Shift(), Clock())))),
            Equal(P, D(2)),
            Mul(Phase(Mul(X("j"), Parenthesized(Add(X("j"), D(1))))),
                Parenthesized(Mul(Shift(), Pow(Clock(), Val(X("j"))))))))));

    private static Formula BobFormula()
    {
        Formula h = Inverse(Typed(D(2), R()));
        Formula offset = Mul(Pow(Parenthesized(h), D(2)),
            Parenthesized(Add(Pow(X("k"), D(2)), Mul(D(2), X("k")))));
        return PrimeScope(All("k", R(), Equal(Call("bobOp", P, X("k")), Cases(
            Cases(Shift(), Equal(X("k"), D(0)), Mul(X("i"), Parenthesized(Mul(Shift(), Clock())))),
            Equal(P, D(2)), Mul(Phase(offset),
                Parenthesized(Mul(Shift(), Pow(Clock(), Val(Mul(h, X("k")))))))))));
    }

    private static Formula EigenFormula() => PrimeScope(All("M", Matrices(), All("a", R(),
        Equal(Call("eigenProj", P, X("M"), X("a")),
            Mul(Inverse(Typed(P, C())), SumOver("m", Call("Fin", P),
                Mul(Phase(Mul(new Formula.Negate(Typed(Call("val", X("m")), R())), X("a"))),
                    Pow(X("M"), Call("val", X("m"))))))))));

    private static Formula VertexFormula() => PrimeScope(All("j", R(), All("k", R(), All("a", R(),
        Equal(Call("vertexProj", P, Parenthesized(Seq(X("j"), Comma, X("k"), Comma, X("a")))),
            Call("kronecker",
                Call("eigenProj", P, Call("aliceOp", P, X("j")), X("a")),
                Call("eigenProj", P, Call("bobOp", P, X("k")),
                    Sub(new Formula.Negate(Mul(X("j"), X("k"))), X("a")))))))));

    private static Formula ClaimFormula()
    {
        Formula projector = Call("vertexProj", P, X("v"));
        Formula laws = All("v", V(), And(Equal(Call("trace", projector), D(1)),
            Equal(Mul(projector, projector), projector)));
        Formula condition = And(NotEqual(X("w"), X("v")),
            Equal(Mul(projector, Call("vertexProj", P, X("w"))), D(0)));
        Formula neighbors = Call("filter", LambdaOf("w", V(), condition),
            Typed(Named("univ"), Call("Finset", V())));
        Formula count = All("v", V(), Equal(Call("card", neighbors),
            Mul(Parenthesized(Sub(Mul(D(2), P), D(1))), Parenthesized(Sub(P, D(1))))));
        return new Formula.Logic(Named("claim"), FormulaLogicOperator.Iff,
            Parenthesized(PrimeScope(And(Call("Injective", Call("vertexProj", P)), And(laws, count)))));
    }

    private static Formula P => X("p");
    private static Formula X(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula N() => Seq(Mathbb, Grp(X("N")));
    private static Formula C() => Seq(Mathbb, Grp(X("C")));
    private static Formula R() => Call("ZMod", P);
    private static Formula V() => Call("Prod", R(), Call("Prod", R(), R()));
    private static Formula Matrices() => Call("Matrix", R(), R(), C());
    private static Formula Shift() => Call("shiftMatrix", P);
    private static Formula Clock() => Call("clockMatrix", P);
    private static Formula Val(Formula value) => Call("val", value);
    private static Formula PhaseRoot() => new Formula.Subscript(Omega, P);
    private static Formula Phase(Formula value) => Pow(PhaseRoot(), Val(value));
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Inverse(Formula value) => Pow(value, new Formula.Negate(D(1)));
    private static Formula Cases(Formula yes, Formula condition, Formula no) =>
        Seq(Begin, Grp(X("cases")), yes, Amp, condition, RowBreak,
            no, Amp, Seq(F.Text, Grp(X("otherwise"))), End, Grp(X("cases")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula PrimeScope(Formula body) => All("p", N(),
        Seq(OpenBracket, Call("Fact", Call("Prime", P)), CloseBracket, Sp, Parenthesized(body)));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
