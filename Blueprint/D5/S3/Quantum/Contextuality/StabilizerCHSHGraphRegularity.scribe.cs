using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Contextuality;

internal sealed class StabilizerCHSHGraphRegularityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Contextuality/StabilizerCHSHGraphRegularity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every prime p, the normalized stabilizer projectors of the qudit CHSH construction are distinct trace-one idempotents and their orthogonality graph has degree (2p-1)(p-1).",
        H("Regularity of the qudit CHSH graph"), Blocks(
            Paragraph(Text(
                "All matrices have complex entries. The local indices and measurement labels belong "
                + "to ZMod p, and val takes the representative from zero through p-1. The product "
                + "of matrices is the usual matrix product; kronecker is its tensor product. "
                + "The graph joins distinct vertices exactly when the product of their projectors "
                + "vanishes. The operators are the ones in Howard, Brennan and Vala, Quantum "
                + "Contextuality with Stabilizer States, Entropy 15 (2013), Section 5. "
                + "The spectral sums include the factor 1/p.")),
            Node("omega", "The primitive phase", "omega", All("p", N(),
                Eq(L("omega", P), Q("D5", "S3", "Observer", "WindowRegister", "windowRoot", P))),
                "The phase is exp(2 pi i/p), as supplied by the finite cyclic window register."),
            Node("shift", "The cyclic shift", "shiftX", PrimeScope(All("x", R(), All("y", R(),
                Eq(App(L("shiftX", P), X("x"), X("y")),
                    Ite(Eq(X("x"), Add(X("y"), D(1))), D(1), D(0)))))),
                "The shift sends the basis vector at y to the basis vector at y+1."),
            Node("clock", "The diagonal clock", "clockZ", PrimeScope(All("x", R(), All("y", R(),
                Eq(App(L("clockZ", P), X("x"), X("y")),
                    Ite(Eq(X("x"), X("y")), Phase(X("x")), D(0)))))),
                "The clock multiplies the basis vector at x by the phase with exponent x.val."),
            Node("alice", "Alice's measurement operators", "aliceOp", AliceFormula(),
                "For p=2 the two operators are X and Y=iXZ. For odd primes the setting j "
                + "has slope j and phase offset j(j+1)."),
            Node("bob", "Bob's measurement operators", "bobOp", BobFormula(),
                "For p=2 Bob also uses X and Y. For odd primes the inverse of two is taken "
                + "in ZMod p, so multiplication by it permutes the measurement slopes."),
            Node("eigen", "The normalized spectral sum", "eigenProj", EigenFormula(),
                "The sum over Fin p enumerates one complete period of powers of the operator. "
                + "For Alice's and Bob's operators, the label a selects the eigenvalue omega raised to a.val."),
            Node("vertex", "The product projector at a vertex", "vertexProj", VertexFormula(),
                "A vertex is a triple (j,k,a). Its second outcome is b=-jk-a, so the two "
                + "local eigenvalue labels sum to -jk. This also gives jk when p=2."),
            Node("claim", "Distinct projectors and the common degree", "claim", ClaimFormula(),
                "Injectivity identifies the p cubed labels with distinct projectors. Each "
                + "projector has trace one and squares to itself. The final clause counts "
                + "every distinct vertex with zero projector product."),
            Describe.Lean(
                DescribeId.Create("stabilizer-chsh-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The qudit CHSH graph is regular"), StatementSource.FromAuthor(Disp(L("claim"))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text(
                        "For odd p put s=2 inverse in ZMod p. A Weyl operator with slope j "
                        + "and phase offset c is a cyclic shift twisted by the unit phases "
                        + "chi(c x+j s x(x-1)). Its m-th power has one nonzero entry in each "
                        + "column, at row y+m, with phase given by the difference of the two "
                        + "endpoint exponents. The normalized spectral sum is therefore "
                        + "1/p times the outer product of the phases chi((c-a)x+j s x(x-1)) "
                        + "with their conjugates. Their squared lengths sum to p, which gives "
                        + "trace one and idempotence.")),
                    Paragraph(Text(
                        "Within one measurement basis, character orthogonality makes distinct "
                        + "labels orthogonal. For two different slopes, multiply the quadratic "
                        + "character sum by its conjugate and write x=y+h. The sum over y "
                        + "vanishes for every nonzero h. Only h=0 remains, giving p and hence "
                        + "squared normalized overlap 1/p. The X and Y bases at p=2 satisfy "
                        + "the same overlap formulas by explicit calculation.")),
                    Paragraph(Text(
                        "A product of two rank-one projectors vanishes exactly when their "
                        + "overlap vanishes. Kronecker multiplication then shows that two "
                        + "vertices are adjacent exactly when Alice's settings agree and her "
                        + "outcomes differ, or Bob's settings agree and his outcomes differ. "
                        + "For a fixed vertex, matching Alice settings give p(p-1) neighbors. "
                        + "For each of the other p-1 Alice settings, Bob's setting must agree "
                        + "and exactly one outcome is excluded, giving another (p-1) squared "
                        + "neighbors. Their sum is (2p-1)(p-1).")),
                    Paragraph(Text(
                        "The trace of the product of two vertex projectors is the product of "
                        + "the two local squared overlaps. A different basis contributes 1/p, "
                        + "which is strictly below one, and a different outcome within a basis "
                        + "contributes zero. Equal vertex projectors have product trace one, "
                        + "so their two settings and Alice's outcome all agree. This proves "
                        + "injectivity."))), DescribeRole.Theorem)
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose) => Describe.Lean(
            DescribeId.Create("stabilizer-chsh-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula AliceFormula() => PrimeScope(All("j", R(),
        Eq(L("aliceOp", P, X("j")), Ite(Eq(P, D(2)),
            Ite(Eq(X("j"), D(0)), L("shiftX", P),
                Scalar(Q("Complex", "I"), Mul(L("shiftX", P), L("clockZ", P)))),
            Scalar(Phase(Mul(X("j"), Add(X("j"), D(1)))),
                Mul(L("shiftX", P), Pow(L("clockZ", P), Q("ZMod", "val", X("j")))))))));

    private static Formula BobFormula()
    {
        Formula h = Q("Inv", "inv", Typed(D(2), R()));
        Formula phase = Mul(Pow(h, D(2)), Add(Pow(X("k"), D(2)), Mul(D(2), X("k"))));
        return PrimeScope(All("k", R(), Eq(L("bobOp", P, X("k")), Ite(Eq(P, D(2)),
            Ite(Eq(X("k"), D(0)), L("shiftX", P),
                Scalar(Q("Complex", "I"), Mul(L("shiftX", P), L("clockZ", P)))),
            Scalar(Phase(phase), Mul(L("shiftX", P),
                Pow(L("clockZ", P), Q("ZMod", "val", Mul(h, X("k"))))))))));
    }

    private static Formula EigenFormula() => PrimeScope(All("M", Matrix(R()), All("a", R(),
        Eq(L("eigenProj", P, X("M"), X("a")), Scalar(Q("Inv", "inv", Typed(P, C())),
            SumOver("m", Q("Fin", P), Scalar(
                Phase(Mul(Negate(Typed(Q("Fin", "val", X("m")), R())), X("a"))),
                Pow(X("M"), Q("Fin", "val", X("m"))))))))));

    private static Formula VertexFormula() => PrimeScope(All("v", V(),
        Eq(L("vertexProj", P, X("v")), Q("Matrix", "kronecker",
            L("eigenProj", P, L("aliceOp", P, First(X("v"))), Second(Second(X("v")))),
            L("eigenProj", P, L("bobOp", P, First(Second(X("v")))),
                Sub(Mul(Negate(First(X("v"))), First(Second(X("v")))),
                    Second(Second(X("v")))))))));

    private static Formula ClaimFormula()
    {
        Formula projector = L("vertexProj", P, X("v"));
        Formula laws = All("v", V(), And(Eq(Q("Matrix", "trace", projector), D(1)),
            Eq(Mul(projector, projector), projector)));
        Formula condition = And(Ne(X("w"), X("v")),
            Eq(Mul(projector, L("vertexProj", P, X("w"))), D(0)));
        Formula neighbors = Q("Finset", "filter", LambdaOf("w", V(), condition),
            Typed(Q("Finset", "univ"), Q("Finset", V())));
        Formula count = All("v", V(), Eq(Q("Finset", "card", neighbors),
            Mul(Sub(Mul(D(2), P), D(1)), Sub(P, D(1)))));
        return Iff(L("claim"), PrimeScope(And(Q("Function", "Injective", L("vertexProj", P)),
            And(laws, count))));
    }

    private static Formula P => X("p");
    private static Formula X(string name) => F.Id(name);
    private static Formula Q(string name, params Formula[] args) => App(Name(name), args);
    private static Formula Q(string a, string b, params Formula[] args) => App(Name(a, b), args);
    private static Formula Q(string a, string b, string c, string d, string e, params Formula[] args) =>
        App(Name(a, b, c, d, e), args);
    private static Formula Name(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula L(string name, params Formula[] args) =>
        App(Name("D5", "S3", "Quantum", "Contextuality", "StabilizerCHSHGraphRegularity", name), args);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula f, Formula t) => Par(Seq(f, Colon, Sp, t));
    private static Formula N() => Seq(Mathbb, Grp(X("N")));
    private static Formula C() => Seq(Mathbb, Grp(X("C")));
    private static Formula R() => Q("ZMod", P);
    private static Formula V() => Q("Prod", R(), Q("Prod", R(), R()));
    private static Formula Matrix(Formula index) => Q("Matrix", index, index, C());
    private static Formula First(Formula f) => Q("Prod", "fst", f);
    private static Formula Second(Formula f) => Q("Prod", "snd", f);
    private static Formula Phase(Formula f) => Pow(L("omega", P), Q("ZMod", "val", f));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Scalar(Formula a, Formula b) => Q("HSMul", "hSMul", a, b);
    private static Formula Ite(Formula c, Formula t, Formula e) => Q("ite", c, t, e);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Par(body));
    private static Formula PrimeScope(Formula body) => All("p", N(),
        Seq(OpenBracket, Q("Fact", Q("Nat", "Prime", P)), CloseBracket, Sp, Par(body)));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Par(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Par(body));
    private static Formula Negate(Formula f) => Q("Neg", "neg", f);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => Seq(Par(a), Sp, Neq, Sp, Par(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
}
