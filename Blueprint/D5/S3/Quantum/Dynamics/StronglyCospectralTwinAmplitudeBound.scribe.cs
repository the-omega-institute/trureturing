using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class StronglyCospectralTwinAmplitudeBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/StronglyCospectralTwinAmplitudeBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/meaghermonterdenguyen2026sedentary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every odd integer relation among the supported adjacency gaps of strongly cospectral "
        + "twins gives an explicit positive floor for their return amplitudes.",
        H("Return amplitudes of strongly cospectral twins"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strongly-cospectral-twins-eigenvalue"),
                DeclarationHandle.Create(Prefix + "twinEigenvalue"),
                H("The twin eigenvalue"),
                StatementSource.FromAuthor(Disp(GraphBinders(And(
                    Arrow(Adj(X("u"), X("v")), Equal(TwinEigenvalue(), new Formula.Negate(D(1)))),
                    Arrow(new Formula.Not(Adj(X("u"), X("v"))), Equal(TwinEigenvalue(), D(0))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The difference of the two vertex basis vectors has "
                    + "eigenvalue minus one for adjacent twins and zero for nonadjacent twins."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("strongly-cospectral-twins-remaining-support"),
                DeclarationHandle.Create(Prefix + "remainingSupport"),
                H("The remaining adjacency support"),
                StatementSource.FromAuthor(Disp(GraphBinders(All(X("e"), Reals(),
                    Equivalent(Member(X("e"), Support()), And(
                        Member(X("e"), Call("spectrum", X("G"))),
                        And(Unequal(X("e"), TwinEigenvalue()), Less(D(0), Weight(X("e")))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The finite support contains the distinct eigenvalues "
                    + "whose projector diagonals at the first twin are positive, excluding the twin eigenvalue. "
                    + "Each projector combines all basis vectors of its eigenspace."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("strongly-cospectral-twins-amplitude-bound"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The odd-relation return-amplitude bound"),
                StatementSource.FromAuthor(Disp(Result())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "In the formula, theta and J denote the two definitions above. E(e) denotes "
                    + "the orthogonal projector onto the full eigenspace of the adjacency matrix A of G, "
                    + "and single(u) is the u-th coordinate vector. The weight a(G,u,e) is E(G,e) at entry "
                    + "(u,u). U(G,t,u,u) denotes the (u,u) entry of exp(itA). For distinct strongly cospectral twins "
                    + "in a finite simple graph with adjacency matrix A, "
                    + "the projector at the twin eigenvalue sends the first vertex vector to half the "
                    + "difference of the two vectors, including when the eigenvalue is repeated. "
                    + "The remaining weights are positive and sum to one half. Their weighted phase "
                    + "sum together with the twin contribution gives the diagonal of exp(itA). "
                    + "The projector diagonals agree at both twins, so their complex return amplitudes agree. "
                    + "The positive-time orbit closure recovers the qualitative equivalence in "
                    + "Theorem 2.2(2) of Meagher, Monterde and Nguyen. On the orbit, an odd zero-gap relation has "
                    + "character one, while its character at the constant phase minus one is minus one. "
                    + "The weighted character chord bound gives a squared displacement of four. "
                    + "The total weighted squared coordinate chord is twice the real part of the "
                    + "dephased amplitude. Each such relation gives the quantitative floor 2/D for every real time, "
                    + "where D is the sum of the squared integer coefficients divided by their projector weights. "
                    + "The gaps may be irrational, and the twins may be adjacent or nonadjacent.")),
                    Paragraph(Text("The doubled independent fibers of the five-cycle give nonadjacent "
                    + "strongly cospectral twins. The pair differences have eigenvalue zero, and the "
                    + "pair-constant restriction is twice the cycle adjacency matrix. The nonzero gaps "
                    + "are 4, minus one plus the square root of five, and minus one minus the square root "
                    + "of five, with respective projector weights 1/10, 1/5, and 1/5. The irrational gap "
                    + "ratio rules out a positive period. The relation (1, 2, 2) gives D = 50 and a "
                    + "certified floor of 1/25."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("meagher-monterde-nguyen-2026-strongly-cospectral-twins"),
                    ResolutionKind.Proved))),
        []));

    private static Formula Result()
    {
        var u = X("u");
        var v = X("v");
        var e = X("e");
        var t = X("t");
        var c = X("C");
        var half = new Formula.Fraction(D(1), D(2));
        var relations = new Formula.TypeArrow(Support(), Field("Z"));
        var projection = Equal(Multiply(Call("E", X("G"), TwinEigenvalue()), Call("single", u)),
            Multiply(half, Parens(Subtract(Call("single", u), Call("single", v)))));
        var twins = All(X("x"), Vertices(), Arrow(
            And(Unequal(X("x"), u), Unequal(X("x"), v)), Equivalent(Adj(X("x"), u), Adj(X("x"), v))));
        var positiveFloor = Some(c, Reals(), And(Less(D(0), c),
            All(t, Reals(), Arrow(Less(D(0), t), AtMost(c, Amplitude(t))))));
        var denominator = SumOnSupport(new Formula.Fraction(new Formula.Power(RealCoefficient(e), D(2)), Weight(e)));
        var quantitative = All(Ell, relations, Arrow(Certificate(), And(Less(D(0), denominator),
            All(t, Reals(), AtMost(new Formula.Fraction(D(2), denominator), Amplitude(t))))));
        var mass = And(Equal(Weight(TwinEigenvalue()), half), And(
            All(e, Reals(), Arrow(Member(e, Support()), Less(D(0), Weight(e)))),
            Equal(SumOnSupport(Weight(e)), half)));
        var equalAmplitudes = All(t, Reals(), Equal(Call("U", X("G"), t, u, u), Call("U", X("G"), t, v, v)));

        return GraphBinders(Arrow(And(Unequal(u, v), And(twins, Call("StronglyCospectral", X("G"), u, v))),
            And(projection, And(mass, And(equalAmplitudes,
                And(Equivalent(positiveFloor, Some(Ell, relations, Certificate())), quantitative))))));
    }

    private static Formula Certificate() => And(
        Equal(SumOnSupport(Multiply(RealCoefficient(X("e")), Parens(Subtract(X("e"), TwinEigenvalue())))), D(0)),
        Call("Odd", SumOnSupport(new Formula.Apply(Ell, [X("e")]))));

    private static Formula GraphBinders(Formula body) => All(X("n"), Field("N"),
        All(X("G"), Call("SimpleGraph", Vertices()), Seq(OpenBracket,
            Call("DecidableRel", Call("Adj", X("G"))), CloseBracket, Sp,
            All(X("u"), Vertices(), All(X("v"), Vertices(), body)))));

    private static Formula Support() => Call("J", X("G"), X("u"), X("v"));
    private static Formula TwinEigenvalue() => new Formula.Apply(Theta, [X("G"), X("u"), X("v")]);
    private static Formula Vertices() => Call("Fin", X("n"));
    private static Formula Weight(Formula e) => Call("a", X("G"), X("u"), e);
    private static Formula Adj(Formula x, Formula y) => Call("Adj", X("G"), x, y);
    private static Formula Amplitude(Formula t) => new Formula.Norm(Call("U", X("G"), t, X("u"), X("u")));
    private static Formula RealCoefficient(Formula e) => Typed(new Formula.Apply(Ell, [e]), Reals());
    private static Formula SumOnSupport(Formula body) => Seq(Sum, Underscore,
        Grp(Seq(X("e"), Sp, InMacro, Sp, Support())), Sp, body);

    private static Formula X(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(X(name))), [.. args]);
    private static Formula Field(string name) => Seq(Mathbb, Grp(X(name)));
    private static Formula Reals() => Field("R");
    private static Formula Parens(Formula body) => Seq(Open, body, Close);
    private static Formula Typed(Formula name, Formula type) => Parens(Seq(name, Colon, Sp, type));
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp, Parens(body));
    private static Formula Some(Formula name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(name, type), Comma, Sp, Parens(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parens(domain), Parens(codomain));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parens(left), FormulaLogicOperator.And, Parens(right));
    private static Formula Equivalent(Formula left, Formula right) =>
        new Formula.Logic(Parens(left), FormulaLogicOperator.Iff, Parens(right));
    private static Formula Unequal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
}
