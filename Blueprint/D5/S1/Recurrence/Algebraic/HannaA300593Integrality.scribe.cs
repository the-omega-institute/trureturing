using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaA300593IntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaA300593Integrality.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/hanna2018a300593");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The square-exponential equations with cubic multipliers define a unique rational ordinary series with integral coefficients.",
        H("Hanna A300593 ordinary integrality"), Blocks(
            Node("IsSource", "The normalized rational ordinary series",
                All("F", Series(), Iffn(Call("IsSource", V("F")), SourceBody(V("F")))),
                "The constant coefficient of F is zero. For every positive natural n, the scalar inside the " +
                "formal exponential is the rational square of n and the right-hand multiplier is the rational cube of n. " +
                "Both extractions are ordinary coefficients. The formal exponential of tF is the substitution " +
                "of C(t)F into PowerSeries.exp over the rationals.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsCompanion", "The normalized A300592 companion",
                All("B", Series(), Iffn(Call("IsCompanion", V("B")), CompanionBody(V("B")))),
                "The companion B has constant coefficient one. Its natural power n squared satisfies an ordinary " +
                "coefficient equation with multiplier n cubed at every positive natural n. The exponential " +
                "generating function entries of B are eCoeff(B,r), the ordinary coefficient in degree r multiplied by r!.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "All-degree integrality and the exponential companion", ResultBody(),
                "Triangular existence and uniqueness apply to the separate scalar functions n squared and n cubed. " +
                "Strong induction takes the lower ordinary coefficients as integers, forms their strict prefix P, " +
                "and transfers all lower equations to P by coefficient agreement. " +
                "For a prime coprime to n, MarkedAssemblyExtraMarker treats two ambient markers on every block " +
                "and an extra ambient marker on the pointed object. Its signed fixed-point sums give the full " +
                "Sylow-order divisibility of the factorial-weighted residual. The coefficient at degree n is " +
                "the negative residual divided by n squared, a local unit. For a prime dividing n, write s for the " +
                "valuation of n. The exponential prefix estimate bounds the valuation of n times the previous " +
                "exponential coefficient below by 3s and that of the current exponential coefficient divided " +
                "by n squared below by 2s minus 1, whenever the respective terms are nonzero. Thus a prime " +
                "dividing a reduced denominator is ruled out in either case. The normalization covers degree zero. " +
                "The formal power law holds for every natural exponent index, including zero. The formal " +
                "exponential and logarithm give both companion correspondences. Dividing the EGF entries by " +
                "their factorials reconstructs B in every degree.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hanna-a300593"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula statement, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hannaa300593-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(statement)),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Series() => Call("PowerSeries", Q());
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) =>
        Seq(a, Sp, Le, Sp, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Iffn(Formula a, Formula b) =>
        Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Square(Formula a) => new Formula.Power(Par(a), D(2));
    private static Formula Cube(Formula a) => new Formula.Power(Par(a), D(3));
    private static Formula Cast(Formula a) => Par(Seq(a, Colon, Sp, Q()));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Unique(string name, Formula type, System.Func<Formula, Formula> property) =>
        Ex(name, type, And(property(V(name)),
            All("G", type, Imp(property(V("G")), Eqn(V("G"), V(name))))));
    private static Formula E(Formula f) => Call("expSeries", D(1), f);
    private static Formula Coeff(Formula n, Formula f) => Call("coeff", n, f);
    private static Formula SourceBody(Formula f) =>
        And(Eqn(Call("constantCoeff", f), D(0)), All("n", N(),
            Imp(Leq(D(1), V("n")), Eqn(
                Coeff(V("n"), Call("expSeries", Square(Cast(V("n"))), f)),
                Mul(Cube(Cast(V("n"))), Coeff(Sub(V("n"), D(1)),
                    Call("expSeries", Square(Cast(V("n"))), f)))))));
    private static Formula CompanionBody(Formula b) =>
        And(Eqn(Call("constantCoeff", b), D(1)), All("n", N(),
            Imp(Leq(D(1), V("n")), Eqn(
                Coeff(V("n"), new Formula.Power(Par(b), Square(V("n")))),
                Mul(Cube(Cast(V("n"))), Coeff(Sub(V("n"), D(1)),
                    new Formula.Power(Par(b), Square(V("n")))))))));
    private static Formula ResultBody() => And(
        Unique("F", Series(), f => Call("IsSource", f)),
        All("F", Series(), Imp(Call("IsSource", V("F")),
            And(All("m", N(), Ex("z", Z(), Eqn(Coeff(V("m"), V("F")), Cast(V("z"))))),
                And(Call("IsCompanion", E(V("F"))),
                    And(Eqn(Call("logOf", E(V("F"))), V("F")),
                        And(All("n", N(), Eqn(Call("expSeries", Square(Cast(V("n"))), V("F")),
                                new Formula.Power(Par(E(V("F"))), Square(V("n"))))),
                            And(All("B", Series(), Imp(Call("IsCompanion", V("B")),
                                    And(Eqn(V("B"), E(V("F"))), Eqn(Call("logOf", V("B")), V("F"))))),
                                EgfBody(V("F"))))))))));
    private static Formula EgfBody(Formula f) =>
        Eqn(Call("mk", Par(Seq(V("fun"), Sp, V("r"), Colon, Sp, N(), Sp, Mapsto, Sp,
            new Formula.Fraction(Call("eCoeff", E(f), V("r")), Cast(Call("factorial", V("r"))))))), E(f));
}
