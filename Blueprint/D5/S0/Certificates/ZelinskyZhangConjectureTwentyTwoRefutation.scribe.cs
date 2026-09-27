using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class ZelinskyZhangConjectureTwentyTwoRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/ZelinskyZhangConjectureTwentyTwoRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/zelinskyzhang2025klprimitive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integer 6 refutes a published lower bound for a divisor-weighted logarithmic sum.",
        H("Zelinsky and Zhang's Conjecture 22"),
        Blocks(
            Node("divisor-weighted-logarithmic-sum", "The divisor-weighted sum",
                VFormula(),
                "For every natural n, v(n) sums over exactly the divisors d of n with "
                    + "d greater than one. Each summand is 1/d times the natural logarithm "
                    + "of (card(divisors(n)) - 1)/d, with all quotients taken in the reals.",
                "v", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("conjecture-twenty-two", "Conjecture 22",
                ClaimFormula(),
                "For every positive natural n outside exactly the twelve displayed exclusions, "
                    + "the conjecture bounds v(n) below by the reciprocal square of Nat.minFac(n). "
                    + "No further condition on n is imposed.",
                "claim", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("conjecture-twenty-two-refuted", "Conjecture 22 is false",
                ResultFormula(),
                "At n = 6 the retained divisors are 2, 3, and 6, while Nat.minFac(6) = 2. "
                    + "The sum reduces to one half times log(3/2) plus one sixth times log(1/2). "
                    + "The inequalities log(3/2) < 1/2 and log(1/2) < 0 make this value strictly "
                    + "less than 1/4, contradicting the asserted lower bound.",
                "result", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "zelinsky-zhang-conjecture-22-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string id,
        string title,
        Formula formula,
        string prose,
        string declaration,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula VFormula()
    {
        var n = F.Id("n");
        var d = F.Id("d");
        var divisors = QualifiedCall("Nat", "divisors", n);
        var retained = QualifiedCall("Finset", "filter", divisors,
            Lambda(d, Less(D(1), d)));
        var divisorCount = Subtract(Call("card", divisors), D(1));
        var ratio = new Formula.Fraction(
            Coerce(divisorCount, Reals()), Coerce(d, Reals()));
        var summand = Multiply(
            new Formula.Fraction(D(1), Coerce(d, Reals())),
            QualifiedCall("Real", "log", ratio));
        var sum = Seq(
            new Formula.Subscript(Sum, Seq(d, Sp, InMacro, Sp, retained)),
            Sp,
            Parenthesized(summand));
        return Disp(Universal("n", Equal(Call("v", n), sum)));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var exclusions = Seq(OpenBrace,
            D(1), Comma, Sp, D(1, 2), Comma, Sp, D(2, 4), Comma, Sp,
            D(3, 0), Comma, Sp, D(3, 6), Comma, Sp, D(4, 8), Comma, Sp,
            D(6, 0), Comma, Sp, D(7, 2), Comma, Sp, D(1, 2, 0), Comma, Sp,
            D(1, 8, 0), Comma, Sp, D(2, 4, 0), Comma, Sp, D(3, 6, 0),
            CloseBrace);
        var outsideExclusions = new Formula.Not(
            Seq(n, Sp, InMacro, Sp, exclusions));
        var lowerBound = new Formula.Fraction(
            D(1),
            new Formula.Power(
                Coerce(QualifiedCall("Nat", "minFac", n), Reals()), D(2)));
        var conclusion = LessThanOrEqual(lowerBound, Call("v", n));
        var quantified = Universal("n", Implies(
            Less(D(0), n),
            Implies(outsideExclusions, conclusion)));
        return Disp(Iff(F.Id("claim"), quantified));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Universal(string variable, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            Naturals(),
            body);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula QualifiedCall(
        string prefix,
        string name,
        params Formula[] arguments) =>
        new Formula.Apply(Seq(F.Id(prefix), Dot, F.Id(name)), [.. arguments]);

    private static Formula Lambda(Formula variable, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, variable, Sp, Mapsto, Sp, body));

    private static Formula Coerce(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Reals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Real"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
