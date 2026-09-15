using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class KrizekIntegralityGcdRecordRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/KrizekIntegralityGcdRecordRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/krizek2014a245786");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The seventh listed A245786 member is not an A216793 gcd record.",
        H("The OEIS A245786 Subsequence Conjecture"),
        Blocks(
            Describe.Lean(DescribeId.Create("a245786-member"),
                DeclarationHandle.Create(Prefix + "IsMember"),
                H("Membership in A245786"),
                StatementSource.FromAuthor(IsMemberFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Here sigma sub zero is tau, the divisor-count function, and sigma "
                        + "sub one is the divisor-sum function. Membership means that the "
                        + "displayed rational sum is an integer."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a216793-gcd-record"),
                DeclarationHandle.Create(Prefix + "IsRecord"),
                H("The A216793 gcd record predicate"),
                StatementSource.FromAuthor(IsRecordFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "At a natural n, the gcd of sigma sub one of n with n must be strictly "
                        + "larger than the corresponding gcd at every positive smaller m."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a245786-subsequence-conjecture"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Krizek's subsequence conjecture"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The conjecture says that every positive A245786 member is an A216793 "
                        + "gcd record."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a245786-subsequence-conjecture-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The conjecture fails at n = 275890944"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "At N = 275890944, tau(N) = 288 and sigma(N) = 919636480, so "
                        + "N/tau(N) + sigma(N)/N = 957958. Its gcd value is 91963648. "
                        + "For the smaller M = 142990848, sigma(M) = 571963392 = 4M and "
                        + "the gcd value is M itself. Thus N is a member but not a record."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a245786-integrality-gcd-record-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula IsMemberFormula()
    {
        var n = F.Id("n");
        var z = F.Id("z");
        var rationalSum = new Formula.Binary(
            new Formula.Fraction(
                Cast(n, Rationals()),
                Cast(SigmaAt(0, n), Rationals())),
            FormulaBinaryOperator.Add,
            new Formula.Fraction(
                Cast(SigmaAt(1, n), Rationals()),
                Cast(n, Rationals())));
        var existence = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("z"),
            Integers(),
            new Formula.Relation(rationalSum, FormulaRelationOperator.Equal, z));
        var definition = new Formula.Logic(
            Parenthesized(Call("IsMember", n)),
            FormulaLogicOperator.Iff,
            Parenthesized(existence));
        return Disp(Universal("n", Naturals(), definition));
    }

    private static Formula IsRecordFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var recordInequality = new Formula.Relation(
            Gcd(SigmaAt(1, m), m),
            FormulaRelationOperator.LessThan,
            Gcd(SigmaAt(1, n), n));
        var smallerPositive = Universal("m", Naturals(),
            Implies(
                Less(D(0), m),
                Implies(Less(m, n), recordInequality)));
        var definition = new Formula.Logic(
            Parenthesized(Call("IsRecord", n)),
            FormulaLogicOperator.Iff,
            Parenthesized(smallerPositive));
        return Disp(Universal("n", Naturals(), definition));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var quantified = Universal("n", Naturals(),
            Implies(
                Less(D(0), n),
                Implies(Call("IsMember", n), Call("IsRecord", n))));
        return Disp(new Formula.Logic(
            Parenthesized(F.Id("claim")),
            FormulaLogicOperator.Iff,
            Parenthesized(quantified)));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Universal(string variable, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            domain,
            body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula SigmaAt(byte index, Formula argument) =>
        new Formula.Apply(new Formula.Subscript(SigmaLower, D(index)), [argument]);

    private static Formula Gcd(Formula left, Formula right) =>
        new Formula.Apply(F.Gcd, [left, right]);

    private static Formula Cast(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() =>
        Seq(Mathbb, new Formula.LatexGroup([F.Id("N")]));

    private static Formula Rationals() =>
        Seq(Mathbb, new Formula.LatexGroup([F.Id("Q")]));

    private static Formula Integers() => new Formula.Integers();

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
