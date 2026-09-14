using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class KrizekDivisorCountPowerRatioDenominatorSquareDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/KrizekDivisorCountPowerRatioDenominatorSquare.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/krizek2018a302975");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every reduced denominator in OEIS A302975 is a square.",
        H("The OEIS A302975 Denominator-Square Conjecture"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a302975-denominator"),
                DeclarationHandle.Create(Prefix + "D"),
                H("The reduced denominator of the divisor-count ratio"),
                StatementSource.FromAuthor(DFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For each natural n, tau(n) is the cardinality of the positive divisors "
                        + "of n. The function D is the reduced denominator of the rational "
                        + "ratio tau(n)^n / n^tau(n); its value D(0)=1 is a totalization artefact, "
                        + "not part of the source claim."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a302975-square-denominator"),
                DeclarationHandle.Create(Prefix + "krizek_a302975"),
                H("Every positive A302975 denominator is a square"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive n, the denominator has even prime valuations. "
                        + "The valuation formula for the reduced ratio splits according to "
                        + "the parity of n and the divisor count; the odd case is forced to "
                        + "have zero valuation whenever a prime divides the divisor count. "
                        + "Reconstructing from the even valuations gives a square."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a302975-divisor-count-power-ratio-denominator-square"),
                    ResolutionKind.Proved)))));

    private static Formula DFormula()
    {
        var n = F.Id("n");
        var divisors = Call("divisors", n);
        var tau = Seq(Lvert, divisors, Rvert);
        var tauCast = Parenthesized(Seq(tau, Sp, Colon, Sp, Mathbb, Grp(F.Id("Q"))));
        var nCast = Parenthesized(Seq(n, Sp, Colon, Sp, Mathbb, Grp(F.Id("Q"))));
        var ratio = new Formula.Fraction(Pow(tauCast, n), Pow(nCast, tau));
        var denominator = Call("den", ratio);
        var equation = new Formula.Relation(
            Call("D", n), FormulaRelationOperator.Equal, denominator);
        return Disp(Seq(Forall, Sp, n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
            Comma, Sp, equation));
    }

    private static Formula TheoremFormula()
    {
        var n = F.Id("n");
        var positive = new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n);
        var conclusion = Call("IsSquare", Call("D", n));
        return Disp(Seq(Forall, Sp, n, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
            Comma, Sp, positive, Sp, Rightarrow, Sp, conclusion));
    }

    private static Formula Pow(Formula basis, Formula exponent) =>
        Seq(Grp(basis), Caret, Grp(exponent));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
