using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class LocalFactorCriticalLineNonvanishingDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/EulerGerm/LocalFactorCriticalLineNonvanishing."
            + "germLocalFactor_critical_line_nonzero_of_five_le";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime local factors at least five do not vanish on the pulled-back critical line.",
        H("Golden Local-Factor Critical-Line Nonvanishing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-local-factor-critical-line-nonvanishing"),
                DeclarationHandle.Create(Declaration),
                H("Prime local factors are nonzero on the pulled-back critical line"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every prime p at least five and every real ordinate t, the "
                            + "golden local factor is nonzero at real part one over twice "
                            + "the square of the golden ratio.")),
                    Paragraph(Text(
                        "The statement makes no claim for the primes two or three."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula p = F.Id("p");
        Formula t = F.Id("t");
        Formula primeHypothesis = Call("Prime", p);
        Formula lowerBound = new Formula.Relation(
            D(5), FormulaRelationOperator.LessThanOrEqual, p);
        Formula criticalRealPart = new Formula.Fraction(
            D(1),
            Seq(D(2), Sp, Times, Sp,
                Power(Seq(F.Id("Real"), Dot, F.Id("goldenRatio")), D(2))));
        Formula criticalPoint = Seq(
            Grp(criticalRealPart), Sp, Plus, Sp,
            F.Id("i"), Sp, Times, Sp, t);
        Formula nonzero = new Formula.Relation(
            Call("germLocalFactor", criticalPoint, p),
            FormulaRelationOperator.NotEqual,
            D(0));
        Formula hypotheses = new Formula.Logic(
            primeHypothesis, FormulaLogicOperator.And, lowerBound);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("p", NaturalNumbers()), Bound("t", RealNumbers())],
            new Formula.Logic(
                hypotheses, FormulaLogicOperator.Implies, nonzero)));
    }

    private static Formula Power(Formula value, Formula exponent) =>
        Seq(Grp(value), Caret, Grp(exponent));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula NaturalNumbers() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula RealNumbers() =>
        Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
