using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class WeightedClosePairTailDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/WeightedClosePairTail";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A count by the larger ordinate bounds the total reciprocal-product weight.",
        H("Weighted close pairs above a height cutoff"),
        Blocks(Describe.Lean(
            DescribeId.Create("weighted-close-pairs-le"),
            DeclarationHandle.Create(Owner + ".weighted_close_pairs_le"),
            H("A cumulative count bounds the weighted tail"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Take a finite set of ordered pairs whose two ordinates lie in [X,T], "
                    + "where 2≤X≤T. Assume each pair has gap at most η and η≤X/2. "
                    + "Each index has nonnegative multiplicity m and nonnegative weight w "
                    + "bounded by m divided by its ordinate. Let B(y) be the sum of m(i)m(j) "
                    + "over the supplied pairs whose larger ordinate is at most y. Assume "
                    + "B(y)≤Cy log y for X≤y≤T with C≥0. Let A denote the sum of w(i)w(j) "
                    + "over the supplied pairs.")),
                Paragraph(Text(
                    "The larger ordinate h of a close pair is at least X. Its smaller "
                    + "ordinate is at least h/2, so the weight of that pair is at most "
                    + "2m(i)m(j)/h². Express 1/h² as 1/T² plus the integral of 2/y³ "
                    + "from h to T. Interchanging the finite sum and the integral replaces "
                    + "the sum of indicators by B(y). Apply the cumulative bound at T "
                    + "and inside the integral. Integrating log y/y² gives the asserted bound."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var x = F.Id("X");
        var numerator = Seq(F.Id("log"), Open, x, Close, Sp, Plus, Sp, D(1));
        return Disp(Seq(F.Id("A"), Sp, Leq, Sp, D(4), Sp, F.Id("C"), Sp,
            new Formula.Fraction(numerator, x)));
    }
}
