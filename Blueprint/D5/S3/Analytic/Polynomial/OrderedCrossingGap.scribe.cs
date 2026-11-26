using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Polynomial;

internal sealed class OrderedCrossingGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader("D5/S3/Analytic/Polynomial/OrderedCrossingGap",
            "Polynomial gap for ordered crossing indices.", "symbolic-inequality"),
        H("Polynomial gap for ordered crossing indices"),
        Blocks(Describe.Lean(
            DescribeId.Create("ordered-crossing-gap-nonnegative"),
            DeclarationHandle.Create("D5/S3/Analytic/Polynomial/OrderedCrossingGap.gap_nonneg"),
            H("The scaled gap is nonnegative under the crossing inequalities"),
            StatementSource.FromAuthor(GapFormula()),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Computability/schiavo2026repeatedrentorbuy")),
            Blocks(Paragraph(Text(
                "The ordered lengths are real parameters. The three unit-gap hypotheses recover the "
                + "discrete inequalities used in Schiavo's Lemma 17 without requiring the parameters "
                + "to be integer-valued. If sigma is nonnegative, each summand is nonnegative after "
                + "using the lower bound for K or the equality of the two boundary indices. If sigma "
                + "is negative, multiply the expression by k+1 and use the upper crossing bound on K. "
                + "The resulting lower bound is affine in K with nonnegative slope. Its value at "
                + "the lower endpoint factors into nonnegative terms by the unit gaps."))),
            DescribeRole.Theorem))));

    private static Formula GapFormula() => Disp(Seq(
            Forall, Sp, Open, F.Id("a"), Sp, F.Id("b"), Sp, F.Id("K"), Sp, F.Id("L"), Sp, F.Id("B"),
            Sp, F.Id("N"), Sp, F.Id("k"), Colon, Sp, Seq(Mathbb, Grp(F.Id("R"))), Close, Comma, Sp, Open, D(0), Le, Sp, F.Id("a"), Land, Sp, F.Id("a"), Le, Sp, F.Id("b"), Land, Sp, D(0), Lt, F.Id("k"), Land, Sp, F.Id("k"), Le, Sp, F.Id("B"), Land, Sp, F.Id("B"), Le, Sp, F.Id("N"), Land, Sp, F.Id("N"), Le, Sp, F.Id("L"), Land, Sp, Open, F.Id("B"), Lt,
            F.Id("L"), Rightarrow, Sp, F.Id("B"), Plus, D(1), Le, Sp, F.Id("L"), Close, Land, Sp, Open, F.Id("k"),
            Lt, F.Id("B"), Rightarrow, Sp, F.Id("k"), Plus, D(1), Le, Sp, F.Id("B"), Close, Land, Sp, Open,
            F.Id("N"), Lt, F.Id("L"), Rightarrow, Sp, F.Id("N"), Plus, D(1), Le, Sp, F.Id("L"), Close, Land, Sp, F.Id("a"), Cdot, Sp, F.Id("L"), Cdot, Sp, Open, F.Id("L"), Minus, D(1), Close, Slash, D(2), Le, Sp, F.Id("K"), Land, Sp, F.Id("K"), Le, Sp, F.Id("a"), Cdot, Sp, F.Id("N"), Cdot, Sp, Open, F.Id("N"), Plus,
            D(1), Close, Slash, D(2), Plus, Open, F.Id("b"), Minus, F.Id("a"), Close, Cdot, Sp, F.Id("k"),
            Cdot, Sp, Open, F.Id("k"), Plus, D(1), Close, Slash, D(2), Close, Rightarrow, Sp, D(0), Le, Sp, Open,
            F.Id("K"), Minus, F.Id("a"), Cdot, Sp, F.Id("L"), Cdot, Sp, F.Id("B"), Slash, D(2), Close, Cdot, Sp, Open, F.Id("k"), Cdot, Sp, Open, F.Id("N"), Minus, F.Id("B"), Close, Minus, Open, F.Id("B"),
            Minus, F.Id("k"), Close, Cdot, Sp, Open, F.Id("L"), Minus, F.Id("N"), Close, Close, Plus,
            F.Id("a"), Cdot, Sp, F.Id("L"), Cdot, Sp, F.Id("B"), Cdot, Sp, Open, F.Id("L"), Minus, F.Id("N"),
            Close, Cdot, Sp, Open, F.Id("N"), Minus, F.Id("B"), Close, Slash, D(2), Plus, F.Id("L"), Cdot, Sp, F.Id("B"), Cdot, Sp, F.Id("k"), Cdot, Sp, Open, F.Id("b"), Minus, F.Id("a"), Close, Cdot, Sp, Open,
            F.Id("B"), Minus, F.Id("k"), Close, Slash, D(2)));
}
