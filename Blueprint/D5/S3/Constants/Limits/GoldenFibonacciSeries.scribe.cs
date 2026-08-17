using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Limits;

internal sealed class GoldenFibonacciSeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden-conjugate weighting of the shifted Fibonacci scale has an exact sum.",
        H("Golden Fibonacci Series"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-fibonacci-series-has-sum"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/Limits/GoldenFibonacciSeries."
                    + "golden_fibonacci_series_has_sum"),
                H("The alternating golden Fibonacci scale sums exactly"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sum, Underscore, Grp(F.Id("k"), Eq, D(0)), Caret, Grp(Infty), Sp,
                    Frac,
                    Grp(Psi, Caret, Grp(F.Id("k")), Sp, Cdot, Sp,
                        F.Id("F"), Underscore, Grp(F.Id("k"), Plus, D(1))),
                    Grp(Varphi, Caret, Grp(F.Id("k"), Plus, D(2))),
                    Sp, Eq, Sp,
                    Frac, Grp(D(1)), Grp(D(2), Sp, Varphi)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Mathlib's Binet formula splits each shifted Fibonacci number into "
                        + "golden-ratio and golden-conjugate powers. After the source weighting "
                        + "is distributed, both parts are summable geometric series. Their "
                        + "closed forms reduce with the quadratic golden-ratio identities to "
                        + "one half of the reciprocal golden ratio.")),
                    Paragraph(Text(
                        "This partial closure covers the exact alternating-series identity in "
                        + "part two of the source atom and hence its stated r-bar value. It does "
                        + "not formalize the C-zero identity, the Mobius minus-two rule, the "
                        + "claimed value of D at one from below, or any critical-line remainder."))),
                DescribeRole.Theorem))));
}
