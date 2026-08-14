using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class GoldenFiberPrefixBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite positive-indexed golden-fiber prefix has an elementary linear upper bound.",
        H("Golden Fiber Prefix Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-fiber-prefix-linear-bound"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/GoldenFiberPrefixBound.golden_fiber_prefix_sum_le"),
                H("Golden-fiber prefixes satisfy the linear bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("T"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Sum, Underscore, Grp(F.Id("n"), Eq, D(1)), Caret, Grp(F.Id("T")), Sp,
                    F.Id("f"), Underscore, F.Id("n"), Sp, Le, Sp, Varphi, Sp,
                    F.Id("T"), Sp, Plus, Sp, D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural prefix length T, the sum of the positive-indexed "
                        + "golden-fiber letters f_n from n = 1 through T is at most phi times T "
                        + "plus two. The integer-valued sum is compared in the real numbers.")),
                    Paragraph(Text(
                        "The repository's exact golden_fiber_prefix_count identity is the strictly "
                        + "stronger reusable result. After rewriting by that identity, Mathlib's "
                        + "Int.floor_le and Real.goldenRatio_lt_two bounds close the inequality; "
                        + "no prefix count is reproved.")),
                    Paragraph(Text(
                        "This is an honest partial closure of only the explicit prefix-sum bound in "
                        + "the leading elementary chain. The polynomial maximum and evaluation "
                        + "claims, Bernstein derivative estimate, peak lower bound, zero-free disks, "
                        + "numerical checks, status change, and localization discussion remain "
                        + "unresolved and are not asserted here."))),
                DescribeRole.Theorem))));
}
