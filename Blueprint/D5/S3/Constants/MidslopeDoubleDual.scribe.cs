using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants;

internal sealed class MidslopeDoubleDualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Affine duality of the arithmetic and geometric midslope values is exactly reverse " +
        "doubling of their curvature coefficients.",
        H("Midslope Double-Dual Law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("arithmetic-geometric-midslope-double-dual-law"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/MidslopeDoubleDual.arithmetic_geometric_double_dual"),
                H("The arithmetic and geometric values satisfy the double-dual law"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("J"), Open, D(0), Close, Sp, Eq, Sp,
                    D(2), F.Id("J"), Open, D(1), Close, Sp, Plus, Sp, D(1),
                    Sp, Leftrightarrow, Sp,
                    Frac, Grp(D(1)), Grp(D(1), Plus, F.Id("J"), Open, D(1), Close),
                    Sp, Eq, Sp,
                    D(2), Frac, Grp(D(1)),
                    Grp(D(1), Plus, F.Id("J"), Open, D(0), Close), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a midslope value j, define its curvature coefficient as " +
                        "c(j) = 1 / (1 + j). Away from the pole j = -1, the identity " +
                        "j' = 2j + 1 is equivalent, by clearing denominators, to the " +
                        "reverse doubling relation c(j) = 2c(j').")),
                    Paragraph(Text(
                        "The repository already proves J(1) = -log 2 for the arithmetic " +
                        "mean and J(0) = 1 - 2 log 2 for the geometric mean. These exact " +
                        "values make both sides hold, while Mathlib's strict logarithm bound " +
                        "shows that neither curvature denominator vanishes.")),
                    Paragraph(Text(
                        "This is casewise partial closure of the source corollary. It covers " +
                        "the arithmetic-geometric pair only; the separate logarithmic-harmonic " +
                        "pair remains outside this declaration."))),
                DescribeRole.Theorem
            ))));
}
