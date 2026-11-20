using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class StructuredRankOneDimensionTwoRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/StructuredRankOneDimensionTwoRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/mazhang2026scaleddowndate");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For n = 2 a continuous structured downdate on a once-punctured interval switches its negative index.",
        H("The dimension threshold for punctured simplices is sharp"),
        Blocks(
            Describe.Lean(DescribeId.Create("dimension-two-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("Corollary 6 in dimension two"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every point c of the open 1-simplex (0, 1), and every pair of continuous maps "
                    + "d, x from (0, 1) minus c to ℝ² with pivot Δ = xᵀ diag(d) x ≠ 0 and positive "
                    + "semidefinite downdate diag(d) − Δ⁻¹ (diag(d) x)(diag(d) x)ᵀ everywhere, either Δ > 0 "
                    + "and every dᵢ ≥ 0 everywhere, or Δ < 0 everywhere and a unique index j has dⱼ < 0 "
                    + "everywhere while every other dᵢ ≥ 0 everywhere. This is the conclusion of Corollary 6 "
                    + "for n = 2 with a one-point deleted set."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dimension-two-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Sharpness of the threshold n ≥ 3"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "The claim is false. Hence the conclusion of Corollary 6, uniform over finite deleted "
                        + "sets, fails for n = 2, and the threshold n ≥ 3 is sharp.")),
                    Paragraph(Text(
                        "Delete c = 1/2. Left of the puncture take D = diag(−1, 1) and x = (1, 0); right of it "
                        + "take D = diag(1, −1) and x = (0, 1). The left piece is open in the punctured "
                        + "interval and so is its complement, so the two-piece maps are continuous. The pivot "
                        + "is −1 on both pieces and the downdates are diag(0, 1) and diag(1, 0), both positive "
                        + "semidefinite. The pivot is negative, so the first alternative fails; the negative "
                        + "diagonal entry is the first coordinate at 1/4 and the second at 3/4, so no index is "
                        + "negative everywhere. This is Corollary 8 of H. Ma and W. Zhang "
                        + "(DOI 10.5281/zenodo.23920598) on MathOverflow 513954, revision 2, asked by Lucid."))),
                DescribeRole.Theorem))));
}
