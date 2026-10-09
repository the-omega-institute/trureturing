using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ErdosGyarfasGarciaOrientationAveragingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationAveraging.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complementary unused-edge distributions force a translated fourteen-cycle with at least ten distinguished-port visits.",
        H("Averaging the two orientation certificates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("u-count"),
                DeclarationHandle.Create(Prefix + "uCount"),
                H("Distinguished-port visits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a fourteen-entry vertex sequence c, an unused-edge sequence e with three possible edge types, a vertex orientation sigma, and a translation h, uCount counts indices i at which sigma(trans(h,c(i))) differs from e(i). These are precisely the visits where the two used cycle edges include the distinguished port."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exists-many-u"),
                DeclarationHandle.Create(Prefix + "exists_many_u"),
                H("A translate has ten distinguished-port visits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let V be a nonempty finite type, and suppose h maps to trans(h,v) bijectively for every v. Suppose the two unused-edge sequences have multiplicities (6,4,4) and (2,6,6). For every orientation sigma, there is a translation h at which the first or the second sequence has at least ten distinguished-port visits.")),
                    Paragraph(Text("Reindex each fixed-position sum by the translation bijection, then interchange the finite sums. At every oriented vertex, twice the number of distinguished-port visits in the first sequence plus that number in the second sequence is 28, independent of its orientation. Consequently twice the first translated total plus the second translated total is 28 times the size of V. If each translate had at most nine visits in both sequences, the same expression would be at most 27 times the size of V. Nonemptiness gives a contradiction."))),
                DescribeRole.Theorem))));
}
