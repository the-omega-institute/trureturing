using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class ConjugacyIndexSumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full centralizer-index identity for normal total perfect subgroup codes.",
        H("Counting actual conjugacy classes in both branches"),
        Blocks(Describe.Lean(DescribeId.Create("conjugacy-centralizer-index-sum"),
            DeclarationHandle.Create("D5/S3/Combinatorics/CayleySumCodes/ConjugacyIndexSum.result"),
            H("The extra reciprocal-index term"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(
                "D5/L/FiniteGroups/manikandishzhang2026sumcodes")),
            Blocks(Paragraph(Text(
                "For every finite group, normal subgroup H and actual total-code "
                + "connection set Y, choose any complete disjoint family of its "
                + "conjugacy classes. The normal-core theorem proves H lies in each "
                + "representative's centralizer. Thus [C_G(y_i):H] is a genuine "
                + "subgroup index. Orbit-stabilizer and the actual disjoint class "
                + "partition give the sum of reciprocal indices equal to one in "
                + "case (a), and one plus 1/[G:H] in case (b). The identity is "
                + "retained in counting Y despite the absence of graph loops. "
                + "This is correction Proposition 3.1(iii), not an assumed "
                + "numerical partition or a square-free-only formula."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/CayleySumCodes/CodeCentralizers"))]));
}
