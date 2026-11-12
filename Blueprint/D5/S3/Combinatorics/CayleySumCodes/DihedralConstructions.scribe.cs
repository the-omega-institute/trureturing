using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.CayleySumCodes;

internal sealed class DihedralConstructionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CayleySumCodes/DihedralConstructions.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create(
        "D5/L/GraphInvariants/Nikandish/manikandishzhang2026sumcodes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "DihedralConstructions in the actual loopless sum graphs.",
        H("Retained constructions and exact corrected examples"),
        Blocks(
            Describe.Lean(DescribeId.Create("reflections-normal"),
                DeclarationHandle.Create(Prefix + "reflections_normal"), H("The all-reflection normal connection"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("All reflections in the actual DihedralGroup n form a conjugation-invariant subset."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reflections-adjacency"),
                DeclarationHandle.Create(Prefix + "reflections_adjacency"), H("The full complete bipartite graph"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Adjacency is exactly between the rotation and reflection parts, so the entire graph is K_n,n. No loop is introduced."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("reflections-total"),
                DeclarationHandle.Create(Prefix + "reflections_total"), H("Every reflection subgroup in the all-reflection graph"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every order-two reflection subgroup is a total perfect code, for all source n. The theorem even allows the infinite n=0 model without using it as a replacement source domain."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("parity-normal"),
                DeclarationHandle.Create(Prefix + "parity_normal"), H("The two normal parity families"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For any additive parity character, odd rotations together with the selected reflection parity class form a normal subset."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("parity-total"),
                DeclarationHandle.Create(Prefix + "parity_total"), H("The complete retained parity total codes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every reflection subgroup matching the selected parity class is a total perfect code, with the exact open-neighbor convention. The source even n=2*l character is DihedralConstructions.parity; c=0 and c=-1 recover both families."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/CayleySumCodes/TotalPerfectCriterion"))]));
}
