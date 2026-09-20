using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrownOrderPolytopeCyclePartitionsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lundstrom2025crown");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd block parity characterizes nontrivial compatible cycle partitions.",
        H("Compatibility of crown cycle partitions"),
        Blocks(
            Paragraph(Text("The first characterization is source Lemma 3.2. The endpoint-isolated formulation is an implementation consequence used in recovering augmented partitions.")),
            Describe.Lean(
                DescribeId.Create("crown-cycle-compatible-iff-exists-odd-block"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCyclePartitions.crownCycleCompatible_iff_exists_oddBlock"),
                H("Compatibility exactly when an odd block exists"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For n at least two and a nontrivial connected partition of the 2n-cycle, antisymmetry of the induced crown quotient order is equivalent to existence of a block with odd cardinality. The nontriviality hypothesis excludes the one-block case."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("crown-partition-exists-odd-original-block"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCyclePartitions.crownPartition_exists_oddOriginalBlock"),
                H("Odd blocks when both endpoints are isolated"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For an augmented connected compatible partition at n at least two, if neither endpoint meets an original vertex and the original-vertex partition is nontrivial, there exists an odd original block distinct from both endpoint blocks."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeCycleCuts"))
        ]));
}
