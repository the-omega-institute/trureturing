using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class SpechtAbsoluteIrreducibilityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/tauceti2026spechtpolytabloids");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Specht AbsoluteIrreducibility",
        H("Specht AbsoluteIrreducibility"),
        Blocks(
            Paragraph(Text("The invariant orthogonal decomposition gives a preimage of each polytabloid inside the Specht subspace under its column antisymmetrizer. An equivariant endomorphism commutes with this operator, whose image is a single polytabloid line. It acts by one scalar on that polytabloid. The orbit spans the entire Specht space, forcing the same scalar everywhere. Transport to the original partition identifies rational Specht intertwining endomorphisms with the rational field.")),
            Describe.Lean(DescribeId.Create("exists-mem-asalgebrahom-columnantisymmetrizer-eq-polytabloid"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility.exists_mem_asAlgebraHom_columnAntisymmetrizer_eq_polytabloid"),
                H("exists mem asAlgebraHom columnAntisymmetrizer eq polytabloid"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("algebramap-intertwiningmap-spechtsubrepresentation-bijective"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility.algebraMap_intertwiningMap_spechtSubrepresentation_bijective"),
                H("algebraMap intertwiningMap spechtSubrepresentation bijective"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("algebramap-intertwiningmap-spechtmodule-bijective"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility.algebraMap_intertwiningMap_spechtModule_bijective"),
                H("algebraMap intertwiningMap spechtModule bijective"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spechtmoduleintertwiningendalgequiv"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Partitions/SpechtAbsoluteIrreducibility.spechtModuleIntertwiningEndAlgEquiv"),
                H("spechtModuleIntertwiningEndAlgEquiv"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The statement is the selected structural result for the explicit permutation representation and polytabloid construction."))),
                DescribeRole.Definition))));
}
