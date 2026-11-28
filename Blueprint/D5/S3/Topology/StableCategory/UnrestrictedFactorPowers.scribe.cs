using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class UnrestrictedFactorPowersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unbounded one-step category of finite powers",
        H("Unbounded one-step category of finite powers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-no-categorical-cover-of-no-one"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/UnrestrictedFactorPowers.exists_no_categorical_cover_of_no_one"),
                H("Unbounded one-step categorical cover size of finite powers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("The added rank coordinate lets every chain extend to a full-rank chain. Projection has a section using the size of each principal ideal. Raising each rank to the maximum of its old rank and the section rank gives two pointwise comparisons. The subdivision fence lift transports categorical lower covers along these maps. The Hales–Jewett obstruction in the enlarged poset then applies to powers of the original finite poset."))),
                DescribeRole.Theorem))));
}
