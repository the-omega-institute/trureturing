using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class DimensionFourCategoricalColourDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Categorical star assignments in dimension four",
        H("Categorical star assignments in dimension four"),
        Blocks(Describe.Lean(
            DescribeId.Create("four-lower-sets-of-categorical-stars"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/DimensionFourCategoricalColour.four_lower_sets_of_categorical_stars"),
            H("Four categorical lower sets after ordinary subdivision"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(
                Paragraph(Text("In dimension at most four, let each closed vertex star be assigned to one of two subcomplexes with nullhomotopic realization inclusions. Under the connectedness hypothesis, the face poset of some ordinary subdivision has a categorical lower cover of size four.")),
                Paragraph(Text("Mixed-label faces and top-dimensional faces supply one colour in the first subdivision. Every monochromatic flag has a constant set of old labels and at most four vertices. The new inclusions contract by gluing the supplied homotopies on the open fibres of a label chosen by positive coordinate support. The common-depth cover of the two regions then gives the four lower sets."))),
            DescribeRole.Theorem))));
}
