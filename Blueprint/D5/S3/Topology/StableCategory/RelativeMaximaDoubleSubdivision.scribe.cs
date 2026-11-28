using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class RelativeMaximaDoubleSubdivisionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A relative two-cover at the second subdivision",
        H("A relative two-cover at the second subdivision"),
        Blocks(Describe.Lean(
            DescribeId.Create("two-relative-charts-for-maximal-attachments"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/RelativeMaximaDoubleSubdivision.exists_relative_two_cover_double_subdivision"),
            H("Two lower regions retract into the common inherited region after two subdivisions"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("Choose maximal elements of a finite poset with at least one strict predecessor for each. One region consists of flags whose chains all meet the old poset and contracts into it by intersection. The other consists of old flags and separate components in which every chain contains the same chosen maximum. Insert its singleton, move the component to it, and follow an ambient path of flags to an old predecessor. Both regions contain and fix the entire inherited region. If the old inclusion is categorical, the same relative homotopies give a categorical lower two-cover."))),
            DescribeRole.Theorem))));
}
