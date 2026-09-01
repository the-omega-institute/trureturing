using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Aperiodic;

internal sealed class GoldenCutProjectSpecializationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Aperiodic/GoldenCutProjectSpecialization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The existing golden lattice-window set is an accepted model set for generic physical and internal projections.",
        H("Golden Cut-and-Project Specialization"),
        Blocks(
            Def("data", "goldenAmbientCutProjectData", "Golden ambient projection data",
                "The first and second Minkowski coordinates become the physical and internal additive projections."),
            Def("lattice", "IsGoldenLatticePoint", "Golden lattice acceptance",
                "The acceptance predicate selects exactly the already defined golden lattice points."),
            Thm("equality", "golden_accepted_model_set_eq_existing", "Generic accepted set equals the existing golden set",
                "The generic window-and-acceptance definition is extensionally identical to the frozen golden cut-and-project set."),
            Thm("canonical-subset", "golden_model_set_subset_generic_accepted", "Canonical golden values lie in the accepted set",
                "The existing one-way inclusion from natural-number golden expansions is transported to the generic interface."),
            Thm("unrestricted", "golden_accepted_subset_unrestricted", "Dropping lattice acceptance enlarges the set",
                "The golden accepted model set lies in the unrestricted ambient-plane window model set."),
            Thm("physical", "golden_physical_projection_eq", "Physical projection compatibility",
                "The generic physical map is exactly the existing first-coordinate projection."),
            Thm("internal", "golden_internal_projection_eq", "Internal projection compatibility",
                "The generic internal map is exactly the existing conjugate-coordinate projection.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Aperiodic/AcceptedModelSet")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S1/Deficit/ModelSet/GoldenCutAndProject")),
        ]));

    private static DocumentBlock.Describe Def(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}
