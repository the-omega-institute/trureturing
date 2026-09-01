using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Aperiodic;

internal sealed class GoldenCutProjectSpecializationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Aperiodic/GoldenCutProjectSpecialization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The frozen golden lattice and window instantiate the generic cut-and-project interface, while natural beta expansions form an accepted sector.",
        H("Golden Cut-and-Project Specialization"),
        Blocks(
            Entry("data", "goldenCutProjectData", "Golden cut-and-project datum", "The frozen Minkowski lattice uses the first coordinate physically and the conjugate coordinate internally.", DescribeRole.Definition),
            Entry("model-set", "goldenCutProject_modelSet_eq", "Generic and frozen model sets agree", "The generic window construction is exactly the previously frozen golden cut-and-project set.", DescribeRole.Theorem),
            Entry("subset", "golden_model_set_subset_generic_cut_project", "Natural golden values lie in the generic model set", "The existing natural beta range enters the generic cut-and-project interface.", DescribeRole.Theorem),
            Entry("witness", "IsNaturalGoldenWitness", "Natural beta witness", "Admissibility records lattice points arising from natural-number beta expansions.", DescribeRole.Definition),
            Entry("accepted", "acceptedNaturalGoldenModelSet", "Accepted natural golden sector", "The golden window is refined by the natural beta-language predicate.", DescribeRole.Definition),
            Entry("exact", "acceptedNaturalGoldenModelSet_eq", "Exact accepted-sector identification", "The accepted generic model set is exactly the physical image of the frozen natural golden model set.", DescribeRole.Theorem),
            Entry("full", "acceptedNaturalGoldenModelSet_subset_full", "Accepted sector lies in the full geometry", "The symbolic natural sector is contained in the full geometric golden model set.", DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Aperiodic/AcceptedModelSet")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Deficit/ModelSet/GoldenCutAndProject"))
        ]));

    private static DocumentBlock.Describe Entry(string id, string declaration, string heading, string paragraph, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(paragraph))), role);
}
