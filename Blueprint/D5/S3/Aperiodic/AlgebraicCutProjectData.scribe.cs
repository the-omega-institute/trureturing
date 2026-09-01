using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Aperiodic;

internal sealed class AlgebraicCutProjectDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Aperiodic/AlgebraicCutProjectData.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cut-and-project data select physical points by an internal window and obey exact window and translation laws.",
        H("Algebraic Cut-and-Project Data"),
        Blocks(
            Entry("data", "CutProjectData", "Cut-and-project datum", "A selected lattice is equipped with physical and internal projections.", DescribeRole.Definition),
            Entry("model-set", "CutProjectData.modelSet", "Window model set", "Physical projections are selected exactly when their lattice witnesses land in the internal window.", DescribeRole.Definition),
            Entry("injective", "CutProjectData.HasInjectivePhysicalProjection", "Physical injectivity", "Physical projection is injective when restricted to selected lattice points.", DescribeRole.Definition),
            Entry("mono", "CutProjectData.modelSet_mono", "Window monotonicity", "Enlarging the internal window enlarges the physical model set.", DescribeRole.Theorem),
            Entry("union", "CutProjectData.modelSet_union", "Window union law", "A union of internal windows selects the union of the two model sets.", DescribeRole.Theorem),
            Entry("unique", "CutProjectData.latticeWitness_unique", "Unique lattice witness", "Physical injectivity makes the lattice witness of a selected physical point unique.", DescribeRole.Theorem),
            Entry("additive", "AdditiveCutProjectData", "Additive cut-and-project datum", "A subgroup lattice and additive projection homomorphisms supply translation structure.", DescribeRole.Definition),
            Entry("translate", "AdditiveCutProjectData.modelSet_translate", "Lattice translation covariance", "A lattice shift translates the internal window and physical model set compatibly.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock.Describe Entry(string id, string declaration, string heading, string paragraph, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(paragraph))), role);
}
