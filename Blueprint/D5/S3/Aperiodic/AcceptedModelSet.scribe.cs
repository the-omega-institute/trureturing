using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Aperiodic;

internal sealed class AcceptedModelSetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Aperiodic/AcceptedModelSet.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Model sets with an additional admissibility predicate separate geometric windows from language or cone constraints.",
        H("Accepted Model Sets"),
        Blocks(
            Entry("accepted", "acceptedModelSet", "Accepted model set", "A lattice witness must satisfy both the internal window and an independent admissibility predicate.", DescribeRole.Definition),
            Entry("subset", "acceptedModelSet_subset_modelSet", "Accepted sector lies in the model set", "Forgetting admissibility embeds the accepted sector into the full geometric model set.", DescribeRole.Theorem),
            Entry("window-mono", "acceptedModelSet_window_mono", "Window monotonicity", "Enlarging the window enlarges the accepted model set.", DescribeRole.Theorem),
            Entry("accept-mono", "acceptedModelSet_accept_mono", "Acceptance monotonicity", "Weakening the admissibility predicate enlarges the selected set.", DescribeRole.Theorem),
            Entry("true", "acceptedModelSet_true", "Universal acceptance", "Accepting every lattice point recovers the full geometric model set.", DescribeRole.Theorem),
            Entry("additive", "additiveAcceptedModelSet", "Additive accepted model set", "The accepted construction specializes to additive cut-and-project data.", DescribeRole.Definition),
            Entry("translate", "additiveAcceptedModelSet_translate", "Accepted translation covariance", "Translation-invariant admissibility preserves lattice translation covariance.", DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Aperiodic/AlgebraicCutProjectData"))
        ]));

    private static DocumentBlock.Describe Entry(string id, string declaration, string heading, string paragraph, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(paragraph))), role);
}
