using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeArenas;

internal sealed class StaticExactExperimentDesignDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeArenas/StaticExactExperimentDesign.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The static exact-design law is carried by two typed Boolean CUT readouts.",
        H("Static Exact Experiment Design Arena"),
        Blocks(Describe.Lean(
            DescribeId.Create("static-exact-experiment-arena"),
            DeclarationHandle.Create(Prefix + "staticExactExperimentArena"),
            H("Static exact-experiment arena"),
            StatementSource.FromAuthor(Disp(Seq(
                F.Id("staticExactExperimentArena"), Colon, Sp,
                F.Id("PrimitiveLawArena"), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The law reproduces individual failure, joint injectivity, and minimal selection using the two realization slots."))),
            DescribeRole.Definition))));
}
