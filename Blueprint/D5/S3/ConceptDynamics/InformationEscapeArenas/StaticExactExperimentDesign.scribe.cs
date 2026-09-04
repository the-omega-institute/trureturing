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
        Blocks(
            Definition("static-readout", "StaticReadout", "Static readout indices",
                "The readout index type is the two-element finite type of static experiments."),
            Definition("static-signature", "staticSignature", "Static experiment signature",
                "The signature assigns a Boolean output to each of the two CUT readout indices."),
            Definition("static-exact-design-statement", "StaticExactDesignStatement",
                "Frozen static exact-design statement",
                "This alias is definitionally the type of the frozen theorem D5/S3/ConceptDynamics/ExperimentDesign/StaticExactExperimentDesign.static_exact_design."),
            Definition("static-exact-experiment-arena", "staticExactExperimentArena",
                "Static exact-experiment arena",
                "The law reproduces individual failure, joint injectivity, and minimal selection using the two realization slots."),
            Describe.Lean(
                DescribeId.Create("static-exact-experiment-arena-nondegenerate"),
                DeclarationHandle.Create(Prefix + "staticExactExperimentArena_nondegenerate"),
                H("Static exact-experiment arena is nondegenerate"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Nondegenerate")), Open,
                    Operatorname, Grp(F.Id("toArena")), Open,
                    F.Id("staticExactExperimentArena"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The three-element source carrier contains a pair of distinct models."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);
}
