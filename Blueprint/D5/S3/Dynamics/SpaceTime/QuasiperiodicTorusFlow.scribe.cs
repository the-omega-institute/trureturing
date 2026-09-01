using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Dynamics.SpaceTime;

internal sealed class QuasiperiodicTorusFlowDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Dynamics/SpaceTime/QuasiperiodicTorusFlow.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-dimensional additive tori carry linear quasiperiodic flows and an integer combination-frequency module.",
        H("Quasiperiodic Torus Flow"),
        Blocks(
            Def("torus", "PhaseTorus", "Finite phase torus",
                "A torus phase assigns one unit additive-circle coordinate to each finite frequency channel."),
            Def("flow", "quasiperiodicFlow", "Linear quasiperiodic flow",
                "Each phase coordinate is translated by time multiplied by its real frequency."),
            Def("frequency", "combinationFrequency", "Integer combination frequency",
                "An integer mode vector pairs with the frequency vector by a finite dot product."),
            Def("resonance", "IsResonantMode", "Exact resonant mode",
                "A mode is resonant when its integer combination frequency vanishes."),
            Thm("zero", "quasiperiodicFlow_zero", "Zero time fixes the torus",
                "The additive identity time contributes no circle translation."),
            Thm("add", "quasiperiodicFlow_add", "Flow times add",
                "Successive torus translations compose by addition of their real time parameters."),
            Thm("inverse", "quasiperiodicFlow_neg_cancel", "Negative time reverses the flow",
                "Translation by a time followed by its negative returns every torus phase."),
            Thm("frequency-add", "combinationFrequency_add", "Combination frequencies are additive",
                "Adding two integer mode vectors adds their paired frequencies."),
            Thm("resonance-add", "isResonantMode_add", "Resonances form an additive family",
                "The sum and negative of exact resonant modes remain resonant.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction")),
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
