using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.CompleteHockeyStick;

internal sealed class NonlinearUpperDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A full span of Kraus products bounds the output divergence for every finite reference and every parameter at least one.",
        H("Dimension-uniform nonlinear hockey-stick bound"),
        Blocks(
          Describe.Lean(
            DescribeId.Create("uniform-nonlinear-hockey-stick-upper"),
            DeclarationHandle.Create("D5/S3/Quantum/Divergence/CompleteHockeyStick/NonlinearUpper.exists_uniform_nonlinear_upper"),
            H("Uniform upper bound at positive input divergence"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/hirchegeorgenuradhawilde2026conditional")),
            Blocks(
                Paragraph(Text("Write x for the input hockey-stick divergence and y for the output divergence. For a channel with full Kraus-product span there is a constant C at least one such that y is at most x minus x squared divided by C squared times (2x + gamma - 1). The same C works for all positive x, all finite references, and all gamma at least one.")),
                Paragraph(Text("The equal reference marginals order the marginals of the positive and negative input parts. The Gram inequality gives purifications related by a contraction on the input and purifier. Lift that contraction through complementary compression, then split its overlap using an optimal output effect and the complementary effect. Cauchy–Schwarz bounds the overlap by the output loss and yields the stated inequality."))),
            DescribeRole.Theorem))));
}
