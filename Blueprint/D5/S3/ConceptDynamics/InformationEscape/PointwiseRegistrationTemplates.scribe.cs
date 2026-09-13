using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class PointwiseRegistrationTemplatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact pointwise registration programs over finite object states.",
        H("PointwiseRegistrationTemplates"),
        Blocks(
            Node("pointwiseEqSignature", "Two typed CUT readouts retain the two terms of a pointwise equation.", DescribeRole.Definition),
            Node("pointwiseEqRealization", "The two supplied functions remain the readouts, with no theorem-based reduction.", DescribeRole.Definition),
            Node("pointwiseEqArena", "The law equates the two readouts at every state of the supplied finite arena.", DescribeRole.Definition),
            Node("pointwiseEqLegacy", "The complete universally quantified equation is definitionally the generated law.", DescribeRole.Theorem),
            Node("pointwiseEq_sensitivity", "Two distinct output values and an inhabited arena witness sensitivity of each individual CUT slot.", DescribeRole.Theorem),
            Node("pointwiseNeSignature", "Two typed CUT readouts retain the two terms of a pointwise disequality.", DescribeRole.Definition),
            Node("pointwiseNeRealization", "Both supplied functions remain unchanged in the realization.", DescribeRole.Definition),
            Node("pointwiseNeArena", "The law requires different readout values at every state.", DescribeRole.Definition),
            Node("pointwiseNeLegacy", "The complete universally quantified disequality is definitionally the generated law.", DescribeRole.Theorem),
            Node("pointwiseNe_sensitivity", "An inhabited state and distinct output values witness both readout slots independently.", DescribeRole.Theorem),
            Node("pointwiseOrderSignature", "Two typed CUT readouts carry values in a linear order.", DescribeRole.Definition),
            Node("pointwiseOrderRealization", "The supplied left and right functions are retained verbatim.", DescribeRole.Definition),
            Node("pointwiseOrderArena", "An explicit strictness selector chooses pointwise less-than or less-than-or-equal, with no arbitrary law parameter.", DescribeRole.Definition),
            Node("pointwiseOrderLegacy", "The full universal comparison is definitionally the law selected by strictness.", DescribeRole.Theorem),
            Node("pointwiseOrder_sensitivity", "Strictly ordered values witness independent sensitivity of each slot for both strict and weak laws.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/PointwiseRegistrationTemplates." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
