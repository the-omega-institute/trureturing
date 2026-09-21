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
            Node("pointwiseOrder_sensitivity", "Strictly ordered values witness independent sensitivity of each slot for both strict and weak laws.", DescribeRole.Theorem),
            Node("homogeneousPointwiseEqSignature", "Two Boolean-indexed CUT slots share one output type and its explicit equality dictionary; there are no anchors.", DescribeRole.Definition),
            Node("homogeneousPointwiseEqRealization", "Boolean elimination selects the supplied left or right readout in the shared output type.", DescribeRole.Definition),
            Node("homogeneousPointwiseEqArena", "The law equates the homogeneous readouts at every state of the supplied finite arena.", DescribeRole.Definition),
            Node("homogeneousPointwiseEqLegacy", "The full pointwise equation is definitionally equivalent to the homogeneous arena law.", DescribeRole.Theorem),
            Node("homogeneousPointwiseEq_sensitivity", "Distinct output values and an inhabited state witness a law change from changing either CUT slot alone.", DescribeRole.Theorem),
            Node("homogeneousPointwiseNeSignature", "Two Boolean-indexed CUT slots share an output type with decidable equality and no anchors.", DescribeRole.Definition),
            Node("homogeneousPointwiseNeRealization", "Boolean elimination retains the two supplied homogeneous readouts for disequality.", DescribeRole.Definition),
            Node("homogeneousPointwiseNeArena", "The law requires the homogeneous readouts to differ at every state.", DescribeRole.Definition),
            Node("homogeneousPointwiseNeLegacy", "The full pointwise disequality is definitionally equivalent to the homogeneous arena law.", DescribeRole.Theorem),
            Node("homogeneousPointwiseNe_sensitivity", "Distinct output values make disequality true; changing either slot alone to match the other falsifies it.", DescribeRole.Theorem),
            Node("homogeneousPointwiseOrderSignature", "Two Boolean-indexed CUT slots share an output type and equality dictionary; order is supplied separately by the arena law.", DescribeRole.Definition),
            Node("homogeneousPointwiseOrderRealization", "Boolean elimination selects the left or right output without an order parameter in the realization.", DescribeRole.Definition),
            Node("homogeneousPointwiseOrderArena", "The arena supplies the linear order and selects strict or weak pointwise comparison of the shared output type.", DescribeRole.Definition),
            Node("homogeneousPointwiseOrderLegacy", "The complete universal strict or weak comparison is definitionally equivalent to the selected arena law.", DescribeRole.Theorem),
            Node("homogeneousPointwiseOrder_sensitivity", "Two strictly ordered values witness independent changes to each CUT slot for both comparison laws.", DescribeRole.Theorem))));

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
