using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class IffRegistrationTemplatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boolean predicate registrations over finite object states.",
        H("IffRegistrationTemplates"),
        Blocks(
            Node("iffSignature", "The homogeneous pointwise equality signature at Bool supplies two Boolean CUT readouts and an empty anchor index.", DescribeRole.Definition),
            Node("iffRealization", "Two supplied Boolean functions feed homogeneousPointwiseEqRealization with the pinned Boolean equality dictionary. This contracts the iff API onto the homogeneous pointwise template; the older pointwiseEqRealization is unchanged.", DescribeRole.Definition),
            Node("iffArena", "The homogeneous pointwise equality arena equates both Boolean readouts at every state of the supplied finite arena.", DescribeRole.Definition),
            Node("iffLegacy", "The generic predicate interface retains explicit named DecidablePred dictionaries dP and dQ, applied under the Boolean readout lambdas. Equality of decided Booleans is equivalent to the original universally quantified iff statement.", DescribeRole.Theorem),
            Node("iff_sensitivity", "The homogeneous pointwise sensitivity theorem uses an inhabited state and the distinct Boolean values false and true to witness each readout slot.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/IffRegistrationTemplates." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
