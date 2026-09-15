using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class GuardedEqualityRegistrationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Guarded equality registration programs over complete finite object arenas.",
        H("GuardedEqualityRegistrations"),
        Blocks(
            Node("positiveFirstArena", "All three candidate models remain in the arena.", DescribeRole.Definition),
            Node("positiveFirstRealization", "E_X is the guard; the model and M_XY are the unreduced equality readouts.", DescribeRole.Definition),
            Node("positiveFirst_bridge", "The original positive-experiment hypothesis and equality are retained.", DescribeRole.Theorem),
            Node("positiveFirst_lawSensitive", "The frozen theorem satisfies the law; changing the model readout falsifies it at M_XY while keeping E_X fixed.", DescribeRole.Theorem),
            Node("positiveFirst_slotSensitive", "The shared sensitivity theorem checks independent support for the guard and both equality slots.", DescribeRole.Theorem),
            Node("outerDimensionArena", "All six groups remain, including the four inner groups.", DescribeRole.Definition),
            Node("outerDimensionRealization", "isOuter is the guard; dimension and constant forty are the CUT readouts.", DescribeRole.Definition),
            Node("outerDimension_bridge", "The full outer-group conditional equation is retained.", DescribeRole.Theorem),
            Node("outerDimension_lawSensitive", "The frozen theorem satisfies the law; a dimension of thirty-nine falsifies it at an outer group with its guard fixed.", DescribeRole.Theorem),
            Node("outerDimension_slotSensitive", "The shared sensitivity theorem checks independent support for the guard and both equality slots.", DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(string declaration, string text, DescribeRole role) =>
        Describe.Lean(
            DescribeId.Create(declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/GuardedEqualityRegistrations." + declaration),
            H(declaration),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            role);
}
