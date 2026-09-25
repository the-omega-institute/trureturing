using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class MechanicalDyadicBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Mechanical/MechanicalDyadicBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lower dyadic slope approximations miss an exact mechanical boundary bit at every precision.",
        H("Mechanical Dyadic Boundary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mechanical-dyadic-boundary-mismatch"),
                DeclarationHandle.Create(Prefix + "dyadic_lower_boundary_mismatch"),
                H("Lower approximation and boundary bit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an irrational slope strictly between zero and one, the floor dyadic approximation is nonnegative and falls strictly below the slope by less than one binary unit. At phase one minus the exact slope, the first actual mechanical bit is true, while the first bit at every lower dyadic approximation is false. Increasing finite precision cannot remove this specified boundary mismatch."))),
                DescribeRole.Theorem))));
}
