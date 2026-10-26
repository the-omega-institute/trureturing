using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraEqualityProfileDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraEqualityProfile.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A unique profile peak forces troughs onto physical endpoints.", H("Profile rigidity in geometric equality"),
        Blocks(
            Describe.Lean(DescribeId.Create("miuraequalityprofile-profile"),
                DeclarationHandle.Create(Prefix + "profile"), H("The original row profile"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The one-row array retains the values of a specified actual row and every existing horizontal neighbour. Its endpoints count as possible local extrema."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuraequalityprofile-boundary"),
                DeclarationHandle.Create(Prefix + "unique_profile_peak_minima_on_boundary"), H("One peak excludes internal troughs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer unit-edge array with a specified actual row, if its row profile has exactly one local maximum including endpoints, every local minimum of that profile lies at the first or last physical column. The attained finite maximum envelope makes the entire profile a tent with its peak at that unique maximum. An internal vertex of such a tent cannot have both adjacent vertices higher."))), DescribeRole.Theorem))));
}
