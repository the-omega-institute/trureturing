using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SteinerSwitchOrbitDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Matroids/SteinerSwitchOrbit";
    private static readonly LibraryNoteRef Veblen = LibraryNoteRef.Create("D5/L/FiniteGeometry/falconefigulagalici2025veblenpoints");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Central translations partition the successful starts of each point-deleted Steiner switch.",
        H("Central Orbits of Successful Steiner Switches"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("centre-divides-successful-starts"),
                DeclarationHandle.Create(Module + ".successful_starts_dvd_center"),
                H("The centre divides the number of successful starts at each pivot"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Veblen),
                Blocks(
                    Paragraph(Text("Take a finite complete Steiner triple system and fix a deleted point and a retained pivot. With the matching of uncovered pairs in the retained packing, the number of successful starting labels is divisible by the cardinality of the Steiner loop centre.")),
                    Paragraph(Text("Multiplication by a central element commutes with both matching translations. It carries each alternating component to a component of the same size, so it preserves the full-carrier vertices in components of size at least six.")),
                    Paragraph(Text("These vertices split into orbits under the central translations. Cancellation gives each orbit exactly as many vertices as there are central elements. The existing image characterization equates their cardinality with that of the successful retained labels. The zero count is included."))),
                DescribeRole.Theorem))));
}
