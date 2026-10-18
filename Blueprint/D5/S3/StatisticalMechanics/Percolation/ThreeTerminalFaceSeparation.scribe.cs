using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Percolation;

internal sealed class ThreeTerminalFaceSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The forced-open component of the middle terminal is the exact obstruction to realizing the exceptional partition in a configuration face.",
        H("Separation by a forced-open component"),
        Blocks(Describe.Lean(DescribeId.Create("three-terminal-face-forced-component"),
            DeclarationHandle.Create("D5/S3/StatisticalMechanics/Percolation/ThreeTerminalFaceSeparation.interval_ac_iff_avoiding_forced_component"),
            H("An interval realizes ac exactly when the forced component can be avoided"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let H and U be arbitrary simple graphs on the same vertex type, with H a subgraph "
                + "of U. Let a, b, c be marked vertices, and assume that neither a nor c belongs to "
                + "the H-connected component B of b. There exists a graph K between H and U whose "
                + "actual three-terminal partition is ac with b separate if and only if a and c "
                + "are reachable using only U-edges whose endpoints both lie outside B. No "
                + "finiteness, connectedness, cactus, or distinct-terminal hypothesis is needed. "
                + "For the reverse direction, take K to be the union of H with all U-edges outside B. "
                + "The set B is closed under adjacency in K, so b remains separate from a and c. "
                + "For the forward direction, an a-to-c walk realizing ac cannot meet B: a visit "
                + "to B followed by a forced-open H-walk would connect a to b. Restricting that "
                + "walk therefore supplies the required path outside B. The graphs and path relation "
                + "are defined independently of the exceptional-mode conclusion."))), DescribeRole.Theorem)),
        []));
}
