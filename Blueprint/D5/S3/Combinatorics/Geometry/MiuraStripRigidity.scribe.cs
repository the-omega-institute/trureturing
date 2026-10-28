using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraStripRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraStripRigidity.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/gupta2026miuradegrees");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strip with no ambient maximum before its exit row is a vertical extrusion.", H("One-exit strip rigidity"),
        Blocks(
            Paragraph(Text("Chakshu Gupta, One construction for the Miura-ori flip-graph degree sequence, arXiv:2607.05567v3. The finite height suppliers are adapted from the accompanying CC BY 4.0 Lean source.")),
            Describe.Lean(DescribeId.Create("miurastriprigidity-stripmap"),
                DeclarationHandle.Create(Prefix + "stripMap"), H("The actual rectangular restriction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The row offset embeds a full-width rectangular strip in the original height grid. Distances and edge increments refer to this same ambient array."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miurastriprigidity-one-exit-strip-rigid"),
                DeclarationHandle.Create(Prefix + "one_exit_strip_rigid"), H("Rigidity from one uphill exit"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("All maxima of the restricted array lie on its exit row: a restricted maximum elsewhere would also be an ambient maximum, because every existing outward edge above the strip is downhill. The finite maximum envelope and the row Lipschitz bound then force each column to have constant upward unit increment toward that row. A physical top boundary has no outward edge and satisfies the condition vacuously."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miura-occupied-strip-maximum"),
                DeclarationHandle.Create(Prefix + "occupied_internal_strip_has_maximum"),
                H("An occupied internal strip forces a maximum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("In an internal strip whose outward top edges are downhill, an ambient extremum before the exit row forces an ambient maximum there. If no maximum existed, one-exit rigidity would make every vertex have a lower neighbour above, excluding a minimum as well."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miura-first-reversal-maximum"),
                DeclarationHandle.Create(Prefix + "first_reversal_has_maximum"),
                H("A slope reversal exposes an ambient maximum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("After a whole upward cut, suppose at least one edge of the next cut points downward. Choose a column of largest height among those reversing edges. Unit horizontal increments in both rows force both existing horizontal neighbours to be lower, even at an endpoint or when the chosen maximum has a nonadjacent tie. The preceding and succeeding vertical neighbours are lower too, so this is a full-grid maximum."))), DescribeRole.Theorem))));
}
