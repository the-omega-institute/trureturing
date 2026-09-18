using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.PhysicalDivider;

internal sealed class ParkingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The divider's bit-tape parking loop returns to the fixed origin without enlarging its charged extent.",
        H("Parking a Divider Tape"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("physical-parking-preserves-extent"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/PhysicalDivider/Parking.park_preserves_extent"),
                H("Counted parking with support and visited-position bounds"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("T"), Eq, D(3), F.Id("n"), Plus, D(2), Comma, Sp,
                    Forall, Sp, F.Id("i"), Le, Sp, D(3), F.Id("n"), Plus, D(1), Comma, Sp,
                    D(0), Le, Sp, F.Id("h"), Underscore, F.Id("i"), Le, Sp, D(2), F.Id("n"), Comma, Sp,
                    F.Id("L"), Underscore, F.Id("i"), Eq, D(0), Comma, Sp, F.Id("H"), Underscore, F.Id("i"), Eq, F.Id("H"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A Boolean stack uses two cells per block. The bottom marker is 01, "
                        + "a data block is 1b, and blank cells are zero. The head begins at "
                        + "coordinate twice the number of data blocks below it. Arbitrary "
                        + "already traversed cells may remain above the head. The initial "
                        + "support and head must lie in the charged interval from zero to H.")),
                    Paragraph(Text(
                        "Parking reads the current marker. At a data block it moves left "
                        + "twice and repeats; at the bottom marker it finishes. For n blocks "
                        + "this requires exactly 3n+1 elementary actions. One additional read "
                        + "executes the finite continuation in the full divider program. "
                        + "All other tapes retain their exact values and positions.")),
                    Paragraph(Text(
                        "At every intermediate action the head lies between zero and its "
                        + "initial position. The lower and upper charged endpoints remain "
                        + "zero and H, and every nonblank cell stays inside that interval. "
                        + "The upper endpoint is preserved even when it records earlier "
                        + "visits or erased cells. The proof inducts over the blocks, proves "
                        + "the three-action transition to the next block, and lifts each "
                        + "block action to the concrete divider transition.")),
                    Paragraph(Text(
                        "This theorem concerns the parking phase. Arithmetic refinement, "
                        + "the complete call time bound, and the complete call space bound "
                        + "are separate statements."))),
                DescribeRole.Theorem))));
}
