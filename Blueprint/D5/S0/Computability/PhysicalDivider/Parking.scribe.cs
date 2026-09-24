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
            Paragraph(Text(
                "Fix an active tape k, a continuation next, a family of tapes t, Boolean lists "
                + "b and a, and an integer H. Put n = length(b). Assume 2n <= H and "
                + "Within(stackWithAbove(b,a),(2n,0,H)). Let S be accountedBlockStep extended "
                + "to optional states by binding, and let P be physicalStep extended in the "
                + "same way. Powers denote iteration and some denotes a present state.")),
            Paragraph(Text(
                "Let I = ((parkMarker,stackWithAbove(b,a)),(2n,0,H)). Let O be the tape "
                + "at the origin with empty left list and right list [false,true], followed "
                + "by [true,v] for each bit v of reverse(b), followed by a. Let E be the "
                + "block configuration (finished none,O). For a block configuration x, "
                + "write L(x) = liftBlockCfg(k,next,t,x). Let C be the physical configuration "
                + "with control continueBlock(next,none) and tape family t updated at k to O. "
                + "For an accounted state c, c1 and c2 denote its block configuration and "
                + "extent; low(c), high(c) and head(c) are the fields of c2, and "
                + "W(c) means Within(c1.tape,c2).")),
            Describe.Lean(
                DescribeId.Create("physical-parking-preserves-extent"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/PhysicalDivider/Parking.park_preserves_extent"),
                H("Counted parking with support and visited-position bounds"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("S"), Caret, Grp(D(3), F.Id("n"), Plus, D(1)),
                    Open, F.Id("some"), Open, F.Id("I"), Close, Close, Eq,
                    F.Id("some"), Open, Open, F.Id("E"), Comma, Open,
                    D(0), Comma, D(0), Comma, F.Id("H"), Close, Close, Close, Sp, Land, Sp,
                    F.Id("P"), Caret, Grp(D(3), F.Id("n"), Plus, D(2)),
                    Open, F.Id("some"), Open, F.Id("L"), Open, F.Id("I"), Underscore, D(1),
                    Close, Close, Close, Eq, F.Id("some"), Open, F.Id("C"), Close, Sp, Land, Sp,
                    Forall, Sp, F.Id("i"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("i"), Le, Sp, D(3), F.Id("n"), Plus, D(1), Sp, Implies, Sp,
                    Exists, Sp, F.Id("c"), InMacro, Sp, F.Id("BlockCfg"), Times, Sp, F.Id("Extent"), Comma, Sp,
                    F.Id("S"), Caret, F.Id("i"), Open, F.Id("some"), Open, F.Id("I"), Close, Close,
                    Eq, F.Id("some"), Open, F.Id("c"), Close, Sp, Land, Sp,
                    F.Id("P"), Caret, F.Id("i"), Open, F.Id("some"), Open,
                    F.Id("L"), Open, F.Id("I"), Underscore, D(1), Close, Close, Close, Eq,
                    F.Id("some"), Open, F.Id("L"), Open, F.Id("c"), Underscore, D(1), Close, Close, Sp, Land, Sp,
                    F.Id("low"), Open, F.Id("c"), Close, Eq, D(0), Sp, Land, Sp,
                    F.Id("high"), Open, F.Id("c"), Close, Eq, F.Id("H"), Sp, Land, Sp,
                    D(0), Le, Sp, F.Id("head"), Open, F.Id("c"), Close, Le, Sp, D(2), F.Id("n"), Sp, Land, Sp,
                    F.Id("W"), Open, F.Id("c"), Close, Dot))),
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
