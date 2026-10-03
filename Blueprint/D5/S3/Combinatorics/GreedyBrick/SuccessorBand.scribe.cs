using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GreedyBrick;

internal sealed class SuccessorBandDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact-reset chronological event histories satisfy the successor birth band.",
        H("Successor Band for Exact-Reset Event Histories"),
        Blocks(Describe.Lean(
            DescribeId.Create("successor-band"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/GreedyBrick/SuccessorBand.successor_band"),
            H("Chronological predecessor injection bounds the renewal height"),
            StatementSource.FromAuthor(Disp(Seq(
                F.Id("b"), Underscore, Grp(F.Id("h")), Sp, Leq, Sp,
                F.Id("H"), Sp, Lt, Sp, F.Id("b"), Underscore,
                Grp(F.Id("h"), Plus, D(1))))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "An event history has chronological indices, positive bin labels bounded by "
                    + "nondecreasing heights, total positive-height births with exact strict cuts, "
                    + "brick endpoints whose increments equal event labels, and immediate same-bin "
                    + "predecessors of renewals. Its reset balance states n+h+rho(e)=H+rho(f), "
                    + "where rho counts strictly earlier renewals at higher bins. Under these "
                    + "explicit laws, every renewal f with predecessor e of height h has height H "
                    + "between the actual birth endpoints b_h and b_(h+1).")),
                Paragraph(Text(
                    "For a first hypothetical lower-band violation, strong chronological induction "
                    + "puts every earlier renewal's predecessor before birth h. Immediate "
                    + "predecessors pair injectively. Births in that strict cut inject into their "
                    + "distinct labels above the current bin and below h; remaining events are "
                    + "earlier higher-bin renewals. Their combined count contradicts the reset "
                    + "balance. The upper band uses the length h+1 of the next birth event.")),
                Paragraph(Text(
                    "This is a conditional event-history component for OEIS A395531. The literal "
                    + "highest-eligible-row process must still supply the rest-event correspondence, "
                    + "first-zero transition, total birth indices, predecessor laws, and reset "
                    + "balance. Future same-bin successor existence, the cut bijection, weighted "
                    + "reciprocity, and the original all-index identity are not delivered here."))),
            DescribeRole.Theorem)),
        []));
}
