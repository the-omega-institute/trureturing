using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.OppositeFirstThirdMaximum;
internal sealed class PhysicalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two physical strips from shared charges", H("Two physical strips from shared charges"),
        Blocks(Paragraph(Text("For bank masses p and terminal values q, heads are p0, p0+q0+p1 and p0+q0+p1+q1+p2; seams add the following terminal. The enlarged row adds the sole fresh value A to bank1 or bank3 in the corresponding original order.")),
            Paragraph(Text("complete_checks reconstructs both rows of head and seam inequalities from six mixed margins. Each shared bank and terminal has nonnegative charge 2*old-new. The old total is zero and the shared enlarged total is -A. Before the insertion, enlarged lower bounds imply old lower bounds and old upper bounds imply enlarged upper bounds. After insertion the corresponding implications use the complementary suffix and both total identities.")),
            Paragraph(Text("Under 2<=b, 2<=d, b<a, d<a and the sector condition (b<d or d+2<=b), the Arithmetic construction supplies a natural mask below 2^(a-1) with all six required gates nonnegative in either sector. physical_joint uses the original-label inventory, actual chain values and exact bank masses. Polynomial identities equate the six physical margins with the Arithmetic gates. Nonnegative individual bank values let four_strip control every intermediate prefix, rather than only the bank boundaries. Native terminal bounds control the final bank and terminal; source_totals supplies both independent zero sums.")),
            Paragraph(Text("The source-to-Fin equivalence actual_nat_joint_iff transports the old permutation and the literal natural-label insertion to OriginalOrder for the original seed and its doubled enlarged seed. The Endpoint then extends these finite periods to all natural replicate/flatten/take windows and proves the two repeated zero totals."))), []));
}
