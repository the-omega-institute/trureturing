using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Epistemic;

internal sealed class DescriptiveAnnouncementCommutationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditioning by two descriptive announcements commutes.",
        H("Descriptive Announcement Commutation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("descriptive-announcement-commutation"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Epistemic/DescriptiveAnnouncementCommutation."
                        + "descriptive_announcement_commutation"),
                H("Descriptive announcements commute"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A descriptive announcement is the canonical operation that intersects "
                            + "the currently admitted states with the announcement predicate.")),
                    Paragraph(Text(
                        "For arbitrary state types and announcement predicates, composing the two "
                            + "conditioning operators in either order gives the same operator.")),
                    Paragraph(Text(
                        "The proof unfolds the conditioning semantics and directly applies the "
                            + "pinned-library identity Set.inter_right_comm. Repository searches "
                            + "found no pre-existing descriptive-announcement primitive."))),
                DescribeRole.Theorem))));

    private static Formula Condition(Formula announcement) =>
        Call("descriptiveCondition", announcement);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula p = F.Id("P");
        Formula q = F.Id("Q");
        Formula setOfState = Call("Set", state);
        Formula left = Seq(Condition(p), Sp, Circ, Sp, Condition(q));
        Formula right = Seq(Condition(q), Sp, Circ, Sp, Condition(p));

        return Disp(Seq(
            Forall, Sp, state, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            p, Comma, Sp, q, Colon, Sp, setOfState, Comma, RowBreak, Grp(),
            left, Sp, Eq, Sp, right, Dot));
    }
}
