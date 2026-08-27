using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Communication;

internal sealed class DiscussionCommonSourceUpperBoundDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Communication/DiscussionCommonSourceUpperBound."
            + "discussion_common_source_upper_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The joint discussion readout and its join with a bounded initial concept "
            + "remain below their common source.",
        H("Discussion Common-Source Upper Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("discussion-and-initial-concept-remain-source-bounded"),
            DeclarationHandle.Create(Declaration),
            H("Discussion preserves a common-source upper bound"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The first clause applies the canonical indexed common-source theorem "
                        + "to the complete dependent message readout.")),
                Paragraph(Text(
                    "For the second clause, the concept-join universal property combines "
                        + "the initial-concept bound with the derived message bound."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula index = F.Id("I");
        Formula state = F.Id("X");
        Formula sourceType = F.Id("B");
        Formula initialType = F.Id("C0");
        Formula messageType = F.Id("M");
        Formula i = F.Id("i");
        Formula message = F.Id("m");
        Formula source = F.Id("s");
        Formula initial = F.Id("c0");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula messageAt = new Formula.Subscript(messageType, i);
        Formula joint = Call("jointReadout", message);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, index, Comma, Sp, state, Comma, Sp, sourceType,
                Colon, Sp, type, Comma, Sp, messageType, Colon, Sp, index,
                Sp, To, Sp, type, Comma),
            Seq(
                message, Colon, Sp, Forall, Sp, i, Colon, Sp, index, Comma, Sp,
                state, Sp, To, Sp, messageAt, Comma, Sp,
                source, Colon, Sp, state, Sp, To, Sp, sourceType, Comma),
            Seq(
                Open, Forall, Sp, i, Colon, Sp, index, Comma, Sp,
                Call("Refines", new Formula.Apply(message, [i]), source), Close,
                Sp, Rightarrow, Sp),
            Seq(
                Call("Refines", joint, source), Sp, Land, Sp),
            Seq(
                Open, Forall, Sp, initialType, Colon, Sp, type, Comma, Sp,
                initial, Colon, Sp, state, Sp, To, Sp, initialType, Comma, Sp,
                Call("Refines", initial, source), Sp, Rightarrow, Sp),
            Seq(
                Call("Refines", Call("conceptJoin", initial, joint), source),
                Close, Dot),
        ]));
    }
}
