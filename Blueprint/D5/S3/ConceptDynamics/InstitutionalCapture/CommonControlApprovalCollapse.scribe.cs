using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InstitutionalCapture;

internal sealed class CommonControlApprovalCollapseDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/InstitutionalCapture/CommonControlApprovalCollapse."
            + "common_control_source_approval_collapse";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint approvals and their final judgment remain below a common control source.",
        H("Common-Control Approval Collapse"),
        Blocks(Describe.Lean(
            DescribeId.Create("common-control-source-approval-collapse"),
            DeclarationHandle.Create(Declaration),
            H("A shared control source bounds both joint approvals and final authorization"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Each approval node is an independent formal coordinate, but every node "
                        + "is assumed to factor through the same source readout.")),
                Paragraph(Text(
                    "The canonical dependent joint readout therefore factors through that "
                        + "source. Composing its factor with the final authorization map gives "
                        + "an explicit source-to-judgment factor g."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula index = F.Id("I");
        Formula state = F.Id("X");
        Formula sourceType = F.Id("Source");
        Formula judgment = F.Id("Judgment");
        Formula approvalType = F.Id("B");
        Formula i = F.Id("i");
        Formula approval = F.Id("A");
        Formula source = F.Id("S");
        Formula finalize = F.Id("f");
        Formula factor = F.Id("g");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula approvalAt = new Formula.Subscript(approvalType, i);
        Formula approvalProfile = Grp(
            Forall, Sp, i, Colon, Sp, index, Comma, Sp, approvalAt);
        Formula joint = Call("jointReadout", approval);
        Formula componentBound = Seq(
            Forall, Sp, i, Colon, Sp, index, Comma, Sp,
            Call("Refines", new Formula.Apply(approval, [i]), source));
        Formula finalFactorization = Seq(
            finalize, Sp, Circ, Sp, joint, Sp, Eq, Sp,
            factor, Sp, Circ, Sp, source);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, index, Comma, Sp, state, Comma, Sp, sourceType,
                Comma, Sp, judgment, Colon, Sp, type, Comma, Sp,
                approvalType, Colon, Sp, index, Sp, To, Sp, type, Comma),
            Seq(
                approval, Colon, Sp, Forall, Sp, i, Colon, Sp, index, Comma, Sp,
                state, Sp, To, Sp, approvalAt, Comma),
            Seq(
                source, Colon, Sp, state, Sp, To, Sp, sourceType, Comma, Sp,
                finalize, Colon, Sp, approvalProfile, Sp, To, Sp, judgment, Comma),
            Seq(
                Open, componentBound, Close, Sp, Rightarrow),
            Seq(
                Call("Refines", joint, source), Sp, Land),
            Seq(
                Exists, Sp, factor, Colon, Sp, sourceType, Sp, To, Sp, judgment,
                Comma, Sp, finalFactorization, Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}
