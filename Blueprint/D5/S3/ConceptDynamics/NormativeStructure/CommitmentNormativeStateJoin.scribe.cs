using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.NormativeStructure;

internal sealed class CommitmentNormativeStateJoinDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Commitment memory obstructs endpoint reduction and forces the joint normative readout.",
        H("Commitment Normative State Join"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("commitment-normative-state-join"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/NormativeStructure/CommitmentNormativeStateJoin."
                        + "commitment_normative_state_join"),
                H("Commitment memory requires the joint normative state"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The physical endpoint and committed-permission ledger are independent "
                            + "readouts on the same history carrier. Two histories share an "
                            + "endpoint but have different committed permissions.")),
                    Paragraph(Text(
                        "The first public conclusion denies every permission readout that factors "
                            + "through physical state alone. The second quantifies over every "
                            + "candidate normative state retaining both source readouts and makes "
                            + "it refine their canonical conceptJoin.")),
                    Paragraph(Text(
                        "The obstruction and universal join clauses are imported family results; "
                            + "no endpoint, ledger, candidate state, or target relation is "
                            + "defined from the conclusions."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

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

    private static Formula TheoremFormula()
    {
        Formula history = F.Id("History");
        Formula physical = F.Id("PhysicalState");
        Formula policy = F.Id("Policy");
        Formula endpoint = F.Id("endpoint");
        Formula commitments = F.Id("committedPermissions");
        Formula first = F.Id("first");
        Formula second = F.Id("second");
        Formula statePermissions = F.Id("statePermissions");
        Formula normativeCarrier = F.Id("NormativeState");
        Formula normativeState = F.Id("normativeState");
        Formula policySet = Seq(Operatorname, Grp(F.Id("Set")), Open, policy, Close);
        Formula sameEndpoint = Seq(
            Apply(endpoint, first), Sp, Eq, Sp, Apply(endpoint, second));
        Formula differentCommitments = Seq(
            Apply(commitments, first), Sp, Neq, Sp, Apply(commitments, second));
        Formula noEndpointFactor = Seq(
            Neg, Sp, Open, Exists, Sp, statePermissions, Colon, Sp,
            Arrow(physical, policySet), Comma, Sp,
            commitments, Sp, Eq, Sp,
            Call("compose", statePermissions, endpoint), Close);
        Formula retained = Seq(
            Call("Refines", endpoint, normativeState), Sp, Land, Sp,
            Call("Refines", commitments, normativeState));
        Formula joinLowerBound = Seq(
            Forall, Sp, normativeCarrier, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            normativeState, Colon, Sp, Arrow(history, normativeCarrier), Comma,
            RowBreak, Grp(), retained, Sp, Rightarrow, Sp,
            Call("Refines", Call("conceptJoin", endpoint, commitments), normativeState));

        return Disp(Seq(
            Forall, Sp, history, Comma, Sp, physical, Comma, Sp, policy,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            endpoint, Colon, Sp, Arrow(history, physical), Comma, Sp,
            commitments, Colon, Sp, Arrow(history, policySet), Comma,
            RowBreak, Grp(), first, Comma, Sp, second, Colon, Sp, history,
            Comma, RowBreak, Grp(),
            Open, sameEndpoint, Sp, Land, Sp, differentCommitments, Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Open, noEndpointFactor, Sp, Land, RowBreak, Grp(),
            joinLowerBound, Close, Dot));
    }
}
