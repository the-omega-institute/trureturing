using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedOrdinalHistoryEventDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedOrdinalHistoryEvent.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One actual successor event", H("One actual successor event"), Blocks(
            Describe.Lean(DescribeId.Create("signedordinalhistoryevent-0"),
                DeclarationHandle.Create(Owner + "execute"), H("Once-prepared local execution"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Under CH the actual exists_prepared_step chooses one Prepared Q. The original reservation sum is read before target projection. A locally valid delayed reservation selects a DelayedTask on that same Q and retains its Result and certificate; all other reservations select an ordinary Result. The event stores exactly the selected Q and Result, together with branch and execution equations. Local delayed tests read only already born rows and labels and the clopen enumeration of their original whole birth."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("signedordinalhistoryevent-1"),
                DeclarationHandle.Create(Owner + "next_regular"), H("Incoming regular bounded convergence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The same selected Result supplies the next predecessor and its regular bounded every-choice F. Literal carrier equality transports the original signed pushforwards and weak-dual convergence. The output retains both Jordan regularity proofs and total variation at most one; this information is not inferred from the weaker Predecessor.F."))), DescribeRole.Theorem))));
}
