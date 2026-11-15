using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class ActualPsiTailEulerBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual psi Euler equation and moments",
        H("ActualPsiTailEulerBridge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-tail-bridge"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/ActualPsiTailEulerBridge.actual_tail_bridge"),
                H("Actual psi Euler equation and moments"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual signed psi tail is L1 above log 2. For every U>=log 2, its actual transform is analytic on Re s>0, all polynomial moments converge and its first two derivatives are the actual moments. The Euler expression equals Phi(U,s) on Re s>0, using the current actual-tail calculus and the actual Qpsi=Mpsi germ. This supplies the original fixed-cutoff signed_peaks API directly, without an EulerTail compatibility structure."))), DescribeRole.Theorem))));
}
