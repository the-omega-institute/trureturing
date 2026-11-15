using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.NativeReader;

internal sealed class FibersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All extended coordinates split into source and tail.",
        H("All extended coordinates split into source and tail"),
        Blocks(Describe.Lean(
            DescribeId.Create("fullCarrierEquiv"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeReader/Fibers.fullCarrierEquiv"),
            H("All extended coordinates split into source and tail"), StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("DependentSourceTail denotes the dependent sum over every original source q of the complete legal tail with left boundary b9(q). originalPart keeps b0..b9 and restores the old fixed b10=0. auxiliaryPart keeps the actual b9..b14 and its fixed right boundary b15=1. joinPath reinserts the actual five auxiliary positions. Its seam legality is proved using the shared b9 and the original and auxiliary boundary conditions.")), Paragraph(Text("The definition fullCarrierEquiv is an actual equivalence between the complete extended legal-path set and this dependent sum. join_split and original_join prove both reconstruction directions; the dependent tail equality retains all coordinates. This is the full direct-sum decomposition, not a restriction to the ready interface or to a fixed tail matrix. The equivalence is consumed by finite summation in the exact global native projection action. It provides no source process, probability law or causal archive."))), DescribeRole.Definition))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Statement() => Disp(Seq(F.Id("Extended"), Sp, Equiv, Sp, Call("DependentSourceTail", F.Id("Source"), F.Id("Tail"))));
}
