using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.NativeReader;

internal sealed class CarrierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All original source paths.",
        H("All original source paths"),
        Blocks(Describe.Lean(
            DescribeId.Create("source-card"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeReader/Carrier.source_card"),
            H("All original source paths"), StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Source is the full binary legal-path set on b0 through b10, with endpoints zero and no adjacent ones. The fixed exterior is b(-1)=1 and b11=1,b12=0. Extended is the corresponding full path set on b0 through b14 with endpoints zero and fixed b15=1,b16=0. The source sector is selected only by b9; no code or complement coordinate is discarded. Tail(i) consists of all paths (i,z10,z11,z12,z13,z14,1). The unique ready tail is (i,0,1,0,0,0,1). The actual report is b13. The unique original ready source has b3=b7=1 and every other b0..b10 zero, the literal J(e00100,0).")), Paragraph(Text("The pathWordEquiv identifies the nine free internal source bits with the existing admissible-word type. The frozen admissibleWord_card_eq_fib supplies 89. The same equivalence on thirteen free internal extended bits supplies extended_card=610. These counts are reused normalization, not new content. The Perron weights d(false)=1,d(true)=x satisfy the neighbor sum identity with delta equal to the golden ratio; x_properties is consumed at its original owner. The definitions and count helpers are used by the full-carrier zero-trigger history theorem."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Statement() => Disp(Seq(Call("card", F.Id("Source")), Sp, Eq, Sp, D(89)));
}
