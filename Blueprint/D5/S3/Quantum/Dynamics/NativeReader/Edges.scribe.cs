using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.NativeReader;

internal sealed class EdgesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact full-vector two-point restriction.",
        H("Exact full-vector two-point restriction"),
        Blocks(Describe.Lean(
            DescribeId.Create("projection-edge-mulVec"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeReader/Edges.projection_edge_mulVec"),
            H("Exact full-vector two-point restriction"), StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The Boolean a selects physical address eleven when false and thirteen when true. The actual edge configurations differ only at tail position two or four, respectively. They are ordered by that physical center bit. The ready tail has center not-a, and the opposite configuration has center a. Both configurations are legal for each source sector. The exact block is sourceQ=((x,x*sqrt(x)),(x*sqrt(x),x*x)); there is no basis or gauge replacement.")), Paragraph(Text("ProjectionEdgeAction(i,a,v,b) is the ready-edge row of projection(i,changedAddress(a)) applied to the complete tail vector v. SourceQAction is (sourceQ*pairVector(i,a,v))(b). The theorem quantifies over both sectors, both addresses, every complete complex vector and both edge rows. The proof first shows every other legal tail contributes zero, then evaluates both retained entries using the original weights and sums the two-point support. The complete input vector remains unchanged as a domain object. pulse_pair transports this exact restriction to the full pulse and is consumed by charge conservation and uniform nonvanishing. The restriction does not authorize a projected state update."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Statement() => Disp(Seq(Forall, Sp, F.Id("i"), Comma, Sp, Forall, Sp, F.Id("a"), Comma, Sp, Forall, Sp, F.Id("v"), Colon, Sp, Call("TailVector", F.Id("i")), Comma, Sp, Forall, Sp, F.Id("b"), Colon, Sp, F.Id("Bool"), Comma, Sp, Call("ProjectionEdgeAction", F.Id("i"), F.Id("a"), F.Id("v"), F.Id("b")), Sp, Eq, Sp, Call("SourceQAction", F.Id("i"), F.Id("a"), F.Id("v"), F.Id("b"))));
}
