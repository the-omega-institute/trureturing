using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.VertexModels;

internal sealed class PonciniRasmussenNineActionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact action in the diagram algebra", H("Exact action in the diagram algebra"), Blocks(
            Paragraph(Text("R is any commutative coefficient ring. The statements concern multiplication in TL(R,9), whose basis contains every noncrossing boundary matching. They follow from the checked table and the general cup-cap path and loop laws.")),
            Describe.Lean(DescribeId.Create("unit-basis"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineAction.unit_basis"),
                H("unit_basis"), StatementSource.FromAuthor(Disp(RingAll("R", Equal(Call("Single", Call("diagram", Num(4861)), Num(1)), Num(1))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The basis vector at coordinate 4861 equals the multiplicative identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("generator-basis"), DeclarationHandle.Create("D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineAction.generator_basis"),
                H("generator_basis"), StatementSource.FromAuthor(Disp(RingAll("R", All("g", Call("Fin", Num(8)), All("i", Call("Fin", Num(4862)), Equal(Call("Multiply", Call("generator", Id("g")), Call("Single", Call("diagram", Id("i")), Num(1))), Call("IfLess", Call("val", Call("transition", Id("g"), Id("i"))), Num(4862), Call("Single", Call("diagram", Call("transition", Id("g"), Id("i"))), Num(1)), Num(0)))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every generator acts by exactly the indicated target basis vector, or by zero when an internal loop is formed."))), DescribeRole.Theorem))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula RingAll(string name, Formula body) => All(name, Id("Type"), Seq(OpenBracket, Call("CommRing", Id(name)), CloseBracket, Sp, body));
}
