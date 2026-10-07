using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class ProductMovesADocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The seventeen literal arrays store all 829 endpoint moves for six-bit chunks", H("The seventeen literal arrays store all 829 endpoint moves for six-bit chunks"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-productmovesa-movesa"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/ProductMovesA.movesA"),
                H("movesA"), StatementSource.FromAuthor(Disp(Seq(F.Id("movesA"),Colon,Call("Array",Call("Array",Tuple(Naturals(),Naturals(),Naturals())))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The seventeen literal arrays store all 829 endpoint moves for six-bit chunks. Each triple is (first chunk, second chunk, endpoint destination). The checker verifies equality with movesFrom(q,6)."))), DescribeRole.Definition))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Tuple(params Formula[] items) => Call("tuple", items);
}
