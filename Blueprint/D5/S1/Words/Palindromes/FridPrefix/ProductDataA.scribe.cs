using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class ProductDataADocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal reachable product-state table is grouped by endpoint state q and first rank state p", H("The literal reachable product-state table is grouped by endpoint state q and first rank state p"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-productdataa-rawgroupsa"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/ProductDataA.rawGroupsA"),
                H("rawGroupsA"), StatementSource.FromAuthor(Disp(Seq(F.Id("rawGroupsA"),Colon,Call("Array",Call("Array",Call("List",Naturals())))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal reachable product-state table is grouped by endpoint state q and first rank state p. Its list at (q,p) contains the permitted second rank states s. There are 17 endpoint rows and 99 first-rank columns."))), DescribeRole.Definition))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
}
