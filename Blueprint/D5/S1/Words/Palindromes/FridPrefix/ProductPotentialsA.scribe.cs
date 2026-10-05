using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class ProductPotentialsADocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compressed co-accessibility and product potentials", H("Compressed co-accessibility and product potentials"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-productpotentialsa-coremasksa"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/ProductPotentialsA.coreMasksA"),
                H("coreMasksA"), StatementSource.FromAuthor(Disp(Seq(F.Id("coreMasksA"),Colon,Call("Array",Call("Array",Naturals()))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At (q,p), bit s of the stored natural number indicates co-accessibility of the triple (q,p,s). These are the literal masks tested by the product proof."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-productpotentialsa-potentialdigitsa"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/ProductPotentialsA.potentialDigitsA"),
                H("potentialDigitsA"), StatementSource.FromAuthor(Disp(Seq(F.Id("potentialDigitsA"),Colon,Call("Array",Call("Array",Naturals()))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At (q,p), the three-bit digit starting at bit 3s encodes U(q,p,s)+2. The decoder performs a right shift followed by remainder modulo 8 and an integer subtraction of 2. The literal arrays are printed in Lean."))), DescribeRole.Definition))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
}
