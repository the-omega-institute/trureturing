using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class LanguageDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite languages and the closed endpoint-complement monitor", H("Finite languages and the closed endpoint-complement monitor"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-languagedata-badrows"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/LanguageData.badRows"),
                H("badRows"), StatementSource.FromAuthor(Disp(Seq(F.Id("badRows"),Colon,Call("List",Call("List",Naturals()))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal 138-row transition mask table tracks two canonical interior words, comparisons with the endpoints, and signed reflection carries. Each row has four paired-digit symbols."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-languagedata-endpointmasks"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/LanguageData.endpointMasks"),
                H("endpointMasks"), StatementSource.FromAuthor(Disp(Seq(F.Id("endpointMasks"),Colon,Call("List",Call("List",Naturals()))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal seventeen-row transition masks encode endpointRows on symbols 2x+y, with x and y binary."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-languagedata-signature"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/LanguageData.Signature"),
                H("Signature"), StatementSource.FromAuthor(Disp(Seq(F.Id("Signature"),Colon,F.Id("Type")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The record fields are bad : Nat, endpoint : Nat, previousX : Nat, previousY : Nat, strict : Bool, and valid : Bool. It derives DecidableEq; no extra condition is imposed by the type."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-languagedata-signature-decidableeq"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/LanguageData.instDecidableEqSignature"),
                H("instDecidableEqSignature"), StatementSource.FromAuthor(Disp(Seq(F.Id("instDecidableEqSignature"),Colon,Call("DecidableEq",F.Id("Signature"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The derived instance decides equality of signatures by comparing their four natural coordinates and two Boolean coordinates."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-languagedata-certificate"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/LanguageData.certificate"),
                H("certificate"), StatementSource.FromAuthor(Disp(Seq(F.Id("certificate"),Colon,Call("List",F.Id("Signature"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The literal 105 monitor signatures include the invalid sink and all monitor states reachable from the initial signature. Closure and the endpoint-complement assertion are kernel checked for every listed state."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-languagedata-badstart"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/LanguageData.badStart"),
                H("badStart"), StatementSource.FromAuthor(Disp(Equal(F.Id("badStart"),D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The natural numeral is a bit mask; bit q indicates membership of state q in this start or accept set."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-languagedata-endpointstart"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/LanguageData.endpointStart"),
                H("endpointStart"), StatementSource.FromAuthor(Disp(Equal(F.Id("endpointStart"),D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The natural numeral is a bit mask; bit q indicates membership of state q in this start or accept set."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-languagedata-badaccept"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/LanguageData.badAccept"),
                H("badAccept"), StatementSource.FromAuthor(Disp(Equal(F.Id("badAccept"),D(2,5,5,2,1,2,4,3,4,4,0,0,5,8,3,4,4,7,0,9,2,5,5,3,0,7,8,8,9,6,7,3,1,3,5,7,5,6,8)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The natural numeral is a bit mask; bit q indicates membership of state q in this start or accept set."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-languagedata-endpointaccept"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/LanguageData.endpointAccept"),
                H("endpointAccept"), StatementSource.FromAuthor(Disp(Equal(F.Id("endpointAccept"),D(2,5,6,8)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The natural numeral is a bit mask; bit q indicates membership of state q in this start or accept set."))), DescribeRole.Definition))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
