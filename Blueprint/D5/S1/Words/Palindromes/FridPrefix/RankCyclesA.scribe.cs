using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class RankCyclesADocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact weighted cycle for the Frid digit family", H("The exact weighted cycle for the Frid digit family"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-rankcyclesa-a-seed-cycle"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/RankCyclesA.a_seed_cycle"),
                H("a_seed_cycle"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"k",Naturals(),Bind(FormulaQuantifier.ForAll,"z",Naturals(),Equal(Call("chunkScore",F.Id("rankA"),Call("append",Call("append",Call("replicate",F.Id("z"),D(0)),Call("replicate",F.Id("k"),D(3,6))),Call("singleton",D(3,7)))),Add(Multiply(D(2),Call("int",F.Id("k"))),D(3))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Numeric chunks 36 and 37 are the six-bit words 100100 and 100101. Initial zero chunks have zero weight. The repeated 36 cycle supplies weight two per repetition; the final chunk supplies the offset three."))), DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
