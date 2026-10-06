using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class RankAutomataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral ranks accumulated on finite chunk runs", H("Integral ranks accumulated on finite chunk runs"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-rankautomata-chunkrank"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/RankAutomata.ChunkRank"),
                H("ChunkRank"), StatementSource.FromAuthor(Disp(Seq(F.Id("ChunkRank"),Colon,F.Id("Type")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("ChunkRank is the record with width : Nat, initial : Nat, transitions : Array (Array Nat), and weights : Array (Array Int). Transitions outside the stored arrays use destination 0 and weight 0 in the evaluator."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-rankautomata-chunkscore"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/RankAutomata.chunkScore"),
                H("chunkScore"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"r",F.Id("ChunkRank"),Bind(FormulaQuantifier.ForAll,"xs",Call("List",Naturals()),Equal(Call("chunkScore",F.Id("r"),F.Id("xs")),Call("snd",Call("foldl",Function("s",Tuple(Naturals(),Integers()),Function("x",Naturals(),Tuple(Call("getD",Call("getD",Call("transitions",F.Id("r")),Call("fst",F.Id("s")),F.Id("emptyArray")),F.Id("x"),D(0)),Add(Call("snd",F.Id("s")),Call("getD",Call("getD",Call("weights",F.Id("r")),Call("fst",F.Id("s")),F.Id("emptyArray")),F.Id("x"),D(0)))))),Tuple(Call("initial",F.Id("r")),D(0)),F.Id("xs")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The state and accumulated integer weight are updated together. No terminal weight is added; the second coordinate of the final pair is the score."))), DescribeRole.Definition))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Tuple(params Formula[] items) => Call("tuple", items);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Function(string variable, Formula domain, Formula body) => Seq(LambdaLower, Sp, Parenthesized(Seq(F.Id(variable), Colon, domain)), Sp, Mapsto, Sp, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
}
