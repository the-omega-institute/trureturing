using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class ChunkTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Regroup endpoint paths into six-bit chunks", H("Regroup endpoint paths into six-bit chunks"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-chunktransport-endpoint-chunked"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/ChunkTransport.endpoint_chunked"),
                H("endpoint_chunked"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"us",Call("List",Call("List",Call("Fin",D(2)))),Bind(FormulaQuantifier.ForAll,"vs",Call("List",Call("List",Call("Fin",D(2)))),Implies(And(Equal(Call("length",F.Id("us")),Call("length",F.Id("vs"))),And(Bind(FormulaQuantifier.ForAll,"u",Call("List",Call("Fin",D(2))),Implies(Call("mem",F.Id("u"),F.Id("us")),Equal(Call("length",F.Id("u")),D(6)))),And(Bind(FormulaQuantifier.ForAll,"v",Call("List",Call("Fin",D(2))),Implies(Call("mem",F.Id("v"),F.Id("vs")),Equal(Call("length",F.Id("v")),D(6)))),Call("mem",Call("zip",Call("flatten",F.Id("us")),Call("flatten",F.Id("vs"))),Call("accepts",F.Id("endpoint")))))),Call("mem",Call("map",Function("p",Tuple(Call("List",Call("Fin",D(2))),Call("List",Call("Fin",D(2)))),Tuple(Call("ofDigits",D(2),Call("map",F.Id("val"),Call("reverse",Call("fst",F.Id("p"))))),Call("ofDigits",D(2),Call("map",F.Id("val"),Call("reverse",Call("snd",F.Id("p"))))))),Call("zip",F.Id("us"),F.Id("vs"))),Call("accepts",Call("chunkEndpoint",D(6))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nat.ofDigits reads least significant digits first, so each six-bit word is reversed before its digit values are passed to ofDigits. The proof decomposes and rebuilds the actual bit path at each chunk boundary, preserving the initial and terminal states."))), DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Tuple(params Formula[] items) => Call("tuple", items);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Function(string variable, Formula domain, Formula body) => Seq(LambdaLower, Sp, Parenthesized(Seq(F.Id(variable), Colon, domain)), Sp, Mapsto, Sp, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
