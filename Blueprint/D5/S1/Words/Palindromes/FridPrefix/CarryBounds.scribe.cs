using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class CarryBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete box for signed Fibonacci carries", H("A complete box for signed Fibonacci carries"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-carrybounds-carrystep"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/CarryBounds.carryStep"),
                H("carryStep"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"s",Tuple(Integers(),Integers()),Bind(FormulaQuantifier.ForAll,"c",Integers(),Equal(Call("carryStep",F.Id("s"),F.Id("c")),Tuple(Add(Call("snd",F.Id("s")),F.Id("c")),Add(Call("fst",F.Id("s")),Call("snd",F.Id("s"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One most-significant signed digit updates the two Fibonacci residual coordinates."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-carrybounds-complete-carry-box"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/CarryBounds.complete_carry_box"),
                H("complete_carry_box"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"before",Call("List",Integers()),Bind(FormulaQuantifier.ForAll,"after",Call("List",Integers()),Implies(And(Bind(FormulaQuantifier.ForAll,"c",Integers(),Implies(Call("mem",F.Id("c"),Call("append",F.Id("before"),F.Id("after"))),AtMost(Call("abs",Call("real",F.Id("c"))),D(2)))),Equal(Add(Call("fst",Call("foldl",F.Id("carryStep"),Tuple(D(0),D(0)),Call("append",F.Id("before"),F.Id("after")))),Multiply(D(2),Call("snd",Call("foldl",F.Id("carryStep"),Tuple(D(0),D(0)),Call("append",F.Id("before"),F.Id("after")))))),D(1))),And(AtMost(Subtract(D(0),D(4)),Call("fst",Call("foldl",F.Id("carryStep"),Tuple(D(0),D(0)),F.Id("before")))),And(AtMost(Call("fst",Call("foldl",F.Id("carryStep"),Tuple(D(0),D(0)),F.Id("before"))),D(4)),And(AtMost(Subtract(D(0),D(3)),Call("snd",Call("foldl",F.Id("carryStep"),Tuple(D(0),D(0)),F.Id("before")))),AtMost(Call("snd",Call("foldl",F.Id("carryStep"),Tuple(D(0),D(0)),F.Id("before"))),D(3)))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The hypotheses concern the full signed word, and the conclusion concerns its specified prefix. Expanding and contracting golden-ratio coordinates give simultaneous strip bounds; integrality restricts the prefix carry to this finite box."))), DescribeRole.Theorem))));

    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Tuple(params Formula[] items) => Call("tuple", items);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
