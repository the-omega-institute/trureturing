using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class NumeralSemanticsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical digit order and Fibonacci value", H("Canonical digit order and Fibonacci value"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-numeralsemantics-canonical-lex-value"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/NumeralSemantics.canonical_lex_value"),
                H("canonical_lex_value"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"u",Call("List",Call("Fin",D(2))),Bind(FormulaQuantifier.ForAll,"v",Call("List",Call("Fin",D(2))),Implies(And(Call("NoAdjacentOnes",F.Id("u")),And(Call("NoAdjacentOnes",F.Id("v")),Equal(Call("length",F.Id("u")),Call("length",F.Id("v"))))),Biconditional(Less(Call("fst",Call("fibPair",F.Id("u"))),Call("fst",Call("fibPair",F.Id("v")))),Call("Lex",Function("a",Call("Fin",D(2)),Function("b",Call("Fin",D(2)),Less(F.Id("a"),F.Id("b")))),F.Id("u"),F.Id("v")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Leading zero digits are permitted. NoAdjacentOnes forbids consecutive one digits. Equal-width canonical words are ordered numerically exactly as they are lexicographically; the strict tail bound follows from the Fibonacci recurrence."))), DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Function(string variable, Formula domain, Formula body) => Seq(LambdaLower, Sp, Parenthesized(Seq(F.Id(variable), Colon, domain)), Sp, Mapsto, Sp, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Biconditional(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Iff, right);
}
