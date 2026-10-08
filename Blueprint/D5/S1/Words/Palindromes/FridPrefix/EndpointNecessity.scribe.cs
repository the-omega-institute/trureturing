using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class EndpointNecessityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Palindrome reflection forces the paired endpoint language", H("Palindrome reflection forces the paired endpoint language"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-endpointnecessity-palindrome-endpoint"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/EndpointNecessity.palindrome_endpoint"),
                H("palindrome_endpoint"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"u",Call("List",Call("Fin",D(2))),Bind(FormulaQuantifier.ForAll,"v",Call("List",Call("Fin",D(2))),Implies(And(Call("NoAdjacentOnes",F.Id("u")),And(Call("NoAdjacentOnes",F.Id("v")),And(Equal(Call("length",F.Id("u")),Call("length",F.Id("v"))),And(Less(Call("fst",Call("fibPair",F.Id("u"))),Call("fst",Call("fibPair",F.Id("v")))),Call("Palindrome",Call("goldenFactor",Subtract(Call("fst",Call("fibPair",F.Id("v"))),Call("fst",Call("fibPair",F.Id("u")))),Call("fst",Call("fibPair",F.Id("u"))))))))),Call("mem",Call("zip",F.Id("u"),F.Id("v")),Call("accepts",F.Id("endpoint")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The words are equal-width canonical Zeckendorf encodings, allowing leading zeros. Their values are the half-open interval endpoints. Canonical last digits determine goldenWord letters through wdigits. A mismatch path would give two reflected positions with different letters, contradicting palindrome reflection. The finite complement monitor therefore forces an accepting endpoint path. This assertion proves the required recognizer necessity directly; it does not assert the arithmetic CanonicalEdge equivalence."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
