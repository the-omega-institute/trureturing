using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class FridNumeralsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frid prefix lengths in Fibonacci numeration", H("Frid prefix lengths in Fibonacci numeration"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-fridnumerals-n"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/FridNumerals.N"),
                H("N"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"k",Naturals(),Equal(Call("N",F.Id("k")),Call("fst",Call("fibPair",Call("append",Call("wordPower",Subtract(Multiply(D(2),F.Id("k")),D(1)),Call("list",D(1),D(0),D(0))),Call("list",D(1),D(0),D(1))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Words/frid2018numerationpalindromes")),
                Blocks(Paragraph(Text("Conjecture 2 on printed page 12 states: “For every k ≥ 1, the prefix of the Fibonacci word of length (100)²ᵏ⁻¹101 cannot be decomposed as a concatenation of at most 2k palindromes.” N(k) is the value of its stated numeral. The digits are read most significant first. wordPower repeats the block [1,0,0]. fibPair uses weights G(0)=1 and G(1)=2. The natural subtraction 2k-1 is truncated at zero; the conjecture only uses k at least one."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frid-prefix-fridnumerals-frid-numeral-twice"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/FridNumerals.frid_numeral_twice"),
                H("frid_numeral_twice"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"m",Naturals(),Equal(Multiply(D(2),Call("fst",Call("fibPair",Call("append",Call("wordPower",F.Id("m"),Call("list",D(1),D(0),D(0))),Call("list",D(1),D(0),D(1)))))),Call("fib",Add(Multiply(D(3),F.Id("m")),D(6))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Fibonacci recurrence yields this exact integer identity by induction on the repeated block. Here fib(0)=0 and fib(1)=1."))), DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
