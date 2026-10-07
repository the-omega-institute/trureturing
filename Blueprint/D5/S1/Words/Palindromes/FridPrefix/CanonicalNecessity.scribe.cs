using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class CanonicalNecessityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal zero-digit rule for every Fibonacci palindrome", H("The literal zero-digit rule for every Fibonacci palindrome"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-canonicalnecessity-frid-canonical-necessity"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/CanonicalNecessity.frid_canonical_necessity"),
                H("frid_canonical_necessity"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"i",Naturals(),Bind(FormulaQuantifier.ForAll,"j",Naturals(),Implies(And(Less(F.Id("i"),F.Id("j")),Call("Palindrome",Call("goldenFactor",Subtract(F.Id("j"),F.Id("i")),F.Id("i")))),Bind(FormulaQuantifier.Exists,"m",Naturals(),And(Call("not",Call("mem",Add(F.Id("m"),D(2)),Call("wdigits",F.Id("i")))),Equal(Call("int",F.Id("j")),Subtract(Subtract(Add(Call("int",F.Id("i")),Call("int",Call("wValue",Add(F.Id("m"),D(2))))),D(2)),Multiply(D(2),Call("int",Call("sum",Call("map",F.Id("fib"),Call("filter",Function("r",Naturals(),Less(F.Id("r"),Add(F.Id("m"),D(2)))),Call("wdigits",F.Id("i")))))))))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Words/frid2018numerationpalindromes")),
                Blocks(Paragraph(Text("Theorem 1, printed pages 10–11, begins: “Let w be a characteristic Sturmian word corresponding to the directive sequence (dₙ), and w(i..j] = w[i + 1] . . . w[j] be a palindrome. Denote the Ostrowski representation of i as i = xₙ ··· xₘ ··· x₀ [o]; note that it may start with several leading zeros. Then there exist a legal representation of j given by j = xₙ ··· xₘ₊₁ yₘ · (dₘ₋₁ − xₘ₋₁) ··· (d₀ − x₀), where 0 ≤ m ≤ n and xₘ < yₘ ≤ dₘ.” For the Fibonacci directive sequence all dₘ equal one: the selected canonical digit is zero, becomes one, and every lower digit is complemented. wdigits stores Fibonacci indices beginning at 2; the selected position m therefore has stored index m+2. wValue(m+2)=fib(m+4), and the filtered sum is the value of all canonical digits strictly below that index. The endpoint equation is an integer equation; the factor uses natural subtraction on the increasing interval. Zero residual carries identify the reconstructed legal numeral with j. No endpoint necessity is assumed."))), DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Function(string variable, Formula domain, Formula body) => Seq(LambdaLower, Sp, Parenthesized(Seq(F.Id(variable), Colon, domain)), Sp, Mapsto, Sp, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);

}
