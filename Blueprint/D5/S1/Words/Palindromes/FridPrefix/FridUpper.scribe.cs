using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class FridUpperDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit upper bound for Frid prefixes", H("An explicit upper bound for Frid prefixes"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-fridupper-frid-upper"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/FridUpper.frid_upper"),
                H("frid_upper"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"k",Naturals(),Implies(AtMost(D(1),F.Id("k")),AtMost(Call("PL",Call("goldenFactor",Call("N",F.Id("k")),D(0))),Add(Multiply(D(2),F.Id("k")),D(1))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Words/frid2018numerationpalindromes")),
                Blocks(Paragraph(Text("Frid writes on printed page 12: “We proved that 2k + 1 palindromes are enough for this word, so, it remains just to prove that this is the minimal possible value.” The proof uses consecutive symmetric trims of Fibonacci central palindromes. True represents the letter 0 and false the letter 1."))), DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula AtMost(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
