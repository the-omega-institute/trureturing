using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes.FridPrefix;

internal sealed class PotentialBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Palindromic factorisations bound integral potentials", H("Palindromic factorisations bound integral potentials"), Blocks(
            Describe.Lean(
                DescribeId.Create("frid-prefix-potentialbound-potential-pl-bound"),
                DeclarationHandle.Create("D5/S1/Words/Palindromes/FridPrefix/PotentialBound.potential_pl_bound"),
                H("potential_pl_bound"), StatementSource.FromAuthor(Disp(Bind(FormulaQuantifier.ForAll,"S",Call("Arrow",Naturals(),Integers()),Bind(FormulaQuantifier.ForAll,"n",Naturals(),Implies(And(Equal(Call("apply",F.Id("S"),D(0)),D(0)),Bind(FormulaQuantifier.ForAll,"i",Naturals(),Bind(FormulaQuantifier.ForAll,"j",Naturals(),Implies(And(Less(F.Id("i"),F.Id("j")),And(AtMost(F.Id("j"),F.Id("n")),Call("Palindrome",Call("goldenFactor",Subtract(F.Id("j"),F.Id("i")),F.Id("i"))))),AtMost(Call("apply",F.Id("S"),F.Id("j")),Add(Call("apply",F.Id("S"),F.Id("i")),D(1))))))),AtMost(Call("apply",F.Id("S"),F.Id("n")),Call("int",Call("PL",Call("goldenFactor",F.Id("n"),D(0)))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Only increasing palindrome edges whose destination is at most n are required. Induction over any nonempty palindrome factorisation telescopes the edge inequalities from the zero potential at the empty prefix."))), DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Call(string name, params Formula[] arguments) => new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Bind(FormulaQuantifier quantifier, string variable, Formula domain, Formula body) => new Formula.Bind(quantifier, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
}
