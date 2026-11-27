using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.UnorderedTrees;

internal sealed class A358587Document : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/wisemanwu2024a358587");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual unordered-tree counts satisfy Wu’s formal generating function and signed recurrence.",
        H("Wu’s Unordered Rooted-Tree Enumeration"),
        Blocks(Describe.Lean(
            DescribeId.Create("oeis-a358587-result"),
            DeclarationHandle.Create("D5/S3/Combinatorics/UnorderedTrees/A358587.result"),
            H("The generating function, initial values and recurrence"),
            StatementSource.FromAuthor(ResultFormula()),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "For each natural n, the qualifying set consists of the classes of parent maps on Fin n under "
                    + "root-preserving vertex isomorphisms, restricted to trees whose vertex height "
                    + "equals their number of internal vertices. The children are unordered. "
                    + "A singleton has vertex height one and zero internal vertices.")),
                Paragraph(Text(
                    "Pruning the original leaves gives a unique fork. At least one arm has length one, and both have length one when c=0. "
                    + "The leaf counts on its spine and tips recover the original isomorphism class. "
                    + "For equal arms the sorted tip counts have the form m+1 and m+d+1, including "
                    + "the diagonal d=0. For unequal arms the two tip counts vary independently. "
                    + "The binomial sums count these decorations for every n.")),
                Paragraph(Text(
                    "Finite coefficient substitution turns the two sums into the generating "
                    + "series over the integers. The displayed denominator has constant coefficient "
                    + "one. The signed recurrence follows by comparing coefficients above degree "
                    + "seven after multiplication by that denominator."))),
            DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var x = F.Id("X");
        var t = F.Id("T");
        var set = Seq(OpenBrace, t, Colon, Sp, Call("TreeClass", n), Sp, Mid, Sp,
            Equal(Call("classHeight", t), Call("classInternalCount", t)), CloseBrace);
        var sum = new Formula.Subscript(Seq(Sum, Caret, Grp(Infty)), Equal(k, D(0)));
        var series = Seq(sum, Sp, IntegerCount(k), new Formula.Power(x, k));
        var numerator = Seq(new Formula.Power(x, D(5)),
            Parenthesized(Seq(new Formula.Power(x, D(2)), Minus, x, Plus, D(1))));
        var denominator = Seq(
            new Formula.Power(Parenthesized(Seq(x, Minus, D(1))), D(2)),
            Parenthesized(Seq(x, Plus, D(1))),
            new Formula.Power(Parenthesized(Seq(D(2), x, Minus, D(1))), D(2)));
        var recurrence = Seq(D(5), Previous(1), Minus, D(7), Previous(2),
            Minus, Previous(3), Plus, D(8), Previous(4), Minus, D(4), Previous(5));
        var body = new Formula.Aligned([
            Seq(Amp, Parenthesized(And(Call("Finite", set), Equal(Count(n), Call("ncard", set))))),
            Seq(Amp, Land, Sp, Equal(Count(D(0)), D(0))),
            Seq(Amp, Land, Sp, Equal(series, new Formula.Fraction(numerator, denominator))),
            Seq(Amp, Land, Sp, Parenthesized(Seq(
                Equal(Count(D(1)), D(0)), Land, Sp, Equal(Count(D(2)), D(0)), Land, Sp,
                Equal(Count(D(3)), D(0)), Land, Sp, Equal(Count(D(4)), D(0)), Land, Sp,
                Equal(Count(D(5)), D(1)), Land, Sp, Equal(Count(D(6)), D(4)), Land, Sp,
                Equal(Count(D(7)), D(1, 4))))),
            Seq(Amp, Land, Sp, Parenthesized(new Formula.Logic(
                new Formula.Relation(D(7), FormulaRelationOperator.LessThan, n),
                FormulaLogicOperator.Implies, Equal(IntegerCount(n), recurrence))))
        ]);
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"),
            Seq(Mathbb, Grp(F.Id("N"))), Parenthesized(body)));
    }

    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Count(Formula index) => Call("a", index);
    private static Formula IntegerCount(Formula index) => Parenthesized(Seq(Count(index),
        Sp, Colon, Sp, new Formula.Integers()));
    private static Formula Previous(byte offset) => IntegerCount(Seq(F.Id("n"), Minus, D(offset)));
}
