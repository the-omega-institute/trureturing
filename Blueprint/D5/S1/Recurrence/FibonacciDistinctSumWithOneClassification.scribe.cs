using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class FibonacciDistinctSumWithOneClassificationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/FibonacciDistinctSumWithOneClassification.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fibonacci sets containing one have Fibonacci sum exactly in alternating form.",
        H("Distinct Fibonacci Sums Containing One"),
        Blocks(
            Paragraph(Text("Write F(n) for the Fibonacci sequence with F(0)=0, F(1)=1, and F(n+2)=F(n)+F(n+1). All indices and values are natural numbers.")),
            Describe.Lean(
                DescribeId.Create("positive-fibonacci-values"),
                DeclarationHandle.Create(Prefix + "PositiveFibonacci"),
                H("Positive Fibonacci values"),
                StatementSource.FromAuthor(Disp(ForAll([Bound("x", Naturals())],
                    Iff(Call("PositiveFibonacci", F.Id("x")),
                        Exists([Bound("n", Naturals())], And(LessOrEqual(D(2), F.Id("n")),
                            Equal(Call("F", F.Id("n")), F.Id("x")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The positive values are 1, 2, 3, 5, 8, and so on. Starting the indices at two counts the value one only once."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("alternating-fibonacci-initial-set"),
                DeclarationHandle.Create(Prefix + "alternatingSet"),
                H("Alternating initial sets"),
                StatementSource.FromAuthor(Disp(ForAll([Bound("r", Naturals())],
                    Equal(Call("A", F.Id("r")), Seq(
                        OpenBrace, D(1), CloseBrace, Sp, Cup, Sp,
                        OpenBrace, Call("F", Add(Multiply(D(2), F.Id("j")), D(1))),
                        Sp, Mid, Sp, D(1), Sp, Le, Sp, F.Id("j"), Sp, Lt, Sp, F.Id("r"), CloseBrace))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A(r) consists of one and the Fibonacci values F(2j+1) for 1 <= j < r. In particular, A(1) is the singleton containing one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fibonacci-sum-with-one-classification"),
                DeclarationHandle.Create(Prefix + "classification"),
                H("Classification and unique parameter"),
                StatementSource.FromAuthor(ClassificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let S be any finite set of positive Fibonacci values containing one. Its sum is a positive Fibonacci value if and only if S=A(r) for some r at least one. For every such r, the sum is F(2r), and any t at least one with S=A(t) equals r. No assumption excludes adjacent Fibonacci indices.")),
                    Paragraph(Text(
                    "If the sum is F(n) and n exceeds two, every member is strictly smaller than F(n). The sum of the Fibonacci values from index two through n-2 is F(n)-2, so F(n-1) must occur. Index three is impossible. At index at least four, deleting F(n-1) preserves one and leaves sum F(n-2). Strong induction therefore forces exactly the alternating initial set. Conversely the recurrence sums A(r) to F(2r); strict increase from index two gives uniqueness."))),
                DescribeRole.Theorem))));

    private static Formula ClassificationFormula()
    {
        Formula s = F.Id("S"), r = F.Id("r"), t = F.Id("t"), x = F.Id("x");
        Formula total = Seq(F.Sum, Underscore, Grp(x, Sp, InMacro, Sp, s), Sp, x);
        Formula shape = And(LessOrEqual(D(1), r), Equal(s, Call("A", r)));
        Formula premises = And(
            ForAll([Bound("x", Naturals())], Implies(Member(x, s), Call("PositiveFibonacci", x))),
            Member(D(1), s));
        Formula uniqueness = ForAll([Bound("t", Naturals())], Implies(
            And(LessOrEqual(D(1), t), Equal(s, Call("A", t))), Equal(t, r)));
        return Disp(ForAll([Bound("S", Call("Finset", Naturals()))], Implies(premises,
            And(Iff(Call("PositiveFibonacci", total), Exists([Bound("r", Naturals())], shape)),
                ForAll([Bound("r", Naturals())], Implies(shape,
                    And(Equal(total, Call("F", Multiply(D(2), r))), uniqueness)))))));
    }
    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
