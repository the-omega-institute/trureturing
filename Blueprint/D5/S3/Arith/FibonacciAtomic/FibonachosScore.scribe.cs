using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FibonachosScoreDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/kagey2025a382814");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fibonachos ties and large-heap majority follow Fibonacci blocks.",
        H("Fibonachos score"),
        Blocks(
            Paragraph(Text("Let fib be the Fibonacci sequence with fib(0)=0 and fib(1)=1. "
                + "Starting from n objects and index one, two players alternate taking fib(i) "
                + "objects and increasing i by one. When fib(i) exceeds the remaining heap, "
                + "i resets to one before the move. The game ends at the empty heap. "
                + "The recursive pair play(n,i) gives the scores of the player to move and "
                + "the other player: a move of size q returns (q+second,first) from the "
                + "smaller heap. This is the same update as the OEIS program, with the "
                + "player flag expressed by swapping the pair. Let a(n)=play(n,1).first "
                + "and D(n)=2a(n)-n. The first ten a-values are 1,1,2,3,3,4,3,4,4,5.")),
            Describe.Lean(
                DescribeId.Create("fibonachos-score-result"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/FibonachosScore.result"),
                H("Ties and first-player majority"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The first uninterrupted segment in the block "
                    + "fib(m)-1 <= n <= fib(m+1)-2 consumes fib(m)-1 objects. "
                    + "With r=n-(fib(m)-1), its alternating score gives "
                    + "D(n)=1+(-1)^m(D(r)-fib(m-3)). The uniform estimate "
                    + "|D(u)-1| <= fib(t-3), for t>=4 and 0<=u<fib(t), follows by "
                    + "induction over these blocks. For n>32 it makes D(n) positive "
                    + "exactly in odd blocks and excludes ties. The smaller positive "
                    + "heaps have ties precisely at 2,8,10,32. The displayed inequalities "
                    + "fib(m)<=n+1 and n+2<=fib(m+1) express the original interval "
                    + "without natural-number subtraction; for n>32 the upper endpoint "
                    + "forces fib(m+1)>=2, so the two forms are equivalent. The "
                    + "comparison uses 2a(n) to avoid rounding n/2."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a382814-fibonachos-score"),
                    ResolutionKind.Proved)))));

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n"), m = F.Id("m");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula twice = Seq(D(2), Call("a", n));
        Formula ties = new Formula.Relation(n, FormulaRelationOperator.MemberOf,
            new Formula.SetLiteral([D(2), D(8), D(1,0), D(3,2)]));
        Formula interval = new Formula.Bind(FormulaQuantifier.Exists,
            FormulaIdentifier.Create("m"), nat,
            And(Call("Odd", m), And(Le(Call("fib", m), Add(n, D(1))),
                Le(Add(n, D(2)), Call("fib", Add(m, D(1)))))));
        return Disp(And(All(nat, Le(D(1), n), Iff(Eq(twice, n), ties)),
            All(nat, Lt(D(3,2), n), Iff(Lt(n, twice), interval))));
    }

    private static Formula All(Formula type, Formula premise, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), type,
            new Formula.Logic(premise, FormulaLogicOperator.Implies, body));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Add(Formula x, Formula y) => Seq(x, Plus, y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
}
