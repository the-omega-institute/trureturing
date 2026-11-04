using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class WuAdjacentFibonacciResiduesDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/WuAdjacentFibonacciResidues.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/wu2026a221018");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An index whose Fibonacci number is divisible by itself and both neighbours ends in zero, two or eight.",
        H("Wu's Adjacent-Index Fibonacci Divisibility Conjecture"),
        Blocks(
            Node("claim", "The A221018 assertion",
                Disp(Equal(F.Id("claim"), Parenthesized(ClaimBody()))),
                "OEIS A221018, revision 35, NAME: “Number k such that Fibonacci(k) is divisible by k, k + 1 and k - 1.” "
                + "The first FORMULA line reads: “a(n) % 10 == 0, 2, or 8 (conjectured). - _Chai Wah Wu_, Aug 06 2026”. "
                + "The web entry has no page number. The generator starts at two, so k ranges over natural numbers "
                + "at least two. Nat.fib has F(0)=0, F(1)=1 and F(n+2)=F(n)+F(n+1). The three divisibilities "
                + "are separate implication hypotheses. Subtraction is natural subtraction, which agrees with integer "
                + "subtraction here; % denotes natural-number remainder. No converse is asserted.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The final-digit theorem", Disp(ClaimBody()),
                "One of k and k+1 is even, so their divisibility into Nat.fib(k) makes that Fibonacci number even. "
                + "The equivalence between Fibonacci divisibility and index divisibility, applied at indices three "
                + "and four, forces 3 and 4 to divide k, hence 12 divides k. If k has remainder one or four modulo "
                + "five, one neighbour is divisible by five. The same equivalence at index five then forces five "
                + "to divide k, a contradiction. Evenness and these two exclusions leave final digits zero, two and eight.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("wu221018-fibdiv"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("wu221018-" + name), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula ClaimBody()
    {
        var k = F.Id("k");
        var fib = new Formula.Apply(Qualified("Nat", "fib"), [k]);
        var remainder = new Formula.Modulo(k, D(1, 0));
        var conclusion = Or(Equal(remainder, D(0)),
            Or(Equal(remainder, D(2)), Equal(remainder, D(8))));
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("k"),
            Seq(Mathbb, Grp(F.Id("N"))),
            Imply(new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, k),
                Imply(Divides(new Formula.Binary(k, FormulaBinaryOperator.Subtract, D(1)), fib),
                    Imply(Divides(k, fib),
                        Imply(Divides(new Formula.Binary(k, FormulaBinaryOperator.Add, D(1)), fib),
                            conclusion)))));
    }

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
    private static Formula Imply(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
}
