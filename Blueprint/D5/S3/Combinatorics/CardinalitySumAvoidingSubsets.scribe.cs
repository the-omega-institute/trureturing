using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class CardinalitySumAvoidingSubsetsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CardinalitySumAvoidingSubsets.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/wu2023a367400");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original subset count has the conjectured generating function.",
        H("Cardinality-Sum-Avoiding Subsets"),
        Blocks(
            Paragraph(Text("For every natural n, the interval [1,n] is empty at n=0. "
                + "A subset S is admissible when no distinct x,y in S satisfy x+y=|S|. "
                + "The test does not prohibit an element x with 2x=|S|. All counts are "
                + "natural numbers. X is the formal indeterminate; the generating-function "
                + "identity lies in Q[[X]], with natural counts cast to Q. No analytic "
                + "convergence or recurrence-defined substitute is assumed.")),
            Node("admissibleFamily", "The original admissible family", FamilyFormula(),
                "The finite family is the powerset of the natural interval [1,n], "
                + "filtered by the displayed predicate. This is exactly the OEIS NAME "
                + "convention, including the empty subset and permission for equal summands.",
                DescribeRole.Definition),
            Node("a", "The original sequence", Disp(Equal(Call("a", F.Id("n")),
                Call("card", Call("admissibleFamily", F.Id("n"))))),
                "The sequence is the cardinality of that actual finite family. Its zero "
                + "coefficient is one because the empty subset is its sole member at n=0.",
                DescribeRole.Definition),
            Node("result", "The formal generating-function identity", ResultFormula(),
                "For each positive cardinality k, the proof constructs an invertible "
                + "encoding by disjoint pairs {i,k-i}, an optional even midpoint, and "
                + "the unrestricted tail [k,n]. It derives the count polynomial, uses "
                + "Mathlib's binomial-series and homogenization identities, and sums "
                + "the two parity families coefficientwise. Every coefficient involves "
                + "only finitely many cardinalities. The empty subset is handled "
                + "separately. All helper proofs and equivalences are local to result.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a367400-cardinality-sum-avoiding-subsets"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a367400-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            (role == DescribeRole.Theorem ? AssessedProvenance.FromRepo(Source)
                : AssessedProvenance.FromLiterature(Source)), Blocks(Paragraph(Text(prose))), role, claim);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula Equal(Formula l, Formula r) => Seq(l, Sp, Eq, Sp, r);
    private static Formula Add(Formula l, Formula r) =>
        new Formula.Binary(l, FormulaBinaryOperator.Add, r);
    private static Formula Sub(Formula l, Formula r) =>
        new Formula.Binary(l, FormulaBinaryOperator.Subtract, r);
    private static Formula Mul(Formula l, Formula r) =>
        new Formula.Binary(l, FormulaBinaryOperator.Multiply, r);
    private static Formula Pow(Formula x, Formula n) => new Formula.Power(x, n);
    private static Formula FamilyFormula()
    {
        Formula n = F.Id("n"), s = F.Id("S"), x = F.Id("x"), y = F.Id("y");
        return Disp(Equal(Call("admissibleFamily", n), Seq(OpenBrace, s, Sp, Subseteq, Sp,
            Call("Icc", D(1), n), Sp, Mid, Sp, Forall, Sp, x, Comma, y, Sp, InMacro, Sp, s,
            Comma, Sp, Open, x, Sp, Neq, Sp, y, Close, Sp, Implies, Sp,
            Open, Add(x,y), Sp, Neq, Sp, Call("card", s), Close, CloseBrace)));
    }
    private static Formula ResultFormula()
    {
        Formula x = F.Id("X"), n = F.Id("n");
        Formula d = Add(Sub(Add(Sub(D(1), Mul(D(2), x)), Pow(x,D(2))),
            Mul(D(2),Pow(x,D(3)))), Pow(x,D(4)));
        Formula a = Seq(Sum, Underscore, Grp(Equal(n,D(0))), Caret, Grp(Infty), Sp,
            Call("a", n), Sp, Pow(x,n));
        return Disp(Equal(Mul(Seq(Open,d,Close),a), Sub(Add(D(1),Pow(x,D(2))),Pow(x,D(3)))));
    }
}
