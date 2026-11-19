using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class MatharA119967RefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/MatharA119967Refutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/mathar2011a119967");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal signed recurrence printed for OEIS A119967 has positive residual at every index at least four.",
        H("The printed A119967 recurrence fails at every valid index"),
        Blocks(
            Node("a", "The source finite sum", AFormula(),
                "Paul Barry's sequence is a(n)=sum C(n,2k)C(k,floor(k/2)), with k from zero through floor(n/2), inclusive. "
                    + "The indices, binomial coefficients and sum are natural numbers. Nat.div is floor division and Finset.range(m) contains zero through m-1. "
                    + "In particular this uses C(n,2k), rather than C(n-k,k).", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("residual", "The unchanged signed expression", ResidualFormula(),
                "The polynomial coefficients are evaluated in the integers. Each natural sequence value is cast to the integers before multiplication. "
                    + "The sequence lags use natural subtraction; for n at least four they are the usual nonnegative indices. "
                    + "All five signs and coefficients are exactly those printed by R. J. Mathar in OEIS A119967.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The two onset readings", ClaimFormula(),
                "The source prints no recurrence onset. Its offset 0,3 is sequence metadata. "
                    + "The first reading asks for zero residual at every n at least four, the least index with all four lags nonnegative. "
                    + "The second allows any natural cutoff N at least four and asks for zero residual at every n at least N. "
                    + "The disjunction records both interpretations without changing the printed expression.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node("residual_pos", "Strict positivity at every valid index",
                Disp(All("n", Naturals(), Implies(AtMost(D(4), F.Id("n")),
                    Less(D(0), Call("residual", F.Id("n")))))),
                "Every summand is nonnegative and the k=0 summand is one, so a(n) is positive. "
                    + "Monotonicity of C(n,2k) in n and inclusion of the summation ranges show that a is nondecreasing. "
                    + "Write A=(n+2)(n-3) and D=(n-2)(n-3). For n at least four both are nonnegative. "
                    + "The first two terms of the residual equal A(a(n)-a(n-1))+(n-4)a(n-1), hence are nonnegative. "
                    + "The remaining terms equal D(a(n-2)-a(n-3))+D(a(n-2)-a(n-4))+(n-2)(n+1)a(n-2). "
                    + "Their last summand is strictly positive and the other two are nonnegative. Thus the entire residual is positive.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "Neither onset reading holds", Disp(new Formula.Not(F.Id("claim"))),
                "At n=4 the source sum gives a(0),...,a(4)=1,1,2,4,9. The five coefficients are 6,-6,14,-2,-2, "
                    + "so the residual is 54. This already contradicts the first reading. "
                    + "For any proposed later cutoff N, positivity at N contradicts zero residual there, excluding the second reading as well. "
                    + "This concerns the printed expression only; no corrected recurrence, generating-function identity or priority assertion is inferred.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("mathar-2011-a119967-recurrence"), ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("mathar-a119967-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula Cast(Formula x) => P(Seq(x, Sp, Colon, Sp, Integers()));
    private static Formula All(string x, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), t, b);
    private static Formula Exists(string x, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), t, b);
    private static Formula Implies(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, P(y));
    private static Formula AtMost(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Less(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Choose(Formula n, Formula k) => Call("choose", n, k);
    private static Formula Half(Formula n) => Call("floor", new Formula.Fraction(n, D(2)));

    private static Formula AFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        var range = Call("range", Add(Half(n), D(1)));
        var sum = Seq(new Formula.Subscript(F.Sum, Seq(k, Sp, InMacro, Sp, range)), Sp,
            Multiply(Choose(n, Multiply(D(2), k)), Choose(k, Half(k))));
        return Disp(All("n", Naturals(), Equal(Call("a", n), sum)));
    }

    private static Formula ResidualFormula()
    {
        Formula n = F.Id("n"), z = Cast(n);
        Formula Term(int lag) => Cast(Call("a", lag == 0 ? n : Subtract(n, D((byte)lag))));
        var first = Multiply(Multiply(P(Add(z, D(2))), P(Subtract(z, D(3)))), Term(0));
        var second = Multiply(P(Subtract(Add(D(2), Multiply(D(2), z)), new Formula.Power(z, D(2)))), Term(1));
        var third = Multiply(Multiply(P(Subtract(Multiply(D(3), z), D(5))), P(Subtract(z, D(2)))), Term(2));
        var coeff = Multiply(P(Subtract(z, D(2))), P(Subtract(z, D(3))));
        var expression = Subtract(Subtract(Add(Add(first, second), third), Multiply(coeff, Term(3))), Multiply(coeff, Term(4)));
        return Disp(All("n", Naturals(), Equal(Call("residual", n), expression)));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), cutoff = F.Id("N");
        var literal = All("n", Naturals(), Implies(AtMost(D(4), n), Equal(Call("residual", n), D(0))));
        var eventual = Exists("N", Naturals(), new Formula.Logic(AtMost(D(4), cutoff), FormulaLogicOperator.And,
            All("n", Naturals(), Implies(AtMost(cutoff, n), Equal(Call("residual", n), D(0))))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            P(new Formula.Logic(P(literal), FormulaLogicOperator.Or, P(eventual)))));
    }
}
