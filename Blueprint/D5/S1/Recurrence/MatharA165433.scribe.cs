using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class MatharA165433Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/MatharA165433.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/mathar2011a165433");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal rational factorial sum defining OEIS A165433 satisfies Mathar's recurrence at every natural index at least three.",
        H("Mathar's recurrence for OEIS A165433"),
        Blocks(
            Node("a", "The inclusive rational sum", AFormula(),
                "The OEIS FORMULA field gives a(n) = Sum_{k=0..floor(n/2)} C(n-k,k)*(2k)!/(k!*2^k). "
                + "Both n and k are natural numbers. Nat.div(n,2) is floor(n/2), and Finset.range(n/2+1) "
                + "includes every k from zero through floor(n/2). The binomial coefficient and factorials "
                + "are computed in the naturals and cast to the rationals before division. The power of two, "
                + "products, quotient, and sum are rational. Every index subtraction is natural subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The complete recurrence", Disp(Iff(F.Id("claim"), RecurrenceFormula())),
                "The source attributes the conjecture 2*a(n)-3*a(n-1)+(3-2*n)*a(n-2)+(2*n-3)*a(n-3)=0 "
                + "to R. J. Mathar. The source specifies no onset; n>=3 is the interpretation using only "
                + "nonnegative predecessor indices. The quantifier includes every such natural n without an upper bound. "
                + "Coefficients use the rational cast of n, and recurrence arithmetic is rational. "
                + "No analytic premise, eventual qualification, or recurrence-defined replacement sequence is assumed.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The literal sum satisfies the recurrence", Disp(RecurrenceFormula()),
                "Put t(n,k)=C(n-k,k), b(k)=(2k)!/(k!*2^k), "
                + "T(c,n)=Sum_{k=0..n} t(n,k)c(k), and W(c,n)=T(k -> k*c(k),n), all evaluated in the rationals. "
                + "The binomial coefficient is zero when n<2*k. Pascal's identity gives "
                + "T(c,n+2)=T(c,n+1)+T(k -> c(k+1),n). The binomial multiplicative identity gives "
                + "(n+1)*(T(c,n+1)-T(c,n))=2*W(c,n+1)-W(c,n). "
                + "Expanding the three factorial successors and cancelling the nonzero denominator gives "
                + "b(k+1)=(2*k+1)*b(k), hence T(k -> b(k+1),n)=2*W(b,n)+T(b,n). "
                + "Apply the Pascal relation at n and n+1 and eliminate the shifted transforms and weighted sums "
                + "using these identities. This yields the stated recurrence at index n+3. "
                + "All terms with k>floor(n/2) vanish, so T(b,n) equals the entire defining inclusive sum a(n). "
                + "Writing any index at least three as n+3 completes the result. "
                + "No assertion of integrality or of a double-factorial replacement is needed.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mathar-2011-a165433-recurrence"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("mathar-a165433-" + name), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula QCast(Formula f) => Par(Seq(f, Sp, Colon, Sp, Rationals()));
    private static Formula All(string v, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Iff(Formula l, Formula r) =>
        new Formula.Logic(l, FormulaLogicOperator.Iff, Par(r));
    private static Formula Implies(Formula l, Formula r) =>
        new Formula.Logic(l, FormulaLogicOperator.Implies, Par(r));
    private static Formula AtMost(Formula l, Formula r) =>
        new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);

    private static Formula AFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        var range = Apply(Qualified("Finset", "range"),
            Add(Apply(Qualified("Nat", "div"), n, D(2)), D(1)));
        var choose = QCast(Apply(Qualified("Nat", "choose"), Subtract(n, k), k));
        var numerator = Multiply(choose, QCast(Apply(Qualified("Nat", "factorial"), Multiply(D(2), k))));
        var denominator = Multiply(QCast(Apply(Qualified("Nat", "factorial"), k)), new Formula.Power(QCast(D(2)), k));
        var summand = new Formula.Fraction(numerator, denominator);
        var sum = Seq(new Formula.Subscript(F.Sum, Seq(k, Sp, InMacro, Sp, range)), Sp, summand);
        return Disp(All("n", Naturals(), Equal(Seq(Call("a", n), Sp, Colon, Sp, Rationals()), sum)));
    }

    private static Formula RecurrenceFormula()
    {
        Formula n = F.Id("n"), q = QCast(n);
        var t0 = Multiply(D(2), Call("a", n));
        var t1 = Multiply(D(3), Call("a", Subtract(n, D(1))));
        var t2 = Multiply(Par(Subtract(D(3), Multiply(D(2), q))), Call("a", Subtract(n, D(2))));
        var t3 = Multiply(Par(Subtract(Multiply(D(2), q), D(3))), Call("a", Subtract(n, D(3))));
        return All("n", Naturals(), Implies(AtMost(D(3), n),
            Equal(Add(Add(Subtract(t0, t1), t2), t3), D(0))));
    }
}
