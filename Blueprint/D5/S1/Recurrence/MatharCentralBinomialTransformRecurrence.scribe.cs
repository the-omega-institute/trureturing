using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class MatharCentralBinomialTransformRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/MatharCentralBinomialTransformRecurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/mathar2012a113409");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The binomial sum defining OEIS A113409 satisfies Mathar's five-term recurrence at every index at least four.",
        H("Mathar's recurrence for the central-binomial transform"),
        Blocks(
            Node("a", "The literal binomial sum", AFormula(),
                "OEIS A113409, FORMULA field: \"a(n) = Sum_{k=0..floor(n/2)} C(n-k, k)*C(k, floor(k/2)).\" "
                    + "Both indices are natural numbers. Nat.choose is the ordinary binomial coefficient, "
                    + "Nat.div(n,2) is floor(n/2), and Finset.range(m) contains 0 through m - 1; "
                    + "the upper endpoint floor(n/2) is therefore included. Subtraction in this definition is natural subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Mathar's conjecture", ClaimFormula(),
                "OEIS A113409, FORMULA field: \"Conjecture: (n+2)*a(n)-2*(n+1)*a(n-1) +(n-4)*a(n-2) +2*a(n-3) +4*(2-n)*a(n-4)=0. - _R. J. Mathar_, Nov 07 2012\" "
                    + "The entry is an online sequence record without page numbers. The encoding quantifies every natural n with 4 <= n. "
                    + "All five indices use natural subtraction, while n and each value a(n-j) are explicitly cast to the integers "
                    + "before the coefficient products and additions are evaluated.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The recurrence holds", Disp(RecurrenceFormula()),
                "Pascal's identity relates consecutive rows of the kernel Nat.choose(n-k,k). "
                    + "A weighted form of the same kernel identity controls the sum with an additional factor k. "
                    + "Splitting Nat.choose(k,floor(k/2)) by the parity of k gives its two-step recurrence "
                    + "from the central-binomial recurrence. Applying the kernel to this relation and eliminating "
                    + "the shifted weighted sums yields the five-term recurrence by induction. "
                    + "Terms beyond floor(n/2) vanish, identifying the extended sum used in the proof with the defining sum a(n). "
                    + "No generating-function equation or asymptotic statement is asserted here.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mathar-2012-a113409-recurrence"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("mathar-central-binomial-" + name),
        DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula IntCast(Formula value) => Parenthesized(Seq(value, Sp, Colon, Sp, Integers()));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula NatDiv(Formula value) => Apply(Qualified("Nat", "div"), value, D(2));
    private static Formula Choose(Formula upper, Formula lower) => Apply(Qualified("Nat", "choose"), upper, lower);

    private static Formula AFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        var range = Apply(Qualified("Finset", "range"), Add(NatDiv(n), D(1)));
        var summand = Multiply(Choose(Subtract(n, k), k), Choose(k, NatDiv(k)));
        var sum = Seq(new Formula.Subscript(F.Sum, Seq(k, Sp, InMacro, Sp, range)), Sp, summand);
        return Disp(All("n", Naturals(), Equal(Call("a", n), sum)));
    }

    private static Formula ClaimFormula() => Disp(Iff(F.Id("claim"), RecurrenceFormula()));

    private static Formula RecurrenceFormula()
    {
        Formula n = F.Id("n"), z = IntCast(n);
        var t0 = Multiply(Parenthesized(Add(z, D(2))), IntCast(Call("a", n)));
        var t1 = Multiply(Multiply(D(2), Parenthesized(Add(z, D(1)))),
            IntCast(Call("a", Subtract(n, D(1)))));
        var t2 = Multiply(Parenthesized(Subtract(z, D(4))), IntCast(Call("a", Subtract(n, D(2)))));
        var t3 = Multiply(D(2), IntCast(Call("a", Subtract(n, D(3)))));
        var t4 = Multiply(Multiply(D(4), Parenthesized(Subtract(D(2), z))),
            IntCast(Call("a", Subtract(n, D(4)))));
        var sum = Add(Add(Add(Subtract(t0, t1), t2), t3), t4);
        return All("n", Naturals(), Implies(AtMost(D(4), n), Equal(sum, D(0))));
    }
}
