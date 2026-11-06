using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class MatharA084261Document : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/MatharA084261.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/mathar2012a084261");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal even-index binomial-factorial sum satisfies Mathar's recurrence at every natural index at least three.",
        H("Mathar's recurrence for OEIS A084261"),
        Blocks(
            Node("a", "The literal inclusive sum", AFormula(),
                "OEIS A084261 defines a(n) as Sum_{k=0..floor(n/2)} C(n,2*k)*k!. "
                    + "The index n, binomial coefficient, factorial, and sum are natural numbers. "
                    + "Nat.div(n,2) is floor(n/2). Finset.range(n/2+1) contains every natural k from zero through floor(n/2), including both endpoints.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The complete conjectured recurrence", ClaimFormula(),
                "The source FORMULA field attributes 2*a(n)-4*a(n-1)+(-n+2)*a(n-2)+(n-2)*a(n-3)=0 to R. J. Mathar. "
                    + "The source supplies no recurrence onset: n>=3 is the disclosed interpretation with all indices nonnegative. "
                    + "Indices use natural subtraction; each sequence value and n is cast to the integers "
                    + "before signed coefficient products and sums are evaluated. No additional hypothesis is used.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The full recurrence holds", Disp(RecurrenceFormula()),
                "Write b(k)=(k/2)! for even k and zero for odd k, and T(c,n)=Sum_{k=0..n} C(n,k)c(k), in the integers. "
                    + "Pascal's identity supplies the shifted-transform relation. Parity and factorial succession give "
                    + "2*b(k+3)+2*b(k+2)-3*b(k+1)-2*b(k)=k*b(k+1)+k*b(k). "
                    + "The weighted binomial identity, with its vanishing boundary terms and justified subtraction cast, "
                    + "then eliminates the shifted transforms. A nonzero-summand bijection k -> k/2 identifies T(b,n) "
                    + "with the literal finite sum, including odd-term vanishing and both endpoints. Substituting n=m+3 covers every n>=3. "
                    + "The proof is bind-only after inlining normalization and upstream identities; the intended admission basis is "
                    + "open-problem-resolution under issue #27208, with utility none. No escape witness or worldwide novelty is claimed. "
                    + "The domain is inhabited (n=3); a(0)=1 and a(2)=2 distinguish actual observations, and the constant-one "
                    + "sequence fails the same law at n=3. The typed Reg mirror attempts source reconstruction, variation and sensitivity. "
                    + "The audit remains declared_unresolved with IE-C050 ClosedTruthReadout, unclassified_form, source.roles; "
                    + "issue #27208 discloses the missing classified source-role binding and certificate. "
                    + "The resolution claim concerns the frozen mathematical result and does not assert declared_validated.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mathar-2012-a084261-recurrence"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("mathar-a084261-" + name),
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
        var summand = Multiply(Choose(n, Multiply(D(2), k)), Apply(Qualified("Nat", "factorial"), k));
        var sum = Seq(new Formula.Subscript(F.Sum, Seq(k, Sp, InMacro, Sp, range)), Sp, summand);
        return Disp(All("n", Naturals(), Equal(Seq(Call("a", n), Sp, Colon, Sp, Naturals()), sum)));
    }

    private static Formula ClaimFormula() => Disp(Iff(F.Id("claim"), RecurrenceFormula()));

    private static Formula RecurrenceFormula()
    {
        Formula n = F.Id("n"), z = IntCast(n);
        var t0 = Multiply(D(2), IntCast(Call("a", n)));
        var t1 = Multiply(D(4), IntCast(Call("a", Subtract(n, D(1)))));
        var t2 = Multiply(Parenthesized(Subtract(D(2), z)), IntCast(Call("a", Subtract(n, D(2)))));
        var t3 = Multiply(Parenthesized(Subtract(z, D(2))), IntCast(Call("a", Subtract(n, D(3)))));
        var sum = Add(Add(Subtract(t0, t1), t2), t3);
        return All("n", Naturals(), Implies(AtMost(D(3), n), Equal(sum, D(0))));
    }
}
