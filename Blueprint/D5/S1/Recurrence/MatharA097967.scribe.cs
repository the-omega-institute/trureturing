using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class MatharA097967Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/MatharA097967.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/mathar2013a097967");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal factorial sum in A097967 satisfies Mathar's recurrence at every natural index at least five.",
        H("Mathar's recurrence for the literal A097967 factorial sum"),
        Blocks(
            Paragraph(Text("N denotes the natural numbers and Q the rational numbers. All indices, factorials, "
                + "descending factorials and index subtractions are natural-number operations. "
                + "A displayed cast to Q occurs before division or signed scalar arithmetic. "
                + "Finset.Icc(1,n) includes both endpoints and is empty at n=0; Finset.range(n) contains 0 through n-1.")),
            Node("literal", "The source factorial sum", LiteralFormula(),
                "The literal FORMULA in the cited OEIS entry is n!(k!+1)/(k!(n-k)!), summed over 1<=k<=n. "
                + "The NAME describes the same sum as the sum of permutations P(n,k) and binomial coefficients C(n,k). "
                + "This definition fixes the sequence independently of any recurrence.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("b", "The descending-factorial component", BFormula(),
                "Nat.descFactorial(n,j) is the natural descending factorial n(n-1)...(n-j+1). "
                + "Splitting each literal summand gives this component plus the binomial sum. "
                + "The proof establishes literal(n)=b(n)+2^n-1 and b(n+1)=(n+1)(b(n)+1) internally, "
                + "using the pinned factorial and binomial identities.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The complete recurrence claim", Disp(new Formula.Logic(F.Id("claim"),
                FormulaLogicOperator.Iff, Par(RecurrenceFormula()))),
                "The cited FORMULA field attributes the six-term recurrence to Mathar. It supplies no onset. "
                + "The condition n>=5 is the registered interpretation with nonnegative indices, not an author quotation. "
                + "There is no upper bound, integrality assumption, negative-index extension, or eventual-only restriction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The literal sum satisfies the recurrence", Disp(RecurrenceFormula()),
                "The proof splits the literal sum into b(n)+2^n-1 by the binomial row sum. "
                + "Five substitutions of b(n+1)=(n+1)(b(n)+1), followed by rational polynomial normalization, "
                + "give the recurrence at n=m+5. Every n>=5 has this form. "
                + "The source's printed identity A007526(n)-A000225(n)-1 is not used or certified: "
                + "at n=1 it gives -1, whereas the literal sum is 2. "
                + "No other named conjecture or asymptotic formula is asserted.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mathar-2013-a097967-literal-recurrence"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("mathar-a097967-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Q() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Cast(Formula x) => Par(Seq(x, Sp, Colon, Sp, Q()));
    private static Formula Named(string x) => Seq(Operatorname, Grp(F.Id(x)));
    private static Formula Apply(string x, params Formula[] args) => new Formula.Apply(Named(x), [.. args]);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula SumOver(Formula k, Formula range, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(k, Sp, InMacro, Sp, range)), Sp, body);
    private static Formula Fac(Formula x) => Apply("Nat.factorial", x);
    private static Formula LiteralFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        var numerator = Multiply(Cast(Fac(n)), Par(Add(Cast(Fac(k)), D(1))));
        var denominator = Multiply(Cast(Fac(k)), Cast(Fac(Subtract(n, k))));
        return Disp(All("n", N(), Equal(Apply("literal", n),
            SumOver(k, Apply("Finset.Icc", D(1), n), new Formula.Fraction(numerator, denominator)))));
    }
    private static Formula BFormula()
    {
        Formula n = F.Id("n"), k = F.Id("k");
        return Disp(All("n", N(), Equal(Apply("b", n), SumOver(k, Apply("Finset.range", n),
            Cast(Apply("Nat.descFactorial", n, Add(k, D(1))))))));
    }
    private static Formula RecurrenceFormula()
    {
        Formula n = F.Id("n"), z = Cast(n);
        Formula A(int j) => Apply("literal", j == 0 ? n : Subtract(n, D(j)));
        var t1 = Multiply(Par(Subtract(Subtract(D(0), z), D(6))), A(1));
        var t2 = Multiply(Par(Add(Multiply(D(6), z), D(7))), A(2));
        var t3 = Multiply(Par(Add(Multiply(Seq(Minus, D(13)), z), D(14))), A(3));
        var t4 = Multiply(Multiply(D(4), Par(Subtract(Multiply(D(3), z), D(8)))), A(4));
        var t5 = Multiply(Multiply(D(4), Par(Add(Subtract(D(0), z), D(4)))), A(5));
        var sum = Add(Add(Add(Add(Add(A(0), t1), t2), t3), t4), t5);
        return All("n", N(), new Formula.Logic(
            new Formula.Relation(D(5), FormulaRelationOperator.LessThanOrEqual, n),
            FormulaLogicOperator.Implies, Par(Equal(sum, D(0)))));
    }
}
