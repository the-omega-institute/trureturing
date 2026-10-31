using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class HannaA369673Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/HannaA369673.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/hanna2024a369673");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna A369673 square classification and five-adic orders.",
        H("Hanna's A369673 conjectures"), Blocks(
            Node("a", All("N", Naturals(), Eq(Call("a", V("N")),
                Product(Add(V("N"), D(1)), Add(
                    Pow(Cast(D(2), Naturals()), V("k")),
                    Pow(D(2), Sub(V("N"), V("k"))))))),
                "OEIS A369673, NAME (unpaginated): \"a(n) = Product_{k=0..n} (2^k + 2^(n-k)).\" The natural index N includes zero. Finset.range (N + 1) includes exactly k = 0 through k = N; subtraction in the exponent is natural subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("b", All("n", Naturals(), Eq(Call("b", V("n")),
                Sub(Cast(Valuation(Factorial(Mul(D(1, 0), V("n")))), Integers()),
                    Cast(Valuation(Factorial(Mul(D(5), V("n")))), Integers())))),
                "OEIS A127428, NAME (unpaginated): \"v_5( (10n)! ) - v_5( (5n)! ), where v_p(N) is the p-adic valuation defined in A112765.\" The difference is in the integers, and factorials are natural factorials. OEIS A112765, NAME (unpaginated): \"Exponent of highest power of 5 dividing n. Or, 5-adic valuation of n.\" All valuation arguments here are positive.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", Eq(Call("claim"), Parenthesized(ClaimBody())),
                "OEIS A369673, COMMENTS (unpaginated): \"Conjectures:\" \"(C.1) a(n) is a square iff n is not divisible by 4.\" \"(C.2) a(2*n+1) is not divisible by 5 for n >= 0.\" \"(C.3) exponent of highest power of 5 dividing a(4*n) = 2*A127428(n).\" \"(C.4) exponent of highest power of 5 dividing a(4*n+2) = 2*A127428(n+1).\" The four natural quantifiers include zero. IsSquare uses a natural square root; padicValNat values are cast to integers in the last two clauses, and b denotes A127428.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", ClaimBody(),
                "All four assertions hold at every natural index. Removing the equal boundary factors gives a two-step product recurrence. At even indices its power of two determines squareness. Lifting the exponent at five and splitting factorials identify the exact five-adic orders with b.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source), new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("h369673"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("hanna-a369673-" + name),
            DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) =>
        Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Named(name) : new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => new Formula.Integers();
    private static Formula Cast(Formula body, Formula type) =>
        Parenthesized(Seq(body, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula NotDvd(Formula divisor, Formula value) =>
        new Formula.Not(Parenthesized(new Formula.Relation(divisor,
            FormulaRelationOperator.Divides, value)));
    private static Formula Valuation(Formula value) => Call("padicValNat", D(5), value);
    private static Formula Factorial(Formula value) =>
        new Formula.Apply(Qualified("Nat", "factorial"), [value]);
    private static Formula Product(Formula size, Formula body) => Seq(
        new Formula.Subscript(Prod, Seq(V("k"), Sp, InMacro, Sp,
            new Formula.Apply(Qualified("Finset", "range"), [size]))),
        Sp, Parenthesized(body));

    private static Formula ClaimBody() => And(
        All("N", Naturals(), IffOf(Call("IsSquare", Call("a", V("N"))),
            NotDvd(Cast(D(4), Naturals()), V("N")))),
        And(All("n", Naturals(), NotDvd(Cast(D(5), Naturals()),
                Call("a", Add(Mul(D(2), V("n")), D(1))))),
            And(All("n", Naturals(), Eq(
                    Cast(Valuation(Call("a", Mul(D(4), V("n")))), Integers()),
                    Mul(D(2), Call("b", V("n"))))),
                All("n", Naturals(), Eq(
                    Cast(Valuation(Call("a", Add(Mul(D(4), V("n")), D(2)))), Integers()),
                    Mul(D(2), Call("b", Add(V("n"), D(1)))))))));
}
