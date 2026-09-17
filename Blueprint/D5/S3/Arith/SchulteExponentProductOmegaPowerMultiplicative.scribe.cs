using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class SchulteExponentProductOmegaPowerMultiplicativeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/SchulteExponentProductOmegaPowerMultiplicative.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/schulte2018a322327");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schulte's A322327 exponent-product function is multiplicative with prescribed prime powers.",
        H("Schulte's Exponent-Product Multiplicativity Conjecture"),
        Blocks(
            Paragraph(Text(
                "N denotes the natural numbers including zero and Z denotes the integers. "
                    + "For n in N, primeFactors(n) is the finite set of prime divisors, "
                    + "factorization(n,p), also written v_p(n), is the natural exponent of p "
                    + "in n, and A005361(n) is the product of those exponents. The empty "
                    + "product gives A005361(1)=1. The function omega(n) counts distinct prime "
                    + "divisors, k is an arbitrary integer parameter, and a_k(n) is integer "
                    + "valued. Coprimality means gcd(m,n)=1. Lean's power convention gives "
                    + "0^0=1. The formal claim covers, for every integer k, multiplicativity "
                    + "on coprime natural arguments and the value k times e at every positive "
                    + "prime-power exponent. The trailing OEIS sequence correspondences are "
                    + "outside the claim.")),
            Node("a", "The exponent-product function", AFormula(),
                "The finite product is A005361(n); each natural exponent is explicitly cast "
                    + "to an integer before multiplication by the integer power k^omega(n).",
                DescribeRole.Definition),
            Node("result", "Schulte's multiplicativity and prime-power formula", ResultFormula(),
                "For every integer k, the first conjunct states multiplicativity on coprime "
                    + "natural arguments and the second gives a_k(p^e)=k times e for prime p "
                    + "and positive e. This settles the two assertions in the OEIS conjecture "
                    + "sentence within the stated scope.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a322327-schulte-exponent-product-omega-power-multiplicative"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(
            DescribeId.Create("a322327-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula AFormula()
    {
        Formula k = F.Id("k"), n = F.Id("n"), p = F.Id("p");
        Formula index = new Formula.Relation(p, FormulaRelationOperator.MemberOf,
            Call("primeFactors", n));
        Formula product = Seq(new Formula.Subscript(Prod, index), Sp,
            Call("intCast", Call("factorization", n, p)));
        Formula value = Multiply(product, new Formula.Power(k, Call("omega", n)));
        return Disp(Seq(Bound(k, Integers()), Bound(n, Naturals()),
            Equal(A(k, n), value)));
    }

    private static Formula ResultFormula()
    {
        Formula k = F.Id("k"), m = F.Id("m"), n = F.Id("n");
        Formula p = F.Id("p"), e = F.Id("e");
        Formula coprime = Equal(Call("gcd", m, n), D(1));
        Formula multiplicative = Seq(Bound(m, Naturals()), Bound(n, Naturals()),
            Implies(coprime,
                Equal(A(k, Multiply(m, n)), Multiply(A(k, m), A(k, n)))));
        Formula primePower = Seq(Bound(p, Naturals()), Bound(e, Naturals()),
            Implies(Call("Prime", p),
                Implies(LessThan(D(0), e),
                    Equal(A(k, new Formula.Power(p, e)), Multiply(k, Call("intCast", e))))));
        Formula conjunction = new Formula.Logic(
            Parenthesized(multiplicative), FormulaLogicOperator.And,
            Parenthesized(primePower));
        return Disp(Seq(Bound(k, Integers()), conjunction));
    }

    private static Formula A(Formula k, Formula n) =>
        Call(new Formula.Subscript(F.Id("a"), k), n);
    private static Formula Call(string name, params Formula[] arguments) =>
        Call(Named(name), arguments);
    private static Formula Call(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Bound(Formula variable, Formula domain) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, domain, Comma, Sp);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessThan(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(
            Parenthesized(hypothesis), FormulaLogicOperator.Implies,
            Parenthesized(conclusion));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
}
