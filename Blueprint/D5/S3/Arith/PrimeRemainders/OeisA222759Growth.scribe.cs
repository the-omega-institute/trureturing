using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimeRemainders;

internal sealed class OeisA222759GrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/PrimeRemainders/OeisA222759Growth.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/noe2013a222759");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime threshold places the cubes of the first k primes below n.",
        H("The first growth assertion of OEIS A222759"),
        Blocks(
            Node("one-based-prime", "One-based prime enumeration", PrimeFormula(),
                "For j at least one, P(j) is the j-th prime, with P(1)=2. "
                + "nth(Prime,t) denotes Mathlib's zero-based prime enumeration. "
                + "The subtraction j-1 is natural subtraction; the unused extension P(0)=2 "
                + "does not alter any positive index in the assertion.",
                "P", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("literal-cubic-remainder", "The literal cubic remainder", RemainderFormula(),
                "choose(a,b) is the natural binomial coefficient. NatMod(a,m) is the "
                + "least nonnegative remainder on division by a positive m, with NatMod(a,0)=a. Thus for "
                + "a positive prime q, cubicRemainder(n,q) lies between zero and q cubed "
                + "minus one. It is compared with the integer n itself.",
                "cubicRemainder", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("complete-first-growth", "At least k distinct prime witnesses", ResultFormula(),
                "For every natural k at least three and every positive natural n at or "
                + "above P(P(k)^3), the displayed injection supplies k distinct positive "
                + "primes. Positive integers and positive naturals describe the same domain "
                + "here. Fin(k) has indices 0 through k-1, and Injective is Function.Injective. "
                + "The proof chooses q(i)=nth(Prime,i), the first k primes. Mathlib's "
                + "Nat.add_two_le_nth_prime at t=j-1 gives P(j)>=j+1 for positive j. "
                + "With j=P(k)^3, the threshold therefore implies P(k)^3<n, including "
                + "equality n=P(P(k)^3) in the hypothesis. Nat.nth_injective and "
                + "Nat.prime_nth_prime give distinct prime witnesses; Nat.nth_monotone "
                + "gives q(i)<=P(k). Hence q(i)^3<=P(k)^3<n. Nat.mod_lt gives "
                + "cubicRemainder(n,q(i))<q(i)^3<n, proving the required inequality. "
                + "The argument uses the literal remainder range and needs no special "
                + "binomial identity. It asserts the first growth clause for every k,n "
                + "in its stated domain, without assuming that the full set of primes "
                + "satisfying the predicate is finite.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("noe-2013-a222759-prime-cube-growth"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula PrimeFormula() => Disp(All("j", Naturals(),
        Eq(Call("P", F.Id("j")), Call("nth", F.Id("Prime"),
            new Formula.Binary(F.Id("j"), FormulaBinaryOperator.Subtract, D(1))))));

    private static Formula RemainderFormula()
    {
        var n = F.Id("n"); var q = F.Id("q");
        return Disp(All("n", Naturals(), All("q", Naturals(),
            Eq(Call("cubicRemainder", n, q),
                Call("NatMod", Call("choose", Mul(n, q), q), Cube(q))))));
    }

    private static Formula ResultFormula()
    {
        var k = F.Id("k"); var n = F.Id("n"); var q = F.Id("q"); var i = F.Id("i");
        var qi = Call("q", i);
        var pointwise = All("i", Call("Fin", k), And(Lt(D(0), qi),
            And(Call("Prime", qi), new Formula.Relation(Call("cubicRemainder", n, qi),
                FormulaRelationOperator.NotEqual, n))));
        var witnesses = Some("q", Seq(Open, Call("Fin", k), Sp, To, Sp, Naturals(), Close),
            And(Call("Injective", q), pointwise));
        return Disp(All("k", Naturals(), All("n", Naturals(),
            Imp(Le(D(3), k), Imp(Le(D(1), n),
                Imp(Le(Call("P", Cube(Call("P", k))), n), witnesses))))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Cube(Formula a) => new Formula.Power(a, D(3));
}
