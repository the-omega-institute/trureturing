using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Combinatorics;

internal sealed class KarttunenParityDirichletConvolutionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Factorization/karttunen2024a369255");
    private static readonly Formula N = F.Id("n");
    private static readonly Formula Dv = F.Id("d");
    private static readonly Formula P = F.Id("p");
    private static readonly Formula Rs = F.Id("rs");
    private const string Conjectures =
        "OEIS A369255, revision 15, FORMULA block (unpaginated). "
        + "“Following convolution formulas have been conjectured for this sequence by Sequence Machine, with both computing the first 2^20 terms correctly:” "
        + "“a(n) = Sum_{d|n} A007875(d)*A219009(n/d).” "
        + "“a(n) = Sum_{d|n} A140773(d)*A355837(n/d).” "
        + "OEIS A140773, revision 51, FORMULA (unpaginated). "
        + "“a(n) = Sum_{m|n} A038548(m) = Sum_{m|n} ceiling(d(m)/2), where d(m) = number of divisors of m (A000005). - _Manfred Boergens_, Feb 25 2021” "
        + "The offset is one. A140773 is the sum of g over positive divisors, and A369255 is its natural remainder modulo two. "
        + "Both divisor sums use integer coefficients. Nat.div is natural-number division.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two A369255 Dirichlet convolutions.",
        H("The two A369255 Dirichlet convolutions"),
        Blocks(
            SourceDefinition("g", "Divisors at most the square root",
                AllN(Equal(Call("g", N), App(Qualified("Finset", "card"),
                    App(Qualified("Finset", "filter"),
                        Lambda("d", F.Id("Nat"), Le(Multiply(Dv, Dv), N)), Divisors(N))))),
                "OEIS A038548, revision 195, NAME (unpaginated). “Number of divisors of n that are at most sqrt(n).” "
                + "For positive n the condition d * d ≤ n retains the divisor on the diagonal when n is a square."),
            SourceDefinition("A", "Unordered coprime factor pairs",
                AllN(Equal(Call("A", N), App(Qualified("Finset", "card"),
                    App(Qualified("Finset", "filter"),
                        Lambda("rs", Seq(F.Id("Nat"), Sp, Times, Sp, F.Id("Nat")), And(
                            Le(App(Qualified("Prod", "fst"), Rs), App(Qualified("Prod", "snd"), Rs)),
                            App(Qualified("Nat", "Coprime"),
                                Parenthesized(App(Qualified("Prod", "fst"), Rs)),
                                Parenthesized(App(Qualified("Prod", "snd"), Rs))))),
                        Parenthesized(App(Qualified("Nat", "divisorsAntidiagonal"), N)))))),
                "OEIS A007875, revision 82, NAME (unpaginated). “Number of ways of writing n as p*q, with p <= q, gcd(p, q) = 1.” "
                + "The two factors are positive. The pair (1,1) contributes at n = 1."),
            SourceDefinition("B", "Möbius convolution with the fourth-power indicator",
                AllN(Equal(Call("B", N), Sum(N, "d",
                    Seq(F.Id("if"), Sp,
                        Parenthesized(new Formula.Relation(Power(Dv, D(4)), FormulaRelationOperator.Divides, N)),
                        Sp, F.Id("then"), Sp,
                        App(Qualified("ArithmeticFunction", "moebius"), NatDiv(N, Power(Dv, D(4)))),
                        Sp, F.Id("else"), Sp, D(0))))),
                "OEIS A219009, revision 44, program line (unpaginated). “a(n)=sumdiv(n,d,if(issquare(d),issquare(sqrtint(d)),0)*moebius(n/d))” "
                + "Index each fourth-power divisor by its positive fourth root. Nat.div computes the quotient exactly on the branch where the fourth power divides n."),
            SourceDefinition("C", "The multiplicative prime-power prescription",
                AllN(Equal(Call("C", N), App(Qualified("Finset", "prod"),
                    Parenthesized(App(Qualified("Nat", "primeFactors"), N)),
                    Lambda("p", F.Id("Nat"), Multiply(
                        Multiply(Cast(D(2), "Int"), Cast(NatMod(Factorization(), D(2)), "Int")),
                        Power(Cast(Parenthesized(Seq(Minus, D(1))), "Int"),
                            NatDiv(Add(Factorization(), D(1)), D(2)))))))),
                "OEIS A355837, revision 25, FORMULA (unpaginated). “Multiplicative with a(p^e) = 2 * (e mod 2) * (-1)^((e+1)/2) for prime p and e>0.” "
                + "The empty product gives C(1) = 1. Nat.div gives the integer exponent on odd e. On even positive e the remainder factor is zero."),
            SourceDefinition("claim", "Both positive-index conjectures",
                Equal(F.Id("claim"), Parenthesized(ClaimBody())), Conjectures),
            Node("result", "Both identities", ClaimBody(), AssessedProvenance.FromRepo(Source),
                "Swapping the two factors counts diagonal pairs once and off-diagonal pairs twice. The prime-power convolution identities reduce both doubled sums to the same arithmetic function, whose values are zero or two. The coefficient C(1) is one and every later coefficient is even, so convolution by C preserves the residue modulo two.",
                DescribeRole.Theorem))));

    private static DocumentBlock SourceDefinition(string name, string title, Formula formula, string prose) =>
        Node(name, title, formula, AssessedProvenance.FromLiterature(Source), prose, DescribeRole.Definition);

    private static DocumentBlock Node(string name, string title, Formula formula,
        AssessedProvenance provenance, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create("a369255-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula ClaimBody()
    {
        Formula parity = Cast(NatMod(DivisorCountSum(N), D(2)), "Int");
        Formula quotient = NatDiv(N, Dv);
        Formula first = Equal(parity, Sum(N, "d", Multiply(Cast(Call("A", Dv), "Int"), Call("B", quotient))));
        Formula second = Equal(parity, Sum(N, "d", Multiply(Cast(DivisorCountSum(Dv), "Int"), Call("C", quotient))));
        return AllN(new Formula.Logic(Parenthesized(Le(D(1), N)), FormulaLogicOperator.Implies,
            Parenthesized(And(Parenthesized(first), Parenthesized(second)))));
    }

    private static Formula DivisorCountSum(Formula n) => Sum(n, "m", Call("g", F.Id("m")));
    private static Formula AllN(Formula formula) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"), F.Id("Nat"), formula);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Colon, type)), Sp, Mapsto, Sp, body));
    private static Formula Sum(Formula n, string name, Formula body) =>
        App(Qualified("Finset", "sum"), Divisors(n), Lambda(name, F.Id("Nat"), body));
    private static Formula Divisors(Formula n) => Parenthesized(App(Qualified("Nat", "divisors"), n));
    private static Formula Factorization() => Parenthesized(App(Qualified("Nat", "factorization"), N, P));
    private static Formula NatDiv(Formula dividend, Formula divisor) =>
        Parenthesized(App(Qualified("Nat", "div"), dividend, divisor));
    private static Formula NatMod(Formula dividend, Formula divisor) =>
        Parenthesized(App(Qualified("Nat", "mod"), Parenthesized(dividend), divisor));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula Cast(Formula value, string type) => Parenthesized(Seq(value, Colon, F.Id(type)));
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
}
