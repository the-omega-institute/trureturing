using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DirichletRoots;

internal sealed class OeisA318314Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/DirichletRoots/OeisA318314.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/oeis2018a318314");
    private static Formula N => F.Id("n");
    private static Formula E => F.Id("e");
    private static Formula P => F.Id("p");
    private static Formula U => F.Id("u");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rational recurrence, local coefficients and denominator mechanism of OEIS A318314.",
        H("The rational Dirichlet square root in OEIS A318314"),
        Blocks(
            Node("oddUnitaryCount", "Odd unitary divisors", Eq(Call("g", N), Call("oddUnitaryCount", N)),
                "For each natural n, g(n) counts d in the positive divisors of n for which d is odd and gcd(d,n/d)=1. This is the independent A068068 definition.", DescribeRole.Definition, true),
            Node("interior", "Interior divisors", Eq(Call("interior", N), Call("properInteriorDivisors", N)),
                "The interior set consists exactly of the positive divisors d of n satisfying 1<d<n; both endpoint divisors are excluded.", DescribeRole.Definition, false),
            Node("f", "The actual rational recurrence", new Formula.Aligned([
                Eq(Call("f", D(0)), D(0)), Eq(Call("f", D(1)), D(1)),
                All("n", Imp(Lt(D(1), N), Eq(Call("f", N),
                    new Formula.Fraction(Sub(Call("g", N), Call("interiorSquareSum", F.Id("f"), N)), D(2))))) ]),
                "The interior square sum is the sum of f(d)f(n/d) over interior(n). Both recursive arguments are strictly below n. The extension f(0)=0 leaves the entire positive source domain unchanged.", DescribeRole.Definition, false),
            Node("SourceSpec", "The source specification", Eq(Call("SourceSpec", U), And(
                Eq(Call("u", D(1)), D(1)), All("n", Imp(Lt(D(1), N), Eq(Call("u", N),
                    new Formula.Fraction(Sub(Call("g", N), Call("interiorSquareSum", U, N)), D(2))))))),
                "A source solution has unit head and the published recurrence at every n>1. No multiplicativity, nonzero value, finite support or exponent bound is assumed.", DescribeRole.Definition, false),
            Node("source_solution_unique", "Existence and uniqueness on the full positive domain", And(
                Call("SourceSpec", F.Id("f")),
                new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("u"),
                    new Formula.Power(Rationals(), Naturals()), Imp(Call("SourceSpec", U),
                        All("n", Imp(Lt(D(0), N), Eq(Call("u", N), Call("f", N))))))),
                "The explicitly recursive f inhabits the source specification. Strong induction identifies every other source solution at every positive index, since d and n/d in an interior term are positive and strictly smaller than n.", DescribeRole.Theorem, false),
            Node("central", "Central-binomial rational coefficients", Eq(Call("C", E),
                new Formula.Fraction(Call("centralBinom", E), Pow(D(4), E))),
                "Here centralBinom(e) is binom(2e,e). In particular C(0)=1; no rational denominator is defined by the conjectured formula.", DescribeRole.Definition, false),
            Node("central_local_square", "The local square at two", All("e", And(Lt(D(0), Call("C", E)),
                Eq(Call("centralConvolution", E), D(1)))),
                "The convolution sums C(i)C(j) over all nonnegative i+j=e. The central-binomial recurrence identifies C(e) with (-1)^e choose(-1/2,e); Chu-Vandermonde then gives the self-convolution exactly.", DescribeRole.Theorem, false),
            Node("binaryWeight", "Binary digit sum", Eq(Call("s", E), Call("binaryDigitSum", E)),
                "s(e)=A000120(e) includes s(0)=0. The inequality s(e)<=e is used before converting ordinary integer subtraction to natural exponents.", DescribeRole.Definition, true),
            Node("central_denominator", "Exact central denominators", All("e", And(
                Eq(Den(Call("C", E)), Pow(D(2), Sub(Mul(D(2), E), Call("s", E)))),
                Eq(Call("integerCast", Call("naturalSub", Mul(D(2), E), Call("s", E))),
                    Sub(Mul(D(2), Call("integerCast", E)), Call("integerCast", Call("s", E)))))),
                "Kummer's digit-sum theorem gives the two-adic valuation s(e) of binom(2e,e). Removing precisely this power leaves an odd numerator and proves the reduced denominator, including e=0. The second conjunct states the integer-subtraction correspondence explicitly.", DescribeRole.Theorem, false),
            Node("halvingSum", "The independent A005187 recurrence", new Formula.Aligned([
                Eq(Call("T", D(0)), D(0)), All("e", Imp(Lt(D(0), E),
                    Eq(Call("T", E), Add(E, Call("T", Call("halfFloor", E)))))) ]),
                "T is independently defined by halving recursion. The binary digit identity proves T(e)=2e-s(e) for every natural e.", DescribeRole.Definition, true),
            Node("localCoefficient", "Prime-local rational factors", new Formula.Aligned([
                Eq(Call("L", D(2), E), Call("C", E)),
                All("p", Imp(Neq(P, D(2)), Eq(Call("L", P, E), Call("C", Call("halfFloor", E))))) ]),
                "The local coefficient at two is C(e); at every other prime it is C(floor(e/2)). Both choices give one when e=0.", DescribeRole.Definition, false),
            Node("local_denominators", "All local denominator formulas", LocalFormulas(),
                "For odd primes, 2 floor(e/2)-s(floor(e/2))=e-s(e). A prime is even precisely when it equals two. These facts give all three local formulas and the explicit ordinary-integer exponent identity.", DescribeRole.Theorem, false),
            Node("auxiliary", "The independent A317934 Euler product", Eq(Call("b", N), Call("auxiliaryEulerProduct", N)),
                "b(n) is the product of 2^(e-s(e)) over the prime factorization of n. Its independent multiplicativity and prime-power prescription are proved by disjoint factorization supports, rather than assumed for the target denominator.", DescribeRole.Definition, true),
            Node("twoPart", "The highest power of two dividing n", Eq(Call("twoPart", N), Pow(D(2), Call("valuationTwo", N))),
                "On positive indices this is A006519(n), with value one at n=1.", DescribeRole.Definition, true),
            Node("a", "The actual reduced denominator", Eq(Call("a", N), Den(Call("f", N))),
                "The denominator is the positive reduced rational denominator, with den(0)=1. This definition refers to the source recurrence f.", DescribeRole.Definition, true),
            Node("root", "An independent global rational Euler product", Eq(Call("R", N), Call("localEulerProduct", N)),
                "For positive n, R(n) is the product of L(p,e) over the actual prime factorization n. Set R(0)=0. This is a rational construction; equality with the source recurrence is a separate mathematical obligation.", DescribeRole.Definition, false),
            Node("root_structure", "Multiplicativity and positivity of the rational product", And(
                Call("Multiplicative", F.Id("R")), And(All("p", All("e", Imp(Call("Prime", P),
                    Eq(Call("R", Pow(P, E)), Call("L", P, E))))),
                    All("n", Imp(Lt(D(0), N), Lt(D(0), Call("R", N)))))),
                "Disjoint prime supports prove rational multiplicativity; the single-prime factorization gives every prime-power value, including exponent zero. Every central coefficient is positive, so every positive-index product is positive.", DescribeRole.Theorem, false),
            Node("root_denominator", "The global no-cancellation denominator identity", All("n", Imp(Lt(D(0), N),
                Eq(Den(Call("R", N)), Mul(Call("twoPart", N), Call("b", N))))),
                "Each local factor has an odd natural numerator over a power of two. Finite multiplication preserves oddness, so cross-cancellation is impossible. The dyadic exponent separates into v_2(n) plus the sum of e-s(e) over all prime factors.", DescribeRole.Theorem, false),
            Node("odd_local_square", "The local square at odd primes", All("e", Eq(Call("oddConvolution", E),
                Call("unitThenTwo", E))),
                "The odd convolution sums C(floor(i/2))C(floor(j/2)) over i+j=e. Its series is (1+x)B(x^2), whose square is (1+x)/(1-x). The constant coefficient is one and every positive coefficient is two.", DescribeRole.Theorem, false),
            Node("source_convolution", "The exact source divisor-square identity", All("n", Imp(Lt(D(0), N),
                Eq(Call("divisorSquareSum", F.Id("f"), N), Call("g", N)))),
                "The full divisor sum has endpoint contributions f(1)f(n) and f(n)f(1), each equal to f(n). Removing both endpoints recovers precisely the original recurrence. At n=1 both sides are one.", DescribeRole.Theorem, false),
            Node("auxiliary_structure", "The independent multiplicative prescription", And(
                Eq(Call("b", D(1)), D(1)), And(All("m", All("n", Imp(Call("Coprime", F.Id("m"), N),
                    Eq(Call("b", Mul(F.Id("m"), N)), Mul(Call("b", F.Id("m")), Call("b", N)))))),
                    All("p", All("e", Imp(Call("Prime", P), Eq(Call("b", Pow(P, E)),
                        Pow(D(2), Sub(E, Call("s", E))))))))),
                "The factorization-product definition has unit head, multiplies over coprime arguments and has exactly the independent A317934 values at every prime power.", DescribeRole.Theorem, false),
            Node("WholeBlock", "The entire published question", WholeFormula(),
                "This proposition includes the actual source specification and its positive-index uniqueness, the product identity, a(1)=1, positive coprime multiplicativity, both prime-power types and the all-prime parity formula with explicit integer-subtraction correspondence. No theorem here asserts this full proposition until the independent Euler product has been identified with the original odd-unitary-count recurrence.", DescribeRole.Definition, false)
        )));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
        DescribeId.Create("a318314-" + name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(Disp(formula)),
        literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula LocalFormulas() => And(
        All("e", Eq(Den(Call("L", D(2), E)), Pow(D(2), Call("T", E)))),
        And(All("p", All("e", Imp(And(Call("Prime", P), Neq(P, D(2))),
            Eq(Den(Call("L", P, E)), Pow(D(2), Sub(E, Call("s", E))))))),
            All("p", All("e", Imp(Call("Prime", P), And(
                Eq(Den(Call("L", P, E)), Pow(D(2), ParityExponent())), IntegerExponent()))))));

    private static Formula WholeFormula() => And(Call("SourceSpec", F.Id("f")),
        And(Call("PositiveIndexUnique", F.Id("f")), And(
            All("n", Imp(Lt(D(0), N), Eq(Call("a", N), Mul(Call("twoPart", N), Call("b", N))))),
            And(Eq(Call("a", D(1)), D(1)), And(
                All("m", All("n", Imp(And(Lt(D(0), F.Id("m")), And(Lt(D(0), N), Call("Coprime", F.Id("m"), N))),
                    Eq(Call("a", Mul(F.Id("m"), N)), Mul(Call("a", F.Id("m")), Call("a", N)))))),
                And(All("e", Eq(Call("a", Pow(D(2), E)), Pow(D(2), Call("T", E)))),
                    And(All("p", All("e", Imp(And(Call("Prime", P), Neq(P, D(2))),
                        Eq(Call("a", Pow(P, E)), Pow(D(2), Sub(E, Call("s", E))))))),
                        All("p", All("e", Imp(Call("Prime", P), And(
                            Eq(Call("a", Pow(P, E)), Pow(D(2), ParityExponent())), IntegerExponent())))))))))));

    private static Formula ParityExponent() => Sub(Mul(Sub(D(2), Call("mod", P, D(2))), E), Call("s", E));
    private static Formula IntegerExponent() => Eq(Call("integerCast", Call("naturalParityExponent", P, E)),
        Sub(Mul(Sub(D(2), Call("mod", Call("integerCast", P), D(2))), Call("integerCast", E)),
            Call("integerCast", Call("s", E))));
    private static Formula All(string n, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll,
        FormulaIdentifier.Create(n), Naturals(), body);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Neq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Den(Formula a) => Call("den", a);
}
