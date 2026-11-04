using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class RoldanCirculantEnergyP2Q3Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/RoldanCirculantEnergyP2Q3.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/roldan2026integralcirculant");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For distinct odd primes p and q, one divisor set uniquely maximises integral circulant energy at order p squared q cubed, including q = 3.",
        H("Roldán's integral circulant energy conjecture"), Blocks(
            Node("adjacency", "Integral circulant adjacency", AdjacencyFormula(),
                "Page 1, Section 1: “An integral circulant graph ICG(n, D) has vertex set Z_n and connects a and b whenever gcd(a − b, n) ∈ D, where D is a nonempty set of proper divisors of n.” The indices are Fin n, subtraction is modulo n, and the gcd uses the natural representative of that difference.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("energy", "Energy with eigenvalue multiplicity", EnergyFormula(),
                "Page 1, Section 1: “E(G) = Σ_{i=1}^n |λ_i|, where λ_1, …, λ_n are the eigenvalues of its adjacency matrix.” The multiset roots of the characteristic polynomial retain eigenvalue multiplicity. For an allowed divisor set the adjacency matrix is real symmetric.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Dstar", "The maximizing divisor set", DstarFormula(),
                "Page 3, Conjecture 1.3 uses D* = {1, p^2, pq, q^2, p^2q^2, pq^3}.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 1.3 (Universality)", Disp(Iff(F.Id("claim"), ClaimBody())),
                "Page 3, Section 1, Conjecture 1.3: “For every pair of distinct odd primes (p, q), the set D* = {1, p^2, pq, q^2, p^2q^2, pq^3} is the unique maximiser of E(p^2q^3, D) over all nonempty D ⊆ div(p^2q^3) ∖ {p^2q^3}.” The first conjunct states that Dstar is allowed; the second gives the strict comparison with every different nonempty allowed divisor set.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ramanujan_prime_power", "Ramanujan sums at prime powers", RamanujanPrimePowerFormula(),
                "For a prime p, the Ramanujan sum at p to the power k+1 is the difference of two divisibility indicators, weighted by p to the powers k+1 and k. The values lie in the complex numbers.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("ramanujan_one", "Ramanujan sum at modulus one", RamanujanOneFormula(),
                "At modulus one the Ramanujan sum equals one for every natural argument.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("gcdRow_dft_ramanujan", "Fourier transform of gcd classes", GcdRowDftFormula(),
                "For a nonzero natural n and a finite subset D of its divisors, the Fourier transform of the gcd-class indicator is the sum of the Ramanujan sums at moduli n divided by d. Nat.div denotes natural-number division. The indicator is real-valued and is cast to the complex numbers before applying ZMod.dft.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "Unique maximization for all distinct odd primes", Disp(ClaimBody()),
                "Fourier diagonalization expresses the energy as a sum of absolute Ramanujan sums with totient multiplicities. Prime-power divisor coordinates give twelve spectral classes. With u = p − 3 and v = q − 3, replacing each spectral polynomial's coefficients by their absolute values gives a majorant on the nonnegative quadrant. For Dstar the coefficients have one sign in each spectral class, so this majorant is attained. The integer coefficient comparison for every other mask gives an energy deficit of at least 96. The argument permits v = 0 and therefore includes q = 3.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("roldan-2026-integral-circulant-energy-p2q3"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("roldan-energy-" + (declaration switch { "ramanujan_prime_power" => "ramanujan-prime-power", "ramanujan_one" => "ramanujan-one", "gcdRow_dft_ramanujan" => "gcdrow-dft-ramanujan", _ => declaration.ToLowerInvariant() })), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Field(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula Call(string name, params Formula[] xs) => App(Named(name), xs);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Not(Formula a) => new Formula.Not(Parenthesized(a));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Pow(Formula a, byte n) => new Formula.Power(Parenthesized(a), D(n));
    private static Formula NatType() => Field("N");
    private static Formula FinsetNat() => Call("Finset", NatType());
    private static Formula SubsetOf(Formula a, Formula b) => Seq(a, Sp, Subseteq, Sp, b);
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Ord(Formula p, Formula q) => Mul(Pow(p, 2), Pow(q, 3));
    private static Formula Val(Formula x) => Call("val", x);
    private static Formula FinType(Formula n) => Call("Fin", n);

    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Divides(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Divides, b);
    private static Formula If(Formula condition, Formula yes, Formula no) => Seq(
        Named("if"), Sp, condition, Sp, Named("then"), Sp, yes, Sp, Named("else"), Sp, no);
    private static Formula Fun(string name, Formula type, Formula body) => Seq(
        Named("fun"), Sp, Typed(F.Id(name), type), Sp, Mapsto, Sp, body);

    private static Formula RamanujanPrimePowerFormula()
    {
        Formula p = F.Id("p"), j = F.Id("j"), k = F.Id("k");
        Formula pk = Power(p, k), next = Power(p, Add(k, D(1)));
        Formula rhs = Sub(Parenthesized(If(Divides(next, j), Typed(next, Field("C")), D(0))),
            Parenthesized(If(Divides(pk, j), Typed(pk, Field("C")), D(0))));
        return Disp(All("p", NatType(), All("j", NatType(), All("k", NatType(),
            Imp(App(Q("Nat", "Prime"), p), Eqn(Call("ramanujanSum", next, j), rhs))))));
    }

    private static Formula RamanujanOneFormula()
    {
        Formula j = F.Id("j");
        return Disp(All("j", NatType(), Eqn(Call("ramanujanSum", D(1), j), Typed(D(1), Field("C")))));
    }

    private static Formula GcdRowDftFormula()
    {
        Formula n = F.Id("n"), dset = F.Id("D"), j = F.Id("j"), k = F.Id("k"), d = F.Id("d");
        Formula zmod = Call("ZMod", n);
        Formula indicator = Fun("k", zmod, If(Member(App(Q("Nat", "gcd"), n, Val(k)), dset),
            Typed(D(1), Field("R")), D(0)));
        Formula row = Fun("k", zmod, Typed(App(Parenthesized(indicator), k), Field("C")));
        Formula rhs = Seq(Sum, Underscore, Grp(Member(d, dset)), Sp,
            Call("ramanujanSum", App(Q("Nat", "div"), n, d), Val(j)));
        Formula statement = All("D", FinsetNat(), Imp(SubsetOf(dset, App(Q("Nat", "divisors"), n)),
            All("j", zmod, Eqn(App(Q("ZMod", "dft"), Parenthesized(row), j), rhs))));
        return Disp(All("n", NatType(), Seq(OpenBracket, Call("NeZero", n), CloseBracket, Comma, Sp, statement)));
    }

    private static Formula AdjacencyFormula()
    {
        Formula n = F.Id("n"), d = F.Id("D"), a = F.Id("a"), b = F.Id("b");
        Formula difference = new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
        Formula condition = Member(App(Q("Nat", "gcd"), Val(difference), n), d);
        Formula entry = Seq(Named("if"), Sp, condition, Sp, Named("then"), Sp, D(1), Sp, Named("else"), Sp, D(0));
        return Disp(All("n", NatType(), All("D", FinsetNat(), All("a", FinType(n), All("b", FinType(n),
            Eqn(Call("adjacency", n, d, a, b), entry))))));
    }

    private static Formula EnergyFormula()
    {
        Formula n = F.Id("n"), d = F.Id("D"), x = F.Id("x");
        Formula roots = App(Q("Polynomial", "roots"), App(Q("Matrix", "charpoly"), Call("adjacency", n, d)));
        Formula function = Seq(Named("fun"), Sp, x, Sp, Mapsto, Sp, Seq(Bar, x, Bar));
        return Disp(All("n", NatType(), All("D", FinsetNat(), Eqn(Call("energy", n, d),
            App(Q("Multiset", "sum"), App(Q("Multiset", "map"), function, roots))))));
    }

    private static Formula DstarFormula()
    {
        Formula p = F.Id("p"), q = F.Id("q");
        Formula data = Seq(OpenBrace, D(1), Comma, Sp, Pow(p, 2), Comma, Sp, Mul(p, q), Comma, Sp,
            Pow(q, 2), Comma, Sp, Mul(Pow(p, 2), Pow(q, 2)), Comma, Sp, Mul(p, Pow(q, 3)), CloseBrace);
        return Disp(All("p", NatType(), All("q", NatType(), Eqn(Call("Dstar", p, q), data))));
    }

    private static Formula ClaimBody()
    {
        Formula p = F.Id("p"), q = F.Id("q"), d = F.Id("D");
        Formula n = Ord(p, q), star = Call("Dstar", p, q), proper = App(Q("Nat", "properDivisors"), n);
        Formula comparison = All("D", FinsetNat(), Imp(App(Q("Finset", "Nonempty"), d),
            Imp(SubsetOf(d, proper), Imp(Not(Eqn(d, star)), Less(Call("energy", n, d), Call("energy", n, star))))));
        return All("p", NatType(), All("q", NatType(), Imp(App(Q("Nat", "Prime"), p),
            Imp(App(Q("Nat", "Prime"), q), Imp(Not(Eqn(p, q)), Imp(Call("Odd", p), Imp(Call("Odd", q),
                And(SubsetOf(star, proper), comparison))))))));
    }
}
