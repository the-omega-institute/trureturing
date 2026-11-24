using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimitiveRoot;

internal sealed class PrimitiveRootCharacterSieveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/PrimitiveRoot/CharacterSieve.";
    private static readonly LibraryNoteRef Cohen =
        LibraryNoteRef.Create("D5/L/ArithUnits/cohen2015grosswald");
    private static readonly LibraryNoteRef McGown =
        LibraryNoteRef.Create("D5/L/ArithUnits/mcgown2016grosswald");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A weighted character sieve for primitive roots",
        H("A weighted character sieve for primitive roots"), Blocks(
            Describe.Lean(DescribeId.Create("primitive-root-sieve-primes"),
                DeclarationHandle.Create(Prefix + "sievePrimes"), H("The sieve primes"),
                StatementSource.FromAuthor(Disp(Eq(SievePrimes(),
                    Seq(OpenBrace, V("t"), Sp, InMacro, Sp, V("T"), Sp, Mid, Sp,
                        And(Call("Prime", V("t")),
                            And(Call("dvd", V("t"), Sub(V("p"), D(1))),
                                Not(Call("dvd", V("t"), V("e"))))), CloseBrace)))),
                AssessedProvenance.FromRepo(McGown), Blocks(Paragraph(Text(
                    "Only primes dividing p-1 that do not divide e enter " +
                    "the sieve; all other members of T are ignored."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("primitive-root-sieve-defect"),
                DeclarationHandle.Create(Prefix + "defect"), H("The exact sieve defect"),
                StatementSource.FromAuthor(Disp(Eq(Call("defect", V("p"), V("e"), V("T"), V("a")),
                    Call("if", And(EFree(), Le(D(2), BadCount())),
                        Sub(BadCount(), D(1)), D(0))))),
                AssessedProvenance.FromRepo(McGown), Blocks(Paragraph(Text(
                    "Let b(a) count the sieve primes t for which a is a t-th power. " +
                    "The defect is b(a)-1 at e-free units with b(a)>=2, and zero elsewhere. " +
                    "It is nonnegative. For nonzero supported e and a covering T it equals " +
                    "the primitive-root indicator minus the elementary sieve indicator."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("primitive-root-weight-error-bound"),
                DeclarationHandle.Create(Prefix + "primitive_weight_error_bound"),
                H("The full corrected error for arbitrary margins"),
                StatementSource.FromAuthor(Disp(WeightStatement(true))),
                AssessedProvenance.FromRepo(McGown), Blocks(Paragraph(Text(
                    "Put f=gcd(e,p-1). With the nonzero, cover and character hypotheses, use " +
                    "K_abs(f,U) to bound the absolute corrected error for every delta(U). " +
                    "No sign restriction on W or delta is needed. The signed coefficient " +
                    "K is recovered exactly when delta(U)>=0 or f has no prime factors."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primitive-root-weight-lower-bound"),
                DeclarationHandle.Create(Prefix + "primitive_weight_lower_bound"),
                H("A two-sided corrected estimate for primitive-root weight"),
                StatementSource.FromAuthor(Disp(WeightStatement())),
                AssessedProvenance.FromRepo(McGown), Blocks(Paragraph(Text(
                    "Let p be prime and e be nonzero. Put f=gcd(e,p-1). " +
                    "The set T covers the prime divisors of p-1 absent from e. Write " +
                    "U=sievePrimes(p,e,T), and R for the product of the distinct prime divisors " +
                    "of e. For nonprincipal characters whose order divides R or tR for some " +
                    "t in U, the absolute real part of the weighted character sum is at most M. " +
                    "For delta(U)>=0 or empty prime support of f, the absolute error bound " +
                    "retains the full weighted defect sum. " +
                    "W is an arbitrary real weight, with no sign restriction. Units(p) denotes " +
                    "the unit group and PrimitiveResidues(p) the residues of order p-1.")),
                    Paragraph(Text(
                    "The character expansion supplies a two-sided estimate for the " +
                    "elementary sieve " +
                    "weight. The exact pointwise identity is " +
                    "1_primitive(a)=1_f-free(a)(1-b(a))+defect(p,f,T,a). " +
                    "Multiplying by any real W(a) and summing preserves this equality. " +
                    "Thus the weighted defect belongs in the conclusion, including when it " +
                    "is negative. There is no need to compare signed terms pointwise.")),
                    Paragraph(Text(
                    "A nonnegative weighted defect gives the defect-free one-sided lower bound " +
                    "P>=theta(f)(delta(U)S-K(f,U)M), where S is the total unit weight. " +
                    "For supported e this is P>=theta(e)(delta(U)S-K(e,U)M). " +
                    "The two-sided absolute error estimate retains the defect. " +
                    "A stronger, easily checked sufficient " +
                    "condition is W(a)>=0 at every f-free unit belonging to at least two " +
                    "t-th power subgroups for t in U. Neither condition is assumed by the " +
                    "theorem. When U has at most one member, the defect vanishes. " +
                    "For negative delta the absolute coefficient K_abs gives the " +
                    "two-sided bound.")),
                Paragraph(Text(
                    "The cover is essential: p=3, e=1 and empty T would otherwise count " +
                    "weight supported at the nongenerator 1. Reducing all output parameters to f " +
                    "removes the prime-support restriction on e. At p=3, e=0, empty T and " +
                    "weight supported at 1, " +
                    "the nonzero condition prevents the false bound 1<=0. At p=3, e=2 " +
                    "and empty T, constant weight 1 with M=0 attains equality in the theta " +
                    "factor. Weight supported at 1 with M=1 attains equality in K=1. " +
                    "These parameter choices exclude a uniform increase of theta or a " +
                    "uniform decrease of K. They do not prove that the constants are " +
                    "optimal separately for every parameter choice."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primitive-root-smoothed-character-sum"),
                DeclarationHandle.Create(Prefix + "smoothedCharacterSum"),
                H("A smoothed von Mangoldt character sum"),
                StatementSource.FromAuthor(Disp(Eq(Call("S", V("p"), V("chi")),
                    Sum("m", Call("range", V("p")),
                        Mul(Mul(Call("Lambda", V("m")),
                            Sub(D(1), Div(V("m"), V("p")))),
                            Call("chi", V("m"))))))),
                AssessedProvenance.FromRepo(Cohen), Blocks(Paragraph(Text(
                    "The variable m runs through 0<=m<p. Lambda is the von Mangoldt function, " +
                    "with Lambda(0)=Lambda(1)=0. Division in the displayed sum takes place " +
                    "in the complex numbers. The real weight is nonnegative and chi is " +
                    "evaluated at m modulo p."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("primitive-root-smoothed-weight"),
                DeclarationHandle.Create(Prefix + "smoothedPrimitiveWeight"),
                H("Smoothed weight at primitive residues"),
                StatementSource.FromAuthor(Disp(Eq(Call("Psm", V("p")),
                    Sum("a", Call("PrimitiveResidues", V("p")), Call("wp", V("a")))))),
                AssessedProvenance.FromRepo(Cohen), Blocks(Paragraph(Text(
                    "Here w_p(a) is the sum of Lambda(m)(1-m/p) over 0<=m<p " +
                    "with m congruent to a modulo p."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("primitive-root-smoothed-defect"),
                DeclarationHandle.Create(Prefix + "smoothedDefect"),
                H("The full smoothed defect correction"),
                StatementSource.FromAuthor(Disp(Eq(Call("Dsm", V("p"), V("e"), V("T")),
                    Sum("a", Call("Units", V("p")), Mul(Call("wp", V("a")),
                        Call("defect", V("p"), V("e"), V("T"), V("a"))))))),
                AssessedProvenance.FromRepo(McGown), Blocks(Paragraph(Text(
                    "The parameter e is explicit; the gcd-reduced criterion uses f=gcd(e,p-1). " +
                    "Both factors in every summand are nonnegative."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("primitive-root-smoothed-weight-error"),
                DeclarationHandle.Create(Prefix + "smoothed_primitive_weight_error_bound"),
                H("A quantitative smoothed estimate after gcd reduction"),
                StatementSource.FromAuthor(Disp(SmoothedWeightStatement())),
                AssessedProvenance.FromRepo(McGown), Blocks(Paragraph(Text(
                    "Put f=gcd(e,p-1), U=sievePrimes(p,e,T) and S=Re(S(p,1)). " +
                    "The principal sum, the primitive weight and the defect D_sm(p,f,T) are " +
                    "nonnegative. The absolute difference " +
                    "P_sm(p)-D_sm(p,f,T)-theta(f)delta(U)S is at most theta(f)K_abs(f,U)M. " +
                    "This retains both sides of the estimate and applies to every delta(U). " +
                    "Only the nonzero, cover and character-bound hypotheses are needed; " +
                    "no positive margin is assumed by this quantitative theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prime-primitive-root-from-signed-smoothed-margin"),
                DeclarationHandle.Create(Prefix + "exists_prime_primitiveRoot_of_smoothed_signed"),
                H("The signed margin without a defect gain is sufficient"),
                StatementSource.FromAuthor(Disp(SignedExistenceStatement())),
                AssessedProvenance.FromRepo(McGown), Blocks(Paragraph(Text(
                    "Under the same nonzero, cover and character hypotheses, " +
                    "K(f,U)M<delta(U)Re(S(p,1)) implies the corrected positivity criterion. " +
                    "If delta(U) were nonpositive, U would contain a prime t and its " +
                    "controlled characters would force M>=0. Since K(f,U)>=0 and the " +
                    "principal smoothed sum is nonnegative, strict signed positivity " +
                    "would be impossible. The conclusion includes delta(U)>0, so K_abs=K. " +
                    "The density " +
                    "is positive and the smoothed defect is nonnegative, which gives " +
                    "the corrected criterion and then a prime primitive root below p."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("prime-primitive-root-from-smoothed-margin"),
                DeclarationHandle.Create(Prefix + "exists_prime_primitiveRoot_of_smoothed"),
                H("A positive margin yields a prime primitive root"),
                StatementSource.FromAuthor(Disp(ExistenceStatement())),
                AssessedProvenance.FromRepo(McGown), Blocks(Paragraph(Text(
                    "Let p be prime and e be nonzero. Keep the cover condition on T and " +
                    "the character-order support built from e, and bound the absolute real " +
                    "part of each supported smoothed sum by M. Put f=gcd(e,p-1). A strictly " +
                    "positive value theta(f)(delta(U)Re(S(p,1))-K_abs(f,U)M)+D_sm(p,f,T) " +
                    "produces a prime q<p of order " +
                    "p-1 modulo p. There is no extra disjunction concerning the prime support " +
                    "of e, the sign of M, or p=2.")), Paragraph(Text(
                    "The integer f is nonzero and its prime support divides p-1. The sieve " +
                    "sets U(f) and U(e) coincide, and the radical R(f) divides R(e), so every " +
                    "character needed for f is controlled by the original hypothesis. " +
                    "The arbitrary-weight gcd estimate applies to the nonnegative residue-class " +
                    "weight obtained from Lambda(m)(1-m/p). Its weighted defect is nonnegative. " +
                    "The principal character sum equals the total weight on units. Positivity " +
                    "gives m<p with Lambda(m)>0, hence m=q^k for a prime q and positive k. " +
                    "The order of q^k divides the order of q, which divides p-1. Since the " +
                    "first order is p-1, the order of q is p-1. Finally q<=q^k=m<p. " +
                    "The defect is retained in the positivity criterion, and delta " +
                    "may have either sign. " +
                    "The criterion is sufficient and does not characterize all primes " +
                    "possessing a prime primitive root.")), Paragraph(Text(
                    "Strictness matters: p=2, e=1, empty T and M=0 give zero margin, " +
                    "but no prime lies below p. Requiring two distinct prime primitive roots " +
                    "or one below the square root of p is a further question: neither " +
                    "a proof under the complete hypotheses nor a counterexample under " +
                    "those hypotheses is supplied by this estimate."))),
                DescribeRole.Theorem))));

    private static Formula SievePrimes() => Call("sievePrimes", V("p"), V("e"), V("T"));
    private static Formula Radical() => Prod("q", Call("primeFactors", V("e")), V("q"));
    private static Formula EFree() => All("q", Nat(),
        Imp(Mem(V("q"), Call("primeFactors", V("e"))),
            Not(Mem(V("a"), Call("powerSubgroup", Call("Units", V("p")), V("q"))))));
    private static Formula BadCount() => Call("card",
        Seq(OpenBrace, V("t"), Sp, InMacro, Sp, SievePrimes(), Sp, Mid, Sp,
            Mem(V("a"), Call("powerSubgroup", Call("Units", V("p")), V("t"))), CloseBrace));
    private static Formula Common(Formula body, bool weighted)
    {
        var p = V("p"); var e = V("e"); var t = V("t"); var q = V("q");
        var n = Sub(p, D(1));
        var cover = All("q", Nat(), Imp(Call("Prime", q), Imp(Call("dvd", q, n),
            Or(Call("dvd", q, e), Mem(q, V("T"))))));
        var chiSum = weighted ?
            Sum("a", Call("Residues", p), Mul(Call("W", V("a")), Call("chi", V("a")))) :
            Call("S", p, V("chi"));
        var order = Call("orderOf", V("chi"));
        var orderSupport = Or(Call("dvd", order, Radical()),
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("t"), Nat(),
                And(Mem(t, SievePrimes()), Call("dvd", order, Mul(t, Radical())))));
        var charBound = All("chi", Call("DirichletCharacter", Complex(), p),
            Imp(Not(Eq(V("chi"), D(1))), Imp(orderSupport,
                Le(Call("abs", Call("re", chiSum)), V("M")))));
        var support = Not(Eq(e, D(0)));
        var hypotheses = Imp(cover, weighted ?
            All("M", Real(), Imp(charBound, body)) : Imp(charBound, body));
        var tail = weighted ? All("e", Nat(), All("T", Call("Finset", Nat()),
            Imp(support, hypotheses))) :
            All("e", Nat(), All("T", Call("Finset", Nat()),
                All("M", Real(), Imp(support, hypotheses))));
        if (weighted)
            tail = All("W", new Formula.TypeArrow(Call("ZMod", p), Real()), tail);
        return All("p", Nat(), Imp(Call("Prime", p), tail));
    }

    private static Formula WeightStatement(bool absolute = false)
    {
        var p = V("p"); var e = GcdParameter(); var u = SievePrimes();
        var primitive = Sum("a", Call("PrimitiveResidues", p), Call("W", V("a")));
        var defect = Sum("a", Call("Units", p), Mul(Call("W", V("a")),
            Call("defect", p, e, V("T"), V("a"))));
        var main = Mul(Mul(Call("theta", e), Call("delta", u)),
            Sum("a", Call("Units", p), Call("W", V("a"))));
        var error = Mul(Mul(Call("theta", e),
            Call(absolute ? "Kabs" : "K", e, u)), V("M"));
        var estimate = Le(Call("abs", Sub(Sub(primitive, defect), main)), error);
        return Common(absolute ? estimate : Imp(Or(Le(D(0), Call("delta", u)),
            Eq(Call("primeFactors", e), Call("empty"))), estimate), true);
    }

    private static Formula GcdParameter() => Call("gcd", V("e"), Sub(V("p"), D(1)));
    private static Formula SmoothedDefect() => Call("Dsm", V("p"), GcdParameter(), V("T"));
    private static Formula SmoothedMain() => Mul(Mul(Call("theta", GcdParameter()),
        Call("delta", SievePrimes())), Call("re", Call("S", V("p"), D(1))));
    private static Formula SmoothedError() => Mul(Mul(Call("theta", GcdParameter()),
        Call("Kabs", GcdParameter(), SievePrimes())), V("M"));
    private static Formula SmoothedWeightStatement() => Common(
        And(Le(D(0), Call("re", Call("S", V("p"), D(1)))),
            And(Le(D(0), Call("Psm", V("p"))), And(Le(D(0), SmoothedDefect()),
                Le(Call("abs", Sub(Sub(Call("Psm", V("p")), SmoothedDefect()), SmoothedMain())),
                    SmoothedError())))), false);
    private static Formula ExistenceStatement() => Common(
        Imp(Lt(D(0), Add(Sub(SmoothedMain(), SmoothedError()), SmoothedDefect())),
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("q"), Nat(),
                And(Call("Prime", V("q")), And(Lt(V("q"), V("p")),
                    Eq(Call("orderOf", Call("residue", V("q"), V("p"))),
                        Sub(V("p"), D(1))))))), false);

    private static Formula SignedExistenceStatement() => Common(
        Imp(Lt(Mul(Call("K", GcdParameter(), SievePrimes()), V("M")),
                Mul(Call("delta", SievePrimes()), Call("re", Call("S", V("p"), D(1))))),
            And(Lt(D(0), Call("delta", SievePrimes())),
                new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("q"), Nat(),
                And(Call("Prime", V("q")), And(Lt(V("q"), V("p")),
                    Eq(Call("orderOf", Call("residue", V("q"), V("p"))),
                        Sub(V("p"), D(1)))))))), false);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Sum(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(V(name), Sp, InMacro, Sp, set)), Sp, Grp(body));
    private static Formula Prod(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(F.Prod, Seq(V(name), Sp, InMacro, Sp, set)), Sp, Grp(body));
}
