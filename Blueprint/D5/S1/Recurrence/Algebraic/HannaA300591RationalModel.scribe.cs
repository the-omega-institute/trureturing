using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaA300591RationalModelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaA300591RationalModel.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/hanna2018a300591");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized rational ordinary series and its exponential companion are unique. " +
        "Its ordinary coefficients are integers in every degree, and every positive-index " +
        "coefficient is an integer multiple of its index.",
        H("The rational model of Hanna A300591"), Blocks(
            Node("expSeries", "Formal scalar exponential",
                All("t", Q(), All("F", Series(), Eqn(Call("expSeries", V("t"), V("F")),
                    Call("subst", Mul(Call("C", V("t")), V("F")), Call("exp", Q()))))),
                "The operation is substitution into the formal exponential over Q. " +
                "The first argument of PowerSeries.subst is the inner series. " +
                "When the inner series has constant coefficient zero, this is exp(t F).",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("IsSource", "The original ordinary-series equation",
                All("F", Series(), Iffn(Call("IsSource", V("F")), SourceBody(V("F")))),
                "OEIS A300591 NAME gives [x^n]exp(n^2 A)=n^2[x^(n-1)]exp(n^2 A) " +
                "for every n>=1. Its OFFSET starts at one. The normalized extension has " +
                "constant coefficient zero. Every coefficient here is an ordinary coefficient, " +
                "and the ambient coefficient field is Q. Integrality is not a hypothesis.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("triangular_exists_unique", "Unique rational normalized triangular source",
                TriangularBody(),
                "The functions lam and mu are arbitrary rational-valued functions on the natural numbers, " +
                "and lam(n) is nonzero for every n>=1. A degree-n change of the exponent changes the " +
                "degree-n exponential coefficient by lam(n) times that change and preserves all lower " +
                "coefficients. The derivative recurrence and coefficient agreement give this residual " +
                "identity. PowerSeriesNormalizedContraction.exists_unique_fixed then constructs the " +
                "unique normalized solution over Q. Taking lam(n)=mu(n)=n^2 gives the original " +
                "A300591 source, before any arithmetic assertion. No integral ambient series, " +
                "coefficient cutoff or positivity premise is used. The same triangular theorem with " +
                "lam(n)=mu(n)=n^3 gives the rational characterization used by HannaA300595Integrality.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("source_local_quotient", "Local quotient integrality at index primes",
                LocalQuotientBody(),
                "For every rational source F, every n>=2, and every prime p dividing n, " +
                "local integrality of the strict prefix alone implies that [x^n]F/n " +
                "has denominator coprime to p. The proof truncates before degree n. " +
                "For h=v_p(t)>=1, the degree-(n-1) exponential coefficient has valuation " +
                "at least h, and the degree-n coefficient of the strict prefix has " +
                "valuation at least 2h-1. These bounds use v_p(j!)<j and the vanishing " +
                "of the zero-th and first power contributions at degree n. The original " +
                "equation then gives v_p([x^n]F)>=h-1 for a nonzero coefficient. " +
                "With t=n^2, this is enough for the quotient because " +
                "2v_p(n)-1>=v_p(n). Zero coefficients are handled separately. " +
                "The same bound is used for every prime, including two; no stronger " +
                "odd-prime estimate is asserted. This result assumes no integrality " +
                "of the next coefficient and uses no signed-counting premise.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("source_denominator_obstruction", "The precise possible first denominator obstruction",
                ObstructionBody(),
                "If every coefficient before degree n is an integer and the coefficient " +
                "at degree n is not, then n>=2 and its reduced denominator has a prime " +
                "divisor p<n with p not dividing n. The constant coefficient is zero " +
                "and the degree-one source equation forces [x]F=1. Index primes are " +
                "excluded by source_local_quotient. For p>n, every factorial denominator " +
                "in the finite exponential coefficient formula is a p-unit, so the " +
                "strict prefix and the degree equation give local integrality directly. " +
                "The theorem locates a possible obstruction; it does not exclude the " +
                "remaining primes p<n coprime to n.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("source_divisible_of_integral", "Ordinary integrality implies integer divisibility",
                DivisibilityBody(),
                "For a source F with every ordinary coefficient integral, every positive " +
                "coefficient equals n times an integer. At primes dividing n, the proof " +
                "uses source_local_quotient and the actual strict prefix. At other primes, " +
                "division by n preserves local integrality of the integer coefficient. " +
                "The existing integral_of_local theorem supplies an integer witness for " +
                "the quotient. Degree one and the auxiliary quotient's zero slot are " +
                "handled separately. This theorem has an explicit integrality premise; " +
                "source_integral_and_divisible discharges it for every source.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("source_integral_and_divisible", "Ordinary integrality and positive-index divisibility",
                All("F", Series(), Imp(Call("IsSource", V("F")),
                    And(All("r", N(), Integral(Coeff(V("r"), V("F")))),
                        All("n", N(), Imp(Leq(D(1), V("n")),
                            Ex("q", Z(), Eqn(Coeff(V("n"), V("F")),
                                Mul(Cast(V("n")), Cast(V("q")))))))))),
                "For every rational source F, all ordinary coefficients, including degree " +
                "zero, are integers, and [x^n]F=n q_n with q_n in Z for every n>=1. " +
                "Strong induction uses the actual integral strict prefix to choose integer " +
                "colors. Its polynomial agrees with F below the current degree. The existing " +
                "exponential agreement and residual identities transfer every lower source " +
                "equation and identify the current residual with -n^2[x^n]F. The signed " +
                "assembly/Sylow theorem makes this residual locally integral at every prime " +
                "coprime to n. source_denominator_obstruction and source_local_quotient " +
                "exclude all remaining denominator primes, completing ordinary integrality. " +
                "The existing source_divisible_of_integral then applies without an extra " +
                "premise. Applying triangular_exists_unique with lam(n)=mu(n)=n^2 identifies " +
                "the unique rational ordinary source, so this series has both arithmetic " +
                "properties. No factorial-rescaled coefficient convention or finite cutoff " +
                "is substituted, and the A300598 quotient is used only for n>=1.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("hannaa300591-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Q() => Seq(Mathbb, Grp(V("Q")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Series() => Call("PowerSeries", Q());
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) =>
        Seq(a, Sp, Le, Sp, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Iffn(Formula a, Formula b) =>
        Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a) => new Formula.Power(Par(a), D(2));
    private static Formula Cast(Formula a) => Par(Seq(a, Colon, Sp, Q()));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Unique(string name, Formula type, System.Func<Formula, Formula> property) =>
        Ex(name, type, And(property(V(name)),
            All("G", type, Imp(property(V("G")), Eqn(V("G"), V(name))))));
    private static Formula Coeff(Formula n, Formula f) => Call("coeff", n, f);
    private static Formula SourceBody(Formula f) =>
        And(Eqn(Call("constantCoeff", f), D(0)), All("n", N(),
            Imp(Leq(D(1), V("n")), Eqn(
                Coeff(V("n"), Call("expSeries", Pow(Cast(V("n"))), f)),
                Mul(Pow(Cast(V("n"))), Coeff(Sub(V("n"), D(1)),
                    Call("expSeries", Pow(Cast(V("n"))), f)))))));
    private static Formula TriangularBody()
    {
        var lam = new Formula.Apply(V("lam"), [V("n")]);
        var mu = new Formula.Apply(V("mu"), [V("n")]);
        var premise = All("n", N(), Imp(Leq(D(1), V("n")), Not(Eqn(lam, D(0)))));
        Formula Source(Formula f) => And(Eqn(Call("constantCoeff", f), D(0)),
            All("n", N(), Imp(Leq(D(1), V("n")), Eqn(
                Coeff(V("n"), Call("expSeries", lam, f)),
                Mul(mu, Coeff(Sub(V("n"), D(1)), Call("expSeries", lam, f)))))));
        return All("lam", Call("Function", N(), Q()),
            All("mu", Call("Function", N(), Q()),
                Imp(premise, Unique("F", Series(), f => Par(Source(f))))));
    }

    private static Formula Not(Formula a) => Seq(Neg, Par(a));
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Dvd(Formula a, Formula b) => Call("Dvd", a, b);
    private static Formula Integral(Formula a) =>
        Ex("z", Z(), Eqn(a, Cast(V("z"))));
    private static Formula Local(Formula p, Formula a) => Call("IsRIntegralRat", p, a);
    private static Formula PrefixIntegral() => All("j", N(),
        Imp(Lt(V("j"), V("n")), Integral(Coeff(V("j"), V("F")))));
    private static Formula PrefixLocal() => All("j", N(),
        Imp(Lt(V("j"), V("n")), Local(V("p"), Coeff(V("j"), V("F")))));
    private static Formula LocalQuotientBody()
    {
        var quotient = new Formula.Fraction(Coeff(V("n"), V("F")), Cast(V("n")));
        var conclusion = Imp(PrefixLocal(), Local(V("p"), quotient));
        var primes = All("p", N(), Imp(Call("Prime", V("p")),
            Imp(Dvd(V("p"), V("n")), conclusion)));
        var indices = All("n", N(), Imp(Leq(D(2), V("n")), primes));
        return All("F", Series(), Imp(Call("IsSource", V("F")), indices));
    }

    private static Formula ObstructionBody()
    {
        var prime = And(Call("Prime", V("p")), And(Lt(V("p"), V("n")),
            And(Not(Dvd(V("p"), V("n"))),
                Dvd(V("p"), Call("den", Coeff(V("n"), V("F")))))));
        var conclusion = And(Leq(D(2), V("n")), Ex("p", N(), prime));
        var indices = All("n", N(), Imp(PrefixIntegral(),
            Imp(Not(Integral(Coeff(V("n"), V("F")))), conclusion)));
        return All("F", Series(), Imp(Call("IsSource", V("F")), indices));
    }

    private static Formula DivisibilityBody()
    {
        var conclusion = Ex("q", Z(), Eqn(Coeff(V("n"), V("F")),
            Mul(Cast(V("n")), Cast(V("q")))));
        var indices = All("n", N(), Imp(Leq(D(1), V("n")), conclusion));
        var premise = All("r", N(), Integral(Coeff(V("r"), V("F"))));
        return All("F", Series(), Imp(Call("IsSource", V("F")), Imp(premise, indices)));
    }
}
