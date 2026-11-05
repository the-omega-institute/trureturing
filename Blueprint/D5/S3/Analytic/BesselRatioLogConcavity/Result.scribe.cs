using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.BesselRatioLogConcavity;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpvishnyakovazhang2025unimodality");
    private const string Prefix = "D5/S3/Analytic/BesselRatioLogConcavity/Result.";
    private const string Quotation = "Conjecture 1. Suppose b ≥ 0, ν1 ≥ ν2 > −1 and 0 < a1 ≤ a2. Then the ratio x → Iν1(a1 x)/Iν2(a2 x) is unimodal on (0, ∞). Moreover, if ν1 ≥ ν2 > 0 it is log-concave.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive rational series disproves log-concavity of a modified Bessel ratio.",
        H("A modified Bessel ratio need not be log-concave"), Blocks(
            Describe.Lean(DescribeId.Create("modified-bessel-series"),
                DeclarationHandle.Create(Prefix + "besselI"),
                H("The modified Bessel function of the first kind"),
                StatementSource.FromAuthor(Disp(BesselFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Printed page 11 of arXiv:2408.01755v2 states: “Using the standard power series expansion of Iν [28, p.217] we have”. The following is its displayed ratio expansion, quoted verbatim from the supplied text extraction with the line order and detached superscripts retained:")),
                    Paragraph(Text("“P∞ 2k 2k k")),
                    Paragraph(Text("Iν1 (a1 x)")),
                    Paragraph(Text("k=0 a1 x /[4 k!Γ(k + ν1 + 1)]")),
                    Paragraph(Text("2 ν1 −ν2")),
                    Paragraph(Text("P")),
                    Paragraph(Text(".")),
                    Paragraph(Text("= 2ν2 −ν2 aν11 a−ν")),
                    Paragraph(Text("x")),
                    Paragraph(Text("∞")),
                    Paragraph(Text("2")),
                    Paragraph(Text("2k 2k")),
                    Paragraph(Text("k")),
                    Paragraph(Text("Iν2 (a2 x)")),
                    Paragraph(Text("k=0 a2 x /[4 k!Γ(k + ν2 + 1)]”")),
                    Paragraph(Text("The extracted prefactor has detached superscripts; the normalization correspondence here is derived independently from the defining series, not asserted as a verbatim standalone formula in the paper. Factoring (a*x/2)^nu from each sum leaves terms a^(2k)*x^(2k)/(4^k*k!*Gamma(k+nu+1)); the ratio prefactor is 2^(nu2−nu1)*a1^nu1*a2^(−nu2)*x^(nu1−nu2). For equal orders the x powers cancel, and scales 1 and 2 leave 2^(−nu). The Lean definition uses the real series with the natural number 2k coerced to a real exponent. It is summable for z>0 and nu>−1."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bessel-log-concavity-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The positive-order log-concavity clause"),
                StatementSource.FromAuthor(Disp(Eqn(V("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjecture 1, printed page 12, with line breaks joined: “" + Quotation + "”")),
                    Paragraph(Text("The claim quantifies over all real orders nu1≥nu2>0 and all scales 0<a1≤a2. It states concavity on the entire positive real half-line of the logarithm of the standard modified Bessel ratio. Positivity of the series on this domain makes that the usual log-concavity assertion. The parameter b in the source does not occur in the ratio. Its unimodality clause is a separate assertion."))),
                DescribeRole.Definition),
            Helper("term_nonneg", "Nonnegative terms", TermNonneg(),
                "A nonnegative power divided by the positive factorial and rising factorial is nonnegative."),
            Helper("term_eq_coeff", "The coefficient correspondence", TermEqCoeff(),
                "Here term(nu,w,k)=w^k/(k!*(nu+1)_k). It equals the normalized coefficient of lower parameter nu+1 multiplied by w^k, so the coefficient recurrence and absolute convergence apply."),
            Helper("term_step", "The weighted recurrence", TermStep(),
                "Multiplying the coefficient recurrence by w^(k+1) gives this recurrence for the weighted term."),
            Helper("term_summable", "Convergence of the weighted series", TermSummable(),
                "The absolute convergence of the normalized coefficient series at lower parameter nu+1 supplies convergence for every real w."),
            Helper("bessel_term_eq", "Gamma normalization of a summand", BesselTermEq(),
                "The Gamma–Pochhammer identity and positive-base real-power identities separate the order-dependent normalization from each summand."),
            Helper("bessel_summable", "Convergence of the modified Bessel series", BesselSummable(),
                "After the summand identity, convergence follows by multiplying the normalized summable series by the fixed normalization factor."),
            Helper("bessel_eq", "The normalized modified Bessel series", BesselEq(),
                "Summing the summand identity pulls the normalization factor outside the infinite sum."),
            Helper("series_pos", "Positive certificate series", All("w", R,
                Imp(Nonneg(V("w")), Pos(Call("series", V("w"))))),
                "The function series(w) is the sum of term(1/10,w,k) over all natural k. Its constant term is one and all other terms are nonnegative."),
            Helper("term_cast", "Rational terms and real terms", All("w", Q, All("k", N,
                Eqn(Term(Qn(1,10), V("w"), V("k")), Call("qterm", V("w"), V("k"))))),
                "The rational recurrence qterm(w,0)=1 and qterm(w,k+1)=w/((k+1)*(11/10+k))*qterm(w,k) agrees with the real term. Rational arguments and values in this formula are coerced to real values where required."),
            Helper("series_lower", "The partial sum is a lower bound", All("w", Q,
                Imp(Nonneg(V("w")), Leq(Call("qlower", V("w")), Call("series", V("w"))))),
                "The rational number qlower(w) sums qterm(w,k) over 0<=k<60. Nonnegative remaining terms make this a lower bound; qlower and w are coerced to real values in the comparison."),
            Helper("tail_ratio", "A bound on the tail ratio", TailRatio(),
                "The rational number qratio(w) is w/(61*(611/10)). For k>=60 the recurrence denominator is at least 61*(611/10), giving the displayed comparison after coercion to real values."),
            Helper("series_upper", "The geometric upper bound", All("w", Q,
                Imp(Nonneg(V("w")), Imp(Less(Call("qratio", V("w")), D(1)),
                    Leq(Call("series", V("w")), Call("qupper", V("w")))))),
                "The rational number qupper(w) is qlower(w)+qterm(w,60)/(1−qratio(w)). A geometric majorant for the tail starting at index 60 bounds the real series by this rational value coerced to the reals."),
            Helper("bessel_ratio", "Cancellation of the common normalization", BesselRatio(),
                "The positive power and Gamma factors cancel in the ratio, leaving the common factor 2^(−nu) and a quotient of normalized series."),
            Helper("bessel_pos", "Positivity on the positive half-line", All("nu", R, All("z", R,
                Imp(OrderCondition(), Imp(Pos(V("z")), Pos(Call("besselI", V("nu"), V("z"))))))),
                "For positive argument and order greater than −1 every summand is positive; convergence and the term of index zero give a positive sum."),
            Helper("numeric_certificate", "Six exact rational bounds", NumericCertificate(),
                "All six comparisons are inequalities in the rationals, evaluated with the 60-term partial sums and the geometric upper bounds."),
            Helper("series_product", "The strict series-product comparison", SeriesProduct(),
                "The three lower bounds and three upper bounds imply the strict product comparison; every series factor used in multiplying the inequalities is positive."),
            Helper("witness", "The midpoint inequality is reversed", Witness(),
                "At order 1/10 the ratio at 9/2 squared is smaller than the product of the ratios at 3/2 and 15/2. Positivity permits logarithms, giving the failure of midpoint concavity."),
            Describe.Lean(DescribeId.Create("bessel-log-concavity-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("An exact infinite-series counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(V("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take equal orders nu1=nu2=1/10 and scales a1=1,a2=2. Write S(w)=∑ₖ₌₀∞ w^k/(k! (11/10)ₖ). The Gamma–Pochhammer identity gamma_pochhammer gives Iν(t)/Iν(2t)=2^(−ν) S(t²/4)/S(t²). Gamma factors cancel, and the positive real power factor is common to all three points.")),
                    Paragraph(Text("For a nonnegative rational w, let L(w) be the sum over 0≤k<60, let t60(w) be the term of index 60, and put rho(w)=w/(61·(611/10)). Every successive ratio starting at index 60 is at most rho(w). When rho(w)<1, the infinite series lies between L(w) and L(w)+t60(w)/(1−rho(w)). Exact rational arithmetic gives S(9/16)≥1.584, S(225/16)≥223.368 and S(81/4)≥894.574, while S(81/16)≤15.316, S(9/4)≤4.447 and S(225/4)≤264068.")),
                    Paragraph(Text("These bounds imply S(9/16)S(225/16)S(81/4)²>S(81/16)²S(9/4)S(225/4). Thus R(3/2)R(15/2)>R(9/2)² for R(t)=I₁⁄₁₀(t)/I₁⁄₁₀(2t). Taking logarithms contradicts concavity at the midpoint 9/2. This disproves the universal log-concavity clause; it leaves unimodality and the full parameter range of log-concavity unresolved."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("karp-vishnyakova-zhang-2025-bessel-ratio-log-concavity"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Helper(string name, string title, Formula statement, string text) =>
        Describe.Lean(DescribeId.Create("helper-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Theorem);
    private static Formula Q => Seq(Mathbb, Sp, Grp(V("Q")));
    private static Formula Qn(long a, long b) => Fr(new Formula.Number(a), new Formula.Number(b));
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Nonneg(Formula a) => Leq(D(0), a);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(V(name), Colon, Sp, type, Mapsto, Sp, body);
    private static Formula Tsum(Formula body) =>
        Seq(new Formula.Subscript(Seq(Sum, Sp, Apos), Seq(V("k"), Colon, Sp, N)), Sp, body);
    private static Formula Term(Formula nu, Formula w, Formula k) => Call("term", nu, w, k);
    private static Formula OrderCondition() => Less(new Formula.Negate(D(1)), V("nu"));
    private static Formula BesselTerm(Formula nu, Formula z, Formula k) =>
        Fr(Pow(Fr(z, D(2)), Add(Mul(D(2), k), nu)),
            Mul(Call("Nat.factorial", k), Call("Real.Gamma", Add(Add(k, nu), D(1)))));
    private static Formula Normalization() => Fr(Pow(Fr(V("z"), D(2)), V("nu")),
        Call("Real.Gamma", Add(V("nu"), D(1))));
    private static Formula TermNonneg() => All("nu", R, All("w", R,
        Imp(OrderCondition(), Imp(Nonneg(V("w")), All("k", N,
            Nonneg(Term(V("nu"), V("w"), V("k"))))))));
    private static Formula TermEqCoeff() => All("nu", R, All("w", R, All("k", N,
        Eqn(Term(V("nu"), V("w"), V("k")),
            Mul(Call("D5.S3.Analytic.BesselRedheffer.Series.coeff", Add(V("nu"), D(1)), V("k")),
                Pow(V("w"), V("k")))))));
    private static Formula TermStep() => All("nu", R, Imp(OrderCondition(),
        All("w", R, All("k", N,
            Eqn(Term(V("nu"), V("w"), Add(V("k"), D(1))),
                Mul(Fr(V("w"), Mul(Add(V("k"), D(1)), Add(Add(V("nu"), D(1)), V("k")))),
                    Term(V("nu"), V("w"), V("k"))))))));
    private static Formula TermSummable() => All("nu", R, Imp(OrderCondition(), All("w", R,
        Call("Summable", Lam("k", N, Term(V("nu"), V("w"), V("k")))))));
    private static Formula BesselTermEq() => All("nu", R, All("z", R,
        Imp(OrderCondition(), Imp(Pos(V("z")), All("k", N,
            Eqn(BesselTerm(V("nu"), V("z"), V("k")),
                Mul(Normalization(), Term(V("nu"), Fr(Pow(V("z"), D(2)), D(4)), V("k")))))))));
    private static Formula BesselSummable() => All("nu", R, All("z", R,
        Imp(OrderCondition(), Imp(Pos(V("z")),
            Call("Summable", Lam("k", N, BesselTerm(V("nu"), V("z"), V("k"))))))));
    private static Formula BesselEq() => All("nu", R, All("z", R,
        Imp(OrderCondition(), Imp(Pos(V("z")), Eqn(Call("besselI", V("nu"), V("z")),
            Mul(Normalization(), Tsum(Term(V("nu"), Fr(Pow(V("z"), D(2)), D(4)), V("k")))))))));
    private static Formula TailRatio() => All("w", Q, Imp(Nonneg(V("w")), All("k", N,
        Imp(Leq(new Formula.Number(60), V("k")),
            Leq(Term(Qn(1,10), V("w"), Add(V("k"), D(1))),
                Mul(Call("qratio", V("w")), Term(Qn(1,10), V("w"), V("k"))))))));
    private static Formula BesselRatio() => All("nu", R, All("t", R,
        Imp(OrderCondition(), Imp(Pos(V("t")),
            Eqn(Fr(Call("besselI", V("nu"), V("t")), Call("besselI", V("nu"), Mul(D(2), V("t")))),
                Mul(Pow(D(2), new Formula.Negate(V("nu"))),
                    Fr(Tsum(Term(V("nu"), Fr(Pow(V("t"), D(2)), D(4)), V("k"))),
                        Tsum(Term(V("nu"), Pow(V("t"), D(2)), V("k"))))))))));
    private static Formula NumericCertificate() =>
        And(Leq(Qn(1584,1000), Call("qlower", Qn(9,16))),
        And(Leq(Qn(223368,1000), Call("qlower", Qn(225,16))),
        And(Leq(Qn(894574,1000), Call("qlower", Qn(81,4))),
        And(Leq(Call("qupper", Qn(81,16)), Qn(15316,1000)),
        And(Leq(Call("qupper", Qn(9,4)), Qn(4447,1000)),
            Leq(Call("qupper", Qn(225,4)), new Formula.Number(264068)))))));
    private static Formula SeriesProduct() => Less(
        Mul(Mul(Pow(Call("series", Qn(81,16)), D(2)), Call("series", Qn(9,4))), Call("series", Qn(225,4))),
        Mul(Mul(Call("series", Qn(9,16)), Call("series", Qn(225,16))), Pow(Call("series", Qn(81,4)), D(2))));
    private static Formula WitnessRatio(long a, long b, long c) =>
        Fr(Call("besselI", Qn(1,10), Qn(a,b)), Call("besselI", Qn(1,10), new Formula.Number(c)));
    private static Formula Witness() => Less(Pow(WitnessRatio(9,2,9), D(2)),
        Mul(WitnessRatio(3,2,3), WitnessRatio(15,2,15)));

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula R => Seq(Mathbb, Sp, Grp(V("R")));
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var word in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(V(word));
        }
        return new Formula.Apply(Seq(Operatorname, Sp, Grp([.. parts])), [.. args]);
    }
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Leq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Pos(Formula value) =>
        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, value);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula BesselFormula()
    {
        var k = V("k");
        var exponent = Add(Mul(D(2), k), V("nu"));
        var summand = new Formula.Fraction(
            new Formula.Power(Parenthesized(new Formula.Fraction(V("z"), D(2))), exponent),
            Mul(Call("Nat.factorial", k), Call("Real.Gamma", Add(Add(k, V("nu")), D(1)))));
        var sum = Seq(new Formula.Subscript(Seq(Sum, Sp, Apos), Seq(k, Colon, Sp, N)), Sp, summand);
        return All("nu", R, All("z", R, Eqn(Call("besselI", V("nu"), V("z")), sum)));
    }
    private static Formula ClaimBody()
    {
        var x = V("x");
        var ratio = new Formula.Fraction(
            Call("besselI", V("nu1"), Mul(V("a1"), x)),
            Call("besselI", V("nu2"), Mul(V("a2"), x)));
        var function = Seq(x, Colon, Sp, R, Mapsto, Sp, Call("Real.log", ratio));
        var concave = Call("ConcaveOn", R, Call("Set.Ioi", D(0)), function);
        return All("nu1", R, All("nu2", R, All("a1", R, All("a2", R,
            Imp(Pos(V("nu2")), Imp(Leq(V("nu2"), V("nu1")),
                Imp(Pos(V("a1")), Imp(Leq(V("a1"), V("a2")), concave))))))));
    }
}
