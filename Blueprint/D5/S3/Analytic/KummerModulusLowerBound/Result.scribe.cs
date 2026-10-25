using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KummerModulusLowerBound;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Asymptotics/garrappagerholdpopoliziosimon2025mittagleffler");
    private const string Prefix = "D5/S3/Analytic/KummerModulusLowerBound/Result.";
    private const string Question = "In view of the preceding result and Remark 2, one may ask if for all α, β > 0 one has |M(α, α−β, z)| ≥ M(α, α−β, ℜz), z ∈ ℂ. (2.4) … In particular, (2.4) holds globally for α > 1 ≥ β > 0 … The question whether (2.4) holds globally for all α, β > 0 seems to be still open.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact nonreal zero contradicts the universal Kummer modulus lower bound.",
        H("A quadratic Kummer counterexample"), Blocks(
            Describe.Lean(DescribeId.Create("kummer-complex-series"), DeclarationHandle.Create(Prefix + "kummerC"), H("The complex Kummer series"),
                StatementSource.FromAuthor(Disp(All("a", R, All("b", R, All("z", C,
                    Eqn(K(V("a"), V("b"), V("z")), Tsum("n", Mul(Cast(Coeff(V("a"), V("b"), V("n")), C), Pow(V("z"), V("n")))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Remark 2(a) identifies M as \"a Kummer confluent hypergeometric function\": M(a, b, z) = Σ_{n≥0} (a)_n z^n / ((b)_n n!), b ∉ {0, −1, −2, …}. The locator is Remark 2(a) of arXiv:2410.11852v4; the supplied extract does not specify a verified page number. The existing KummerRatio.Defs.kummerCoeff is (a)n/((b)n n!), where (a)n is (ascPochhammer R n).eval a. The complex summands cast these same real coefficients into C. No normalization changes."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kummer-modulus-claim"), DeclarationHandle.Create(Prefix + "claim"), H("The universal modulus assertion"),
                StatementSource.FromAuthor(Disp(Eqn(V("claim"), ClaimBody()))), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Remark 6 of arXiv:2410.11852v4: “" + Question + "” The supplied locator specifies the remark, without a verified page number. Alpha and beta are real and positive; alpha−beta is not a nonpositive integer. The real side is exactly KummerRatio.Defs.kummer alpha (alpha−beta) z.re, and the complex norm is the ordinary complex modulus. The pole exclusion is already part of the definition of M in Remark 2(a)."))), DescribeRole.Definition),
            Helper("half_ne_nat", "The second parameter avoids poles", All("n", N, Ne(Qn(-3,2), Neg(Cast(V("n"), R)))),
                "The number 3/2 lies strictly between the natural numbers 1 and 2. Thus −3/2 is never a nonpositive integer; result uses this for alpha=1/2 and beta=2."),
            Helper("coeff_eq", "The exact polynomial coefficient", All("n", N,
                Eqn(Coeff(Qn(1,2), Qn(-3,2), V("n")), Fr(Weight(Cast(V("n"), R)), Fac(V("n"))))),
                "Write P_n(x)=(x)_n. Evaluate Mathlib ascPochhammer_mul at −3/2 with lengths (n, 2) and (2, n). The common value P_{n+2}(−3/2) gives P_n(−3/2)(n−3/2)(n−1/2)=(3/4)P_n(1/2). Rational normalization gives (1/2)n=(1−4n/3+4n(n−1)/3)(−3/2)n. The denominator is nonzero because its only possible roots are nonpositive integers. Dividing by the factorial gives the coefficient used by complex_closed."),
            Helper("second_exp_hasSum", "The second factorial moment of the exponential series", All("z", C,
                Call("HasSum", Lam("n", N, Fr(Mul(Mul(Cast(V("n"), C), Sub(Cast(V("n"), C), D(1))), Pow(V("z"), V("n"))), Fac(V("n")))),
                    Mul(Pow(V("z"), D(2)), Call("Complex.exp", V("z"))))),
                "A shift by one reduces the second factorial moment to ResolvedCountWeakValue.weighted_exp_hasSum, the first weighted exponential series. This supplies the quadratic term in complex_closed."),
            Helper("complex_closed", "The complex closed form", All("z", C,
                Eqn(K(Qn(1,2), Qn(-3,2), V("z")), Mul(Call("Complex.exp", V("z")), Quadratic(V("z"))))),
                "Combine the exponential series, its first factorial moment and its second factorial moment with coefficients 1, −4/3 and 4/3. The exact coefficient identity identifies their sum with the complex Kummer series. The identity is used both at the nonreal zero and at real arguments."),
            Helper("real_closed", "The real closed form", All("x", R,
                Eqn(RealK(Qn(1,2), Qn(-3,2), V("x")), Mul(Call("Real.exp", V("x")), Quadratic(V("x"))))),
                "The real embedding commutes with the infinite sum, powers and exponential. Applying injectivity of that embedding to complex_closed yields the real identity; witness_pos uses it at x=1/2."),
            Helper("witness_zero", "An exact nonreal zero", Eqn(K(Qn(1,2), Qn(-3,2), ZeroPoint()), D(0)),
                "At z=1/2+(sqrt 2/2)i, the quadratic 1−4z/3+4z²/3 vanishes exactly, since (sqrt 2)²=2. Therefore the complex series has norm zero."),
            Helper("witness_pos", "The positive real-axis value", Less(D(0), RealK(Qn(1,2), Qn(-3,2), Qn(1,2))),
                "At x=1/2, the quadratic is 2/3. Hence the real series is (2/3)exp(1/2)>0, contradicting the proposed bound at the complex zero."),
            Describe.Lean(DescribeId.Create("kummer-modulus-refutation"), DeclarationHandle.Create(Prefix + "result"), H("A negative answer to the universal question"),
                StatementSource.FromAuthor(Disp(new Formula.Not(V("claim")))), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take alpha=1/2, beta=2 and z=1/2+(sqrt 2/2)i. Both parameters are positive, and alpha−beta=−3/2 avoids every excluded pole. The real-axis value is strictly positive, while the complex norm is zero. Thus the universal assertion in Remark 6 is false. The paper's range alpha>1≥beta>0 is not contradicted. A classification of all parameter pairs satisfying the modulus inequality remains outside this conclusion."))), DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(ProblemSlugRef.Create("garrappa-gerhold-popolizio-simon-2025-kummer-modulus"), ResolutionKind.Refuted)))));

    private static DocumentBlock Helper(string name, string title, Formula statement, string text) =>
        Describe.Lean(DescribeId.Create("kummer-modulus-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula R => Seq(Mathbb, Sp, Grp(V("R")));
    private static Formula C => Seq(Mathbb, Sp, Grp(V("C")));
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var word in name.Split('.')) { if (parts.Count > 0) parts.Add(Dot); parts.Add(V(word)); }
        return new Formula.Apply(Seq(Operatorname, Sp, Grp([.. parts])), [.. args]);
    }
    private static Formula Qn(long a, long b) => Fr(a < 0 ? Neg(new Formula.Number(-a)) : new Formula.Number(a), new Formula.Number(b));
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Neg(Formula a) => new Formula.Negate(a);
    private static Formula Cast(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
    private static Formula Lam(string n, Formula t, Formula body) => Seq(V(n), Colon, Sp, t, Mapsto, Sp, body);
    private static Formula Tsum(string n, Formula body) => Seq(new Formula.Subscript(Seq(Sum, Sp, Apos), Seq(V(n), Colon, Sp, N)), Sp, body);
    private static Formula Fac(Formula n) => Call("Nat.factorial", n);
    private static Formula Coeff(Formula a, Formula b, Formula n) => Call("D5.S3.Analytic.KummerRatio.Defs.kummerCoeff", a, b, n);
    private static Formula RealK(Formula a, Formula b, Formula x) => Call("D5.S3.Analytic.KummerRatio.Defs.kummer", a, b, x);
    private static Formula K(Formula a, Formula b, Formula z) => Call("kummerC", a, b, z);
    private static Formula Weight(Formula n) => Add(Sub(D(1), Mul(Qn(4,3), n)), Mul(Mul(Qn(4,3), n), Sub(n, D(1))));
    private static Formula Quadratic(Formula z) => Add(Sub(D(1), Fr(Mul(D(4), z), D(3))), Fr(Mul(D(4), Pow(z, D(2))), D(3)));
    private static Formula ZeroPoint() => Add(Cast(Qn(1,2), C), Mul(Cast(Fr(Call("Real.sqrt", D(2)), D(2)), C), Call("Complex.I")));
    private static Formula ClaimBody() => All("alpha", R, All("beta", R,
        Imp(Less(D(0), V("alpha")), Imp(Less(D(0), V("beta")),
        Imp(All("n", N, Ne(Sub(V("alpha"), V("beta")), Neg(Cast(V("n"), R)))), All("z", C,
            Leq(RealK(V("alpha"), Sub(V("alpha"), V("beta")), Call("Complex.re", V("z"))),
                Call("norm", K(V("alpha"), Sub(V("alpha"), V("beta")), V("z"))))))))));
}
