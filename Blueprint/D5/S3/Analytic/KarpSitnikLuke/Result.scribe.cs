using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpSitnikLuke;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpsitnik2009luke");
    private const string Prefix = "D5/S3/Analytic/KarpSitnikLuke/Result.";
    private const string TheoremThree = "For bₖ > aₖ > 0, k = 1, . . . , q, x > −1 and σ ≥ 1 the inequality 1/(1 + x ∏ᵢ₌₁ᵠ (aᵢ/bᵢ))^σ < _{q+1}F_q(σ, (a_q); (b_q); −x) holds true.";
    private const string ConjectureOne = "Theorem 3 is true for all σ > 0 and ∑ᵢ₌₁ᵠ (bᵢ − aᵢ) > 0.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A convergent hypergeometric series contradicts the sum-condition Luke lower bound.",
        H("A counterexample to the sum-condition lower bound"), Blocks(
            Describe.Lean(DescribeId.Create("luke-hypergeometric-summand"),
                DeclarationHandle.Create(Prefix + "hyperTerm"), H("The generalized hypergeometric summand"),
                StatementSource.FromAuthor(Disp(Parameters(Scalars("z", All("n", N,
                    Eqn(Term(V("sigma"), V("a"), V("b"), V("z"), V("n")),
                        Mul(Fr(Mul(Poch(V("n"), V("sigma")),
                            Call("D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult.pochRatio", V("a"), V("b"), V("n"))),
                            Call("Nat.factorial", V("n"))), Pow(V("z"), V("n"))))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Equation (1), printed page 1 of arXiv:math/0703084v2, defines the generalized hypergeometric series by the product of upper rising factorials divided by the product of lower rising factorials and n!, multiplied by z^n. The upper list here is sigma followed by a, and the lower list is b. The existing pochRatio is precisely the quotient of the products for a and b. Mathlib's (ascPochhammer R n).eval t equals the source's (t)n=t(t+1)...(t+n−1), with value one at n=0. Thus hyperTerm is the source's summand, with no Gamma normalization factor."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("luke-hypergeometric-value"),
                DeclarationHandle.Create(Prefix + "hyper"), H("The power-series value"),
                StatementSource.FromAuthor(Disp(Parameters(Scalars("z",
                    Eqn(Hyper(V("sigma"), V("a"), V("b"), V("z")),
                        Tsum("n", Term(V("sigma"), V("a"), V("b"), V("z"), V("n")))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The real tsum interprets equation (1) inside its convergence disk. Printed page 1 states: “The series converges for |z| < 1 and can be analytically continued onto the entire complex plane cut along [1, ∞].” Summability is an explicit assumption of the assertion below, and is proved for the counterexample."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("luke-sum-condition-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The sum-condition assertion inside the disk"),
                StatementSource.FromAuthor(Disp(Eqn(V("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Theorem 3, printed page 6, equation (23), with the displayed formula joined to its sentence: “" + TheoremThree + "”")),
                    Paragraph(Text("Conjecture 1, printed page 14: “" + ConjectureOne + "”")),
                    Paragraph(Text("All a and b entries are positive; the conjecture replaces the componentwise inequalities by positivity of the sum of b−a. The assertion is restricted to −1<x<1, the power-series disk at z=−x, and assumes summability and a positive real-power base. These restrictions give a weaker assertion than the paper's x>−1 assertion via analytic continuation. Refuting this weaker assertion therefore refutes the paper's Conjecture 1. For q=0 the positive-sum assumption is impossible; including it adds no cases. Real powers use Real.rpow."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("luke-witness-magnitudes"),
                DeclarationHandle.Create(Prefix + "u"), H("Positive magnitudes of the witness summands"),
                StatementSource.FromAuthor(Disp(All("n", N, Eqn(U(V("n")),
                    Mul(Fr(Call("Nat.factorial", V("n")),
                        Mul(Poch(V("n"), Qn(1,10)), Add(V("n"), D(1)))), Pow(Qn(1,10), V("n"))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The magnitudes are n!/((1/10)n(n+1)) times (1/10)^n. Natural indices in real expressions are coerced to real numbers."))), DescribeRole.Definition),
            Helper("u_nonneg", "Nonnegative magnitudes", All("n", N, Leq(D(0), U(V("n")))),
                "The rising factorial at 1/10 and the factorial are positive, and the power is nonnegative."),
            Helper("u_step", "The exact successive-term ratio", All("n", N,
                Eqn(U(Add(V("n"), D(1))), Mul(Fr(Pow(Add(V("n"), D(1)), D(2)),
                    Mul(Mul(D(1,0), Add(V("n"), Qn(1,10))), Add(V("n"), D(2)))), U(V("n"))))),
                "The factorial and rising-factorial recurrences give u(n+1)/u(n)=(n+1)^2/(10(n+1/10)(n+2))."),
            Helper("u_half", "A uniform geometric comparison", All("n", N,
                Leq(U(Add(V("n"), D(1))), Mul(Qn(1,2), U(V("n"))))),
                "For every natural n the ratio is at most one half: the denominator comparison reduces to 4n^2+(17/2)n≥0. In particular the magnitudes decrease from the first term onward."),
            Helper("u_summable", "Absolute convergence of the magnitudes", Call("Summable", V("u")),
                "The ratio bound one half implies summability by the geometric comparison test."),
            Helper("term_eq", "The exact witness summands", All("n", N,
                Eqn(WitnessTerm(V("n")), Mul(Pow(new Formula.Negate(D(1)), V("n")), U(V("n"))))),
                "At q=2, sigma=1, a=(1,1), b=(1/10,2) and z=−1/10, the identities (1)n=n! and (2)n=(n+1)! cancel the factorial weights. The resulting term is (−1)^n u(n)."),
            Helper("witness_summable", "Convergence at the counterexample", Call("Summable",
                Lam("n", N, WitnessTerm(V("n")))),
                "The exact summand identity and summability of the magnitudes imply convergence of the alternating hypergeometric series."),
            Helper("witness_upper", "The hypergeometric value is below two thirds",
                Less(WitnessHyper(), Qn(2,3)),
                "The antitone alternating-series upper bound uses indices zero, one and two: 1−1/2+2/33=37/66<2/3. Summability identifies the limit with the real tsum."),
            Describe.Lean(DescribeId.Create("luke-sum-condition-refutation"),
                DeclarationHandle.Create(Prefix + "result"), H("Refutation of the conjectured extension"),
                StatementSource.FromAuthor(Disp(new Formula.Not(V("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take q=2, sigma=1, a=(1,1), b=(1/10,2), x=1/10. The parameters are positive, the sum of b−a is 1/10, and the product of a/b is 5. The real-power base is 3/2, so the proposed lower bound is 2/3. The convergent series value is at most 37/66, contradicting the strict lower-bound assertion. This counterexample uses sigma=1 and violates the componentwise condition b1>a1. It does not contradict Theorem 3 under that theorem's original hypotheses, and does not address the componentwise case 0<sigma<1 or Conjecture 2."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("karp-sitnik-2009-luke-lower-bound"), ResolutionKind.Refuted)))));

    private static DocumentBlock Helper(string name, string title, Formula statement, string text) =>
        Describe.Lean(DescribeId.Create("luke-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula R => Seq(Mathbb, Sp, Grp(V("R")));
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
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
    private static Formula Qn(long a, long b) => Fr(new Formula.Number(a), new Formula.Number(b));
    private static Formula Fr(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a),b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan,b);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal,b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name),type,body);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a),FormulaLogicOperator.Implies,Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(V(name), Colon, Sp, type, Mapsto, Sp, body);
    private static Formula Tsum(string name, Formula body) =>
        Seq(new Formula.Subscript(Seq(Sum, Sp, Apos), Seq(V(name), Colon, Sp, N)), Sp, body);
    private static Formula Finite(string name, Formula symbol, Formula body) =>
        Seq(new Formula.Subscript(symbol, Seq(V(name), Colon, Sp, Call("Fin", V("q")))), Sp, body);
    private static Formula Parameters(Formula body) => All("q",N,
        All("a",new Formula.TypeArrow(Call("Fin",V("q")),R),
        All("b",new Formula.TypeArrow(Call("Fin",V("q")),R),body)));
    private static Formula Scalars(string name, Formula body) => All("sigma", R, All(name,R,body));
    private static Formula Poch(Formula n, Formula t) =>
        Call("Polynomial.eval", t, Call("ascPochhammer", R, n));
    private static Formula Term(Formula sigma, Formula a, Formula b, Formula z, Formula n) =>
        Call("hyperTerm",sigma,a,b,z,n);
    private static Formula Hyper(Formula sigma, Formula a, Formula b, Formula z) => Call("hyper",sigma,a,b,z);
    private static Formula U(Formula n) => Call("u",n);
    private static Formula A => Call("Function.const",Call("Fin",D(2)),D(1));
    private static Formula B => Seq(Bang, OpenBracket, Qn(1,10), Comma, Sp, D(2), CloseBracket);
    private static Formula WitnessTerm(Formula n) => Term(D(1),A,B,new Formula.Negate(Qn(1,10)),n);
    private static Formula WitnessHyper() => Hyper(D(1),A,B,new Formula.Negate(Qn(1,10)));
    private static Formula ClaimBody()
    {
        var i = V("i");
        var a = new Formula.Apply(V("a"), [i]);
        var b = new Formula.Apply(V("b"), [i]);
        var product = Finite("i", Prod, Fr(a,b));
        var sum = Finite("i", Sum, Parenthesized(Sub(b,a)));
        var basis = Add(D(1),Mul(V("x"), Parenthesized(product)));
        var summable = Call("Summable", Lam("n",N,
            Term(V("sigma"),V("a"),V("b"),new Formula.Negate(V("x")),V("n"))));
        var conclusion = Less(Fr(D(1),Pow(basis,V("sigma"))),
            Hyper(V("sigma"),V("a"),V("b"),new Formula.Negate(V("x"))));
        return Parameters(Scalars("x",
            Imp(All("i",Call("Fin",V("q")),Less(D(0),a)),
            Imp(All("i",Call("Fin",V("q")),Less(D(0),b)),
            Imp(Less(D(0),sum), Imp(Less(D(0),V("sigma")),
            Imp(Less(new Formula.Negate(D(1)),V("x")), Imp(Less(V("x"),D(1)),
            Imp(Less(D(0),basis), Imp(summable,conclusion))))))))));
    }
}
