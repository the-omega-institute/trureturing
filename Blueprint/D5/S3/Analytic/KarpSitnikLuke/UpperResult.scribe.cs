using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpSitnikLuke;

internal sealed class UpperResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpsitnik2009luke");
    private const string Prefix = "D5/S3/Analytic/KarpSitnikLuke/UpperResult.";
    private const string ConjectureTwo = "For 0 < σ ≤ min(a₁, a₂, . . . , a_q), ∑ᵢ₌₁ᵠ (bᵢ − aᵢ) > 0 and x > 0: _{q+1}F_q(σ, (a_q); (b_q); −x) < 1/[1 + x ∏ᵢ₌₁ᵠ Γ(aᵢ)Γ(bᵢ−σ)/(Γ(bᵢ)Γ(aᵢ−σ))]^σ. (38)";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An alternating lower bracket contradicts the sum-condition Luke upper bound.",
        H("A counterexample to the sum-condition upper bound"), Blocks(
            Describe.Lean(DescribeId.Create("luke-upper-gamma-product"),
                DeclarationHandle.Create(Prefix + "gammaProduct"), H("The Gamma product"),
                StatementSource.FromAuthor(Disp(Parameters(All("sigma", R,
                    Eqn(K(V("sigma"),V("a"),V("b")), GammaBody()))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjecture 2, printed page 14 of arXiv:math/0703084v2, equation (38), uses the product of Gamma(a_i)Gamma(b_i−sigma)/(Gamma(b_i)Gamma(a_i−sigma)). Gamma is Mathlib's real Gamma function, and the finite product has indices in Fin q."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("luke-upper-sum-condition-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The conjectured upper bound inside the disk"),
                StatementSource.FromAuthor(Disp(Eqn(V("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Conjecture 2, printed page 14, in linear notation: “" + ConjectureTwo + "”")),
                    Paragraph(Text("The preceding sentence reads verbatim: “The asymptotic formula (16) and numerical experiments suggest the following”. Formula (16), printed page 5, with its preceding condition: “It follows that for σ < min(a₁, a₂, . . . , a_q) we will have”")),
                    Paragraph(Text("Formula (16): “_{q+1}F_q(σ, (a_q); (b_q); −z) = Γ[(a_q)−σ, (b_q) / (a_q), (b_q)−σ] z^{−σ} + o(z^{−σ}), z → ∞.”")),
                    Paragraph(Text("The extracted layout places a sigma next to the Gamma product. Separately, Gamma of parameter lists in (16) denotes the product quotient, so the asymptotic coefficient is the reciprocal of gammaProduct. The asymptotically precise reading is 1/(1+x K^(1/sigma))^sigma, with K=gammaProduct: the inner exponent 1/sigma makes its leading coefficient agree with (16). The counterexample has sigma=1, where this reading and the quoted display without that inner exponent coincide.")),
                    Paragraph(Text("The existing Result.hyperTerm and Result.hyper encode equation (1): (sigma)n times the product of (a_i)n/(b_i)n, divided by n!, times z^n, and its real infinite sum. They use the existing TwoBlockResult.pochRatio and Mathlib's rising factorial, so the upper-bound assertion refers to the same function as the lower-bound assertion.")),
                    Paragraph(Text("All a and b entries are positive, their denominator-minus-numerator sum is positive, and 0<sigma≤a_i for every i. Each additional hypothesis weakens the paper's universal assertion: x<1 restricts the domain to the power-series disk, summability restricts to convergent defining series, and gammaProduct>0 restricts the parameter set. With x>0 and gammaProduct>0 the base of the outer real power is positive. Refuting this weaker assertion refutes Conjecture 2. For q=0 the positive-sum assumption is impossible. Powers are Real.rpow."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("luke-upper-witness-magnitudes"),
                DeclarationHandle.Create(Prefix + "u"), H("Magnitudes of the witness terms"),
                StatementSource.FromAuthor(Disp(All("n", N, Eqn(U(V("n")),
                    Mul(Call("D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockResult.pochRatio", A, B, V("n")),
                        Pow(Qn(1,2),V("n"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a=(2,2) and b=(3/2,3), u(n)=(2)n²/((3/2)n(3)n) times (1/2)^n. These are the magnitudes at z=−1/2 and sigma=1. Natural indices in real expressions are coerced to real numbers."))), DescribeRole.Definition),
            Helper("u_nonneg", "Nonnegative magnitudes", All("n", N, Leq(D(0),U(V("n")))),
                "All rising factorials in the ratio are positive and the power is nonnegative."),
            Helper("u_step", "The exact successive-term ratio", All("n", N,
                Eqn(U(Add(V("n"),D(1))),Mul(Fr(Pow(Add(V("n"),D(2)),D(2)),
                    Mul(Mul(D(2),Add(V("n"),Qn(3,2))),Add(V("n"),D(3)))),U(V("n"))))),
                "The rising-factorial recurrence gives the multiplier (n+2)²/(2(n+3/2)(n+3))."),
            Helper("u_half", "A uniform ratio bound", All("n",N,
                Leq(U(Add(V("n"),D(1))),Mul(Qn(1,2),U(V("n"))))),
                "The inequality (n+2)²≤(n+3/2)(n+3) holds for every natural n, since their difference is (n+1)/2. Thus the successive magnitudes decrease by at least a factor of one half."),
            Helper("u_summable", "Summable magnitudes", Call("Summable",V("u")),
                "The uniform ratio bound implies summability by geometric comparison."),
            Helper("term_eq", "The exact alternating summands", All("n",N,
                Eqn(WitnessTerm(V("n")),Mul(Pow(new Formula.Negate(D(1)),V("n")),U(V("n"))))),
                "The identity (1)n=n! cancels the factorial in hyperTerm at sigma=1. The remaining term is (−1)^n u(n)."),
            Helper("witness_summable", "Convergence at the counterexample", Call("Summable",Lam("n",N,WitnessTerm(V("n")))),
                "Summability of u and the exact summand identity prove convergence of the hypergeometric series at −1/2."),
            Helper("witness_lower", "The value exceeds two thirds", Less(Qn(2,3),WitnessHyper()),
                "The six-term alternating lower bracket is 1−4/9+1/5−16/175+8/189−32/1617=249826/363825>2/3. The antitone alternating-series theorem compares this bracket with the real infinite sum."),
            Helper("witness_gamma", "The Gamma product equals one", Eqn(K(D(1),A,B),D(1)),
                "Gamma(2)=Gamma(1)=1, Gamma(3)=2 and Gamma(3/2)=(1/2)Gamma(1/2). Positivity of Gamma(1/2) permits cancellation. The two factors are 2 and 1/2, whose product is one."),
            Describe.Lean(DescribeId.Create("luke-upper-sum-condition-refutation"),
                DeclarationHandle.Create(Prefix + "result"), H("Refutation of the upper bound"),
                StatementSource.FromAuthor(Disp(new Formula.Not(V("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take q=2, sigma=1, a=(2,2), b=(3/2,3), x=1/2. All parameters are positive, the sum of b−a is 1/2, and sigma≤a_i. The defining series converges. The Gamma product is one and the proposed upper expression is 2/3, whereas the function exceeds 2/3. This refutes the sum-condition extension. It leaves the componentwise case b_k>a_k open."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("karp-sitnik-2009-luke-upper-bound"),ResolutionKind.Refuted)))));

    private static DocumentBlock Helper(string name, string title, Formula statement, string text) =>
        Describe.Lean(DescribeId.Create("luke-upper-" + name.Replace('_', '-')),
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
    private static Formula Finite(string name, Formula symbol, Formula body) =>
        Seq(new Formula.Subscript(symbol, Seq(V(name), Colon, Sp, Call("Fin", V("q")))), Sp, body);
    private static Formula Parameters(Formula body) => All("q",N,
        All("a",new Formula.TypeArrow(Call("Fin",V("q")),R),
        All("b",new Formula.TypeArrow(Call("Fin",V("q")),R),body)));
    private static Formula Scalars(string name, Formula body) => All("sigma", R, All(name,R,body));
    private static Formula Term(Formula sigma, Formula a, Formula b, Formula z, Formula n) =>
        Call("hyperTerm",sigma,a,b,z,n);
    private static Formula Hyper(Formula sigma, Formula a, Formula b, Formula z) => Call("hyper",sigma,a,b,z);
    private static Formula U(Formula n) => Call("u",n);
    private static Formula A => Call("Function.const",Call("Fin",D(2)),D(2));
    private static Formula B => Seq(Bang, OpenBracket, Qn(3,2), Comma, Sp, D(3), CloseBracket);
    private static Formula WitnessTerm(Formula n) => Term(D(1),A,B,new Formula.Negate(Qn(1,2)),n);
    private static Formula WitnessHyper() => Hyper(D(1),A,B,new Formula.Negate(Qn(1,2)));
    private static Formula K(Formula sigma, Formula a, Formula b) => Call("gammaProduct",sigma,a,b);
    private static Formula Gamma(Formula t) => Call("Real.Gamma",t);
    private static Formula GammaBody()
    {
        var a = new Formula.Apply(V("a"),[V("i")]);
        var b = new Formula.Apply(V("b"),[V("i")]);
        return Finite("i",Prod,Fr(Mul(Gamma(a),Gamma(Sub(b,V("sigma")))),
            Mul(Gamma(b),Gamma(Sub(a,V("sigma"))))));
    }
    private static Formula ClaimBody()
    {
        var i = V("i");
        var a = new Formula.Apply(V("a"),[i]);
        var b = new Formula.Apply(V("b"),[i]);
        var sum = Finite("i",Sum,Parenthesized(Sub(b,a)));
        var k = K(V("sigma"),V("a"),V("b"));
        var basis = Add(D(1),Mul(V("x"),Pow(k,Fr(D(1),V("sigma")))));
        var summable = Call("Summable",Lam("n",N,
            Term(V("sigma"),V("a"),V("b"),new Formula.Negate(V("x")),V("n"))));
        var conclusion = Less(Hyper(V("sigma"),V("a"),V("b"),new Formula.Negate(V("x"))),
            Fr(D(1),Pow(basis,V("sigma"))));
        return Parameters(Scalars("x",
            Imp(All("i",Call("Fin",V("q")),Less(D(0),a)),
            Imp(All("i",Call("Fin",V("q")),Less(D(0),b)),
            Imp(Less(D(0),sum),Imp(Less(D(0),V("sigma")),
            Imp(All("i",Call("Fin",V("q")),Leq(V("sigma"),a)),
            Imp(Less(D(0),V("x")),Imp(Less(V("x"),D(1)),
            Imp(summable,Imp(Less(D(0),k),conclusion)))))))))));
    }
}
