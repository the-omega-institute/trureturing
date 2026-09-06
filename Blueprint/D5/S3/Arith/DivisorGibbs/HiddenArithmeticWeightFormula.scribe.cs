using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DivisorGibbs;

internal sealed class HiddenArithmeticWeightFormulaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/DivisorGibbs/HiddenArithmeticWeightFormula.";
    private static Formula N => F.Id("n");
    private static Formula J => F.Id("J");
    private static Formula T => F.Id("T");
    private static Formula S => F.Id("s");
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula Dv => F.Id("d");
    private static Formula JT => Mul(J, T);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual coprime divisor Gibbs laws identify the hidden log partition through the "
            + "conditional entropy of the observer-first graph and the full-law hidden log moment.",
        H("Hidden Arithmetic Weight"),
        Blocks(
            Paragraph(Text(
                "All natural-number carriers below live in Type 0. Div(n) is the subtype of "
                    + "Nat.divisors n, and v(d) denotes its underlying natural value, embedded "
                    + "in the reals in powers and logarithms. Every logarithm is natural. "
                    + "The symbols w, Z and m denote weight, partition and mass. P(f,p) denotes "
                    + "the finite pushforward of p along f; H and C denote shannonEntropy and "
                    + "conditionalEntropy. In C the first coordinate is the conditioning observer. "
                    + "Each pair statement quantifies over positive natural J and T with gcd(J,T)=1. "
                    + "The symbols e, q and r denote mulEquiv, qJ and qT for exactly these "
                    + "hypotheses. The parameter s ranges independently over all real numbers.")),
            Claim("Div", "actual-divisors", "Actual divisor carrier",
                Quant(N, Naturals(), Equal(Div(N), Seq(OpenBrace, Dv, Sp, InMacro, Sp,
                    Naturals(), Sp, Mid, Sp, Dv, Sp, InMacro, Sp, Call("divisors", N), CloseBrace))),
                "The carrier contains precisely the natural divisors in Nat.divisors n. "
                    + "The zero integer has the library's empty divisor carrier.", true),
            Claim("weight", "weight", "Real power weight",
                Quant(N, Naturals(), Quant(S, Reals(), Quant(Dv, Div(N),
                    Equal(W(S, Dv), new Formula.Power(V(Dv), Seq(Minus, S)))))),
                "The weight is defined directly from the actual divisor value, independently of entropy.", true),
            Claim("partition", "partition", "Finite partition",
                Quant(N, Naturals(), Quant(S, Reals(), Equal(Z(N), SumOver(Dv, Div(N), W(S, Dv))))),
                "Z(n,s) is a finite sum over the actual divisor subtype.", true),
            Claim("mass", "mass", "Normalized weight",
                Quant(N, Naturals(), Quant(S, Reals(), Quant(Dv, Div(N),
                    Equal(M(N, Dv), new Formula.Fraction(W(S, Dv), Z(N)))))),
                "This definition uses total real division. Positivity and normalization for positive n "
                    + "are proved below and are not assumptions in the definition.", true),
            Claim("mulEquiv", "multiplication-equivalence", "Actual multiplication equivalence",
                PairScope(Seq(F.Id("e"), Sp, Colon, Sp,
                    Call("Equiv", Seq(Div(J), Sp, Times, Sp, Div(T)), Div(JT))), false),
                "The forward function sends (a,b) to the divisor with value v(a)v(b). "
                    + "Equiv.ofBijective supplies its inverse after coprime injectivity and "
                    + "the actual divisor-image identity prove bijectivity.", true),
            Claim("qJ", "observed-divisor", "Observed inverse coordinate",
                PairScope(Quant(Dv, Div(JT), Equal(Q(Dv),
                    Call("fst", CallInverse(Dv)))), false),
                "q(d) is the first coordinate of e inverse applied to the full divisor d.", true),
            Claim("qT", "hidden-divisor", "Hidden inverse coordinate",
                PairScope(Quant(Dv, Div(JT), Equal(R(Dv),
                    Call("snd", CallInverse(Dv)))), false),
                "r(d) is the second coordinate of e inverse applied to the full divisor d.", true),
            Claim("divisor_mul_equiv_val", "value-law", "Multiplication value law",
                PairScope(Factors(Equal(V(Call("e", Pair(A, B))), Mul(V(A), V(B)))), false),
                "The equivalence's forward value is actual natural multiplication."),
            Claim("divisor_split_unique", "unique-splitting", "Unique divisor splitting",
                PairScope(Quant(Dv, Div(JT), Seq(Exists, Bang, Sp, F.Id("u"), Sp, InMacro,
                    Sp, Div(J), Sp, Times, Sp, Div(T), Comma, Sp,
                    Equal(Mul(V(Call("fst", F.Id("u"))), V(Call("snd", F.Id("u")))), V(Dv)))), false),
                "Each full divisor has a unique factor pair. Coprimality supplies injectivity "
                    + "separately from the finset image theorem that supplies surjectivity."),
            Claim("partition_pos", "positive-partition", "Positive partition at every real exponent",
                SingleScope(Seq(D(0), Sp, Lt, Sp, Z(N))),
                "Every divisor weight is positive and divisor one witnesses a nonempty sum."),
            Claim("partition_mul", "partition-product", "Coprime partition product",
                PairScope(Equal(Z(JT), Mul(Z(J), Z(T)))),
                "Real power multiplicativity and reindexing through the actual multiplication "
                    + "equivalence factor the finite sum."),
            Claim("mass_pos", "positive-mass", "Strictly positive divisor mass",
                SingleScope(Quant(Dv, Div(N), Seq(D(0), Sp, Lt, Sp, M(N, Dv)))),
                "A positive weight divided by the positive finite partition is positive."),
            Claim("mass_total", "normalization", "Actual normalization",
                SingleScope(Equal(SumOver(Dv, Div(N), M(N, Dv)), D(1))),
                "Summing the independently defined quotient gives one."),
            Claim("mass_mul", "mass-product", "Actual mass product",
                PairScope(Factors(Equal(M(JT, Call("e", Pair(A, B))), Mul(M(J, A), M(T, B))))),
                "The weight and partition product laws give the product of the two actual masses."),
            Claim("split_pushforward", "splitting-pushforward", "Full splitting law",
                PairScope(Equal(P(Map(Dv, Pair(Q(Dv), R(Dv))), Mass(JT)),
                    Map(F.Id("u"), Mul(M(J, Call("fst", F.Id("u"))),
                        M(T, Call("snd", F.Id("u"))))))),
                "On the right u ranges over Div(J) times Div(T). The identity transports the "
                    + "original full-divisor law to the independently defined product mass."),
            Claim("observer_pushforward", "observed-marginal", "Actual observed marginal",
                PairScope(Equal(P(F.Id("q"), Mass(JT)), Mass(J))),
                "Pushforward composition with the first projection and hidden normalization "
                    + "identify the observed law."),
            Claim("hidden_pushforward", "hidden-marginal", "Actual hidden marginal",
                PairScope(Equal(P(F.Id("r"), Mass(JT)), Mass(T))),
                "Pushforward composition with the second projection and observed normalization "
                    + "identify the hidden law."),
            Claim("hidden_log_expectation", "hidden-expectation", "Full-law hidden log expectation",
                PairScope(Equal(FullMoment(), Moment(T))),
                "The actual hidden marginal transports the full-law logarithmic expectation."),
            Claim("observer_conditional_entropy", "graph-conditional-entropy", "Observer-first graph entropy",
                PairScope(Equal(GraphEntropy(), Call("H", Mass(T)))),
                "The injective splitting transports full entropy to product entropy. Public product "
                    + "mutual-information identities give entropy additivity, and the public quotient "
                    + "fiber decomposition identifies the graph conditional entropy. The graph is "
                    + "d mapped to (q(d),d), so the quantity is H(D given D_J)."),
            Claim("neg_log_mass", "pointwise-gibbs", "Pointwise divisor surprisal",
                SingleScope(Quant(Dv, Div(N), Equal(Seq(Minus, Ln(M(N, Dv))),
                    Add(Mul(S, Ln(V(Dv))), Ln(Z(N)))))),
                "Positive divisor values and a positive partition justify the logarithm of the "
                    + "quotient and the real power. There is no sign restriction on s."),
            Claim("gibbs_entropy", "finite-gibbs-entropy", "Finite divisor Gibbs entropy",
                SingleScope(Equal(Call("H", Mass(N)), Add(Mul(S, Moment(N)), Ln(Z(N))))),
                "Multiply the pointwise surprisal by mass, sum over actual divisors, and use "
                    + "normalization. No infinite series or division by s is used."),
            Claim("hidden_arithmetic_weight_formula", "hidden-arithmetic-weight", "Hidden arithmetic weight formula",
                PairScope(Equal(Ln(Z(T)), Seq(GraphEntropy(), Sp, Minus, Sp, Mul(S, FullMoment())))),
                "This is the real-parameter actual-divisor consumer of the first chapter's "
                    + "Theorem 5.5 in ZECKENDORF_EULER_5040. It combines the graph entropy, hidden "
                    + "expectation transport, and finite Gibbs identity. The alternate observer "
                    + "recording all observed prime exponents would require its own value-preserving "
                    + "equivalence and is not established here. Neighboring coarse-graining and "
                    + "collision-escape clauses are separate."))));

    private static DocumentBlock.Describe Claim(string declaration, string id, string title, Formula statement,
        string explanation, bool definition = false) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Quant(Formula v, Formula domain, Formula body) =>
        Seq(Forall, Sp, v, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Div(Formula n) => Call("Div", n);
    private static Formula V(Formula d) => Call("v", d);
    private static Formula W(Formula s, Formula d) => Call("w", s, d);
    private static Formula Z(Formula n) => Call("Z", n, S);
    private static Formula M(Formula n, Formula d) => Call("m", n, S, d);
    private static Formula Mass(Formula n) => Call("m", n, S);
    private static Formula Q(Formula d) => Call("q", d);
    private static Formula R(Formula d) => Call("r", d);
    private static Formula P(Formula f, Formula p) => Call("P", f, p);
    private static Formula Ln(Formula x) => Seq(Log, Sp, Open, x, Close);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula Map(Formula v, Formula value) => Seq(Open, v, Sp, Mapsto, Sp, value, Close);
    private static Formula CallInverse(Formula d) => new Formula.Apply(
        new Formula.Power(F.Id("e"), Seq(Minus, D(1))), [d]);
    private static Formula SumOver(Formula v, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(Seq(v, Sp, InMacro, Sp, domain)), Sp, body);
    private static Formula Moment(Formula n) => Seq(Open,
        SumOver(Dv, Div(n), Mul(M(n, Dv), Ln(V(Dv)))), Close);
    private static Formula FullMoment() => Seq(Open,
        SumOver(Dv, Div(JT), Mul(M(JT, Dv), Ln(V(R(Dv))))), Close);
    private static Formula GraphEntropy() => Call("C", P(Map(Dv, Pair(Q(Dv), Dv)), Mass(JT)));
    private static Formula Factors(Formula body) => Quant(A, Div(J), Quant(B, Div(T), body));
    private static Formula SingleScope(Formula body) => Quant(N, Naturals(), Quant(S, Reals(),
        Seq(Open, D(0), Sp, Lt, Sp, N, Close, Sp, Rightarrow, Sp, body)));
    private static Formula PairScope(Formula body, bool parameter = true) => new Formula.Aligned([
        Quant(J, Naturals(), Quant(T, Naturals(), parameter ? Quant(S, Reals(), Seq()) : Seq())),
        Seq(Open, D(0), Sp, Lt, Sp, J, Sp, Land, Sp, D(0), Sp, Lt, Sp, T,
            Sp, Land, Sp, Gcd, Open, J, Comma, T, Close, Sp, Eq, Sp, D(1), Close,
            Sp, Rightarrow),
        body
    ]);
}
