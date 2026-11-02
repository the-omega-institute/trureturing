using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class WolfordBinomialBirootDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/WolfordBinomialBiroot.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithSums/wolford2025biroot");
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, F.Id(name), Colon, type, Comma, Sp, body);
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula x => F.Id("x");
    private static Formula c => F.Id("c");
    private static Formula n => F.Id("n");
    private static Formula m => F.Id("m");
    private static Formula k => F.Id("k");
    private static Formula C => Call("ceiling", m, n);
    private static Formula U => Call("numerator", x, c, n, m);
    private static Formula V => Call("denominator", x, c, n, m);
    private static Formula Beta => Call("beta", x, c, n, m);
    private static Formula Inputs(Formula body) => All("x", Real, All("c", Real, All("n", Nat, All("m", Nat, body))));
    private static Formula Summand(bool denominator) => Mul(Mul(Pow(x, k), Pow(c,
        denominator ? Sub(Sub(m, Mul(n, k)), D(1)) : Sub(m, Mul(n, k)))),
        Call("choose", m, denominator ? Add(Mul(n, k), D(1)) : Mul(n, k)));
    private static Formula SumFormula(bool denominator) => Seq(Sum, Underscore, Grp(Seq(k, Eq, D(0))), Caret,
        Grp(denominator ? Sub(C, D(1)) : C), Sp, Summand(denominator));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role, bool derived = false,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("wolford-" + name), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), derived ? AssessedProvenance.FromRepo(Source) : AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role, claim);

    public DocumentDefinition Create()
    {
        var positive = Seq(D(0), Lt, x, Land, Sp, D(0), Lt, c, Land, Sp, D(1), Le, Sp, n);
        var domain = All("m", Nat, Seq(D(0), Lt, m, Implies, Sp, D(0), Lt, V));
        var limit = Call("Tendsto", Call("positiveIndexQuotientSequence", x, c, n), Call("atTop"),
            Call("nhds", Pow(x, new Formula.Fraction(D(1), n))));
        var statement = All("x", Real, All("c", Real, All("n", Nat, Seq(Par(positive), Implies, Sp, Par(Seq(domain, Land, Sp, limit))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The original generalized binomial biroot converges for all positive real parameters and every positive root index.",
            H("Wolford's generalized binomial biroot"), Blocks(
            Paragraph(Text("The assertion is Conjecture 3.4 of arXiv:2508.14095v3. Both source summation bounds are inclusive. The ceiling is the exact rational ceiling, choose(m,j) is the natural binomial coefficient extended by zero for j>m, and each displayed exponent of c is an integer. Positive x and c are arbitrary real numbers, n ranges over every natural n>=1, and the limit uses all positive integer m, including every residue class. No parameter-uniform rate is asserted. positiveIndexQuotientSequence(x,c,n) denotes m mapped to beta(x,c,n,m), including the totalized zero value at m=0.")),
            Node("ceiling", "Exact ceiling", All("m", Nat, All("n", Nat, Seq(C, Eq, Call("ceilQ", new Formula.Fraction(m, n))))),
                "ceiling(m,n) is the natural ceiling of the rational quotient m/n. For n>=1 this is the ordinary integer ceiling. ceiling_bound proves m<=n*ceiling(m,n).", DescribeRole.Definition),
            Node("numerator", "Inclusive source numerator", Inputs(Seq(U, Eq, SumFormula(false))),
                "The numerator includes k=0 and k=ceiling(m,n). An out-of-range binomial factor makes a padded term zero even when its signed c exponent is negative. Natural subtraction does not define the source exponent.", DescribeRole.Definition),
            Node("denominator", "Inclusive source denominator", Inputs(Seq(V, Eq, SumFormula(true))),
                "The denominator includes k=0 through ceiling(m,n)-1. For positive m and n this ceiling is positive, so the Lean range with length (ceiling-1)+1 has exactly the source indices. denominator_pos proves positivity using its k=0 term m*c^(m-1) and nonnegativity of every other term.", DescribeRole.Definition),
            Node("beta", "Positive-index quotient", Inputs(Seq(Par(Seq(D(0), Lt, m, Implies, Sp, Beta, Eq, new Formula.Fraction(U, V))), Land, Sp,
                Call("beta", x, c, n, D(0)), Eq, D(0))),
                "beta is exactly numerator/denominator at every positive m and is totalized to zero at m=0. This isolated value does not affect atTop convergence.", DescribeRole.Definition),
            Node("result", "Full convergence and denominator domain", statement,
                "For every positive real x,c and natural n>=1, all positive-index denominators are strictly positive and beta tends to x raised to the reciprocal real n. Real.rpow_pos_of_pos and Real.rpow_inv_natCast_pow identify this as the positive real nth root.", DescribeRole.Theorem, true,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wolford-2025-generalized-binomial-biroot-conjecture-3-4"),
                    ResolutionKind.Proved)),
            Paragraph(Text("The finite state type is ZMod n. shift moves each state to its successor, and walk(a,b)=a*I+b*shift. shift_pow and walk_pow identify every power entry with the complete weighted binomial multisection. matrix_mul_nat is the scalar matrix identity used by walk_pow. walk_nonneg and walk_stochastic establish the stochastic hypotheses. walk_primitive selects the positive binomial summand indexed by the least nonnegative representative of j-i in the nth matrix power; it applies to arbitrary n, including composite n. walk_column identifies the uniform stationary row. walk_limit applies FiniteStochasticMixing.primitive_convergence and its uniqueness conclusion.")),
            Paragraph(Text("residue is the unnormalized weighted multisection. normalized_residue proves its exact scaling to a walk entry, residue_limit transfers entry convergence to 1/n, and residue_ratio_limit takes the ratio using the nonzero limit 1/n. weight, weight_zero and multisection give a finite bijection between source indices and all admissible binomial indices. numerator_residue and denominator_residue prove the literal source reconstruction for n>=2, including padded zero terms and signed exponents. limit_ge_two then transfers the exact quotient limit.")),
            Paragraph(Text("The source denominator for n=1 omits the constant binomial term. denominator_one proves the exact correction x*denominator=residue-c^m. limit_one divides by (c+x)^m and uses geometric decay of (c/(c+x))^m. Thus n=1 is proved from its original indices, without identifying it with the uncorrected residue ratio. result combines this case with limit_ge_two and consumes denominator_pos.")),
            Paragraph(Text("The generalized binomial biroot and convergence conjecture are due to Wolford, whose source proves the square-root case. The source-to-walk reconstruction above derives the general quotient limit from finite stochastic mixing.")))));
    }
}
