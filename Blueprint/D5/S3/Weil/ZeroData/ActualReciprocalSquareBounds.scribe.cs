using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class ActualReciprocalSquareBoundsDocument : IScribeDocumentDefinition
{
    private static Formula Nat => Seq(Mathbb, Grp(FormulaDsl.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(FormulaDsl.Id("R")));
    private static Formula Complex => Seq(Mathbb, Grp(FormulaDsl.Id("C")));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula Then(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Absolute(Formula value) => new Formula.Absolute(value);

    private static Formula SetOfNat(string variable, Formula predicate) =>
        Seq(Left, OpenBrace, DefinitionDsl.Id(variable), Colon, Nat, Sp, Mid, Sp, predicate, Right, CloseBrace);

    private static Formula CountBothFormula()
    {
        var t = DefinitionDsl.Id("T");
        var k = DefinitionDsl.Id("k");
        var ordinate = Absolute(Call("im", Call("actualZero", k)));
        var cutoff = SetOfNat("k", AtMost(ordinate, t));
        var left = Call("ncard", cutoff);
        var right = new Formula.Floor(Multiply(new Formula.Number(2), Power(t, new Formula.Number(2))));
        return All("T", Real, Then(AtMost(new Formula.Number(10), t), AtMost(left, right)));
    }

    private static Formula NaturalMassFormula()
    {
        var k = DefinitionDsl.Id("k");
        var ordinate = Call("im", Call("actualZero", k));
        var inverse = Power(ordinate, new Formula.Negate(new Formula.Number(1)));
        var term = Power(Seq(Left, Open, inverse, Right, Close), new Formula.Number(2));
        var mass = Seq(Sum, Underscore, Grp(k, Sp, InMacro, Sp, Nat), Sp, term);
        var factor = new Formula.Fraction(new Formula.Number(101), new Formula.Number(100));
        return AtMost(mass, Multiply(factor, DefinitionDsl.Id("firstLiMass")));
    }

    private static Formula HeightFormula()
    {
        var rho = DefinitionDsl.Id("rho");
        return All("rho", Complex,
            Then(Call("IsNontrivialZero", rho),
                Less(new Formula.Number(10), Absolute(Call("im", rho)))));
    }

    public DocumentDefinition Create()
    {
        return DocumentDefinition.Create(ScribeNode.Create(
            "Actual multiplicity-exact zero mass and unconditional height-ten exclusion from the first xi resolvent at six.",
            H("Actual Zeta Mass and Height"),
            Blocks(
                Paragraph(Text(
                    "The exact source family is actualData = zetaZeroData, with " +
                    "the real kernel pairWeight rho = Re(1/(rho*(1-rho))), and " +
                    "firstLiMass = 2 + EulerGamma - 2*log(2*sqrt(pi)). " +
                    "The normalized reflection and resolvent-positive R(6) chain uses " +
                    "sixWeight, sixDefect, the digamma-at-3 and H512 reductions, " +
                    "log(pi) and log(2) bounds, the complete von Mangoldt prime-power series, " +
                    "and the tail integral 1/648. The complex HasSum at six is consumed by the " +
                    "real HasSum for sixWeight; the positive kernel estimate and the evaluated defect " +
                    "are then consumed by the height contradiction.")),
                Paragraph(Text(
                    "The natural-index enumeration is equivalent to the sigma family of Fin (actualData.multiplicity n) over " +
                    "the exhaustive actual family. ActualZeroOccurrence, its infinite instance, " +
                    "actualOccurrenceEquiv : N ≃ ActualZeroOccurrence, actualZero, the exact fiber " +
                    "identity and fiber cardinality give exact transports of the infinite mass and " +
                    "the finite inclusive cutoffs. The resulting family includes both imaginary signs and every positive " +
                    "analytic multiplicity. The reciprocal-square summability and strict total bound " +
                    "are transported through those fibers. After height ten is proved, the complete " +
                    "inverse-square mass is sharpened to at most (101/100)*firstLiMass. " +
                    "The mathematical count consequence applies that sharper mass to the " +
                    "literal cutoff |Im(actualZero k)| ≤ T and gives ncard ≤ floor(2*T^2) for " +
                    "every T ≥ 10, without a filtered family or RH premise.")),
                Describe.Lean(
                    DescribeId.Create("actualcomplexpairweighthassum"),
                    DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_complex_pairWeight_hasSum"),
                    H("Complete Complex First Li Mass"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The normalized xi resolvent gives the multiplicity-weighted complex first Li mass. Taking real parts yields the real pair-weight mass; transporting the complex sum to every analytic occurrence supplies the complete integrated series."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("firstlimasssplit"),
                    DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.firstLiMass_split"),
                    H("First Li Mass Normalization"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The first Li mass equals 2 plus the Euler constant minus twice log 2 minus log pi. This normalization supplies the height estimates and the scalar cancellation in the integrated explicit formula."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("zeroendpointlogderiv"),
                    DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.zero_endpoint_logDeriv"),
                    H("Xi Logarithmic Derivative at Zero"), StatementSource.WithoutFormula(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The logarithmic derivative of xi at zero is minus half the first Li mass. Reflection gives the endpoint at one, and the zero endpoint normalizes the complete resolvent."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("actualreciprocalsquarebounds"),
                    DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_inverse_square_mass_le_height"),
                    H("Complete Height-Derived Inverse Square Mass"),
                    StatementSource.FromAuthor(Disp(NaturalMassFormula())),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The sum is over every natural occurrence k, with both imaginary signs and " +
                        "each exact analytic multiplicity. For u = Im(rho)^2 > 100, " +
                        "1/u <= (101/100)/(u+1) <= (101/100)*pairWeight(rho). " +
                        "Multiplication by each multiplicity and comparison of the summable full " +
                        "series give mass <= (101/100)*firstLiMass. The occurrence equivalence " +
                        "transports this bound exactly to the displayed natural-index sum. " +
                        "The two private refined-mass helpers feed this public conclusion. " +
                        "The height theorem is upstream; no height or mass certificate is assumed."))),
                    DescribeRole.Theorem),
                Paragraph(Text(
                    "The complete height-derived mass bound gives the following literal-cutoff consequence.")),
                new DocumentBlock.DisplayFormula(CountBothFormula()),
                Paragraph(Text(
                    "For each distinct source zero n, the occurrence fiber is exactly " +
                    "{actualOccurrenceEquiv.symm (n,j) : j in Fin(actualData.multiplicity n)}. " +
                    "Its cardinality is actualData.multiplicity n, and multiplicity_spec identifies " +
                    "this number with the analytic order. The weighted reciprocal-square series " +
                    "is summable; its coarse mass is below 2*firstLiMass < 2. Transport through " +
                    "the natural equivalence gives both the natural-index summability and mass < 2. " +
                    "The distinct indices |Im(zero n)| <= T form a finite set for every real T: " +
                    "the strip bounds its spectral radius by T+1. Taking all finite occurrence " +
                    "fibers and mapping back by the equivalence yields exactly the inclusive " +
                    "natural cutoff, with no change of cutoff or sign restriction. For every " +
                    "real-valued weight w, the finite natural sum equals the sum over these " +
                    "distinct indices of multiplicity(n)*w(zero n). Its cardinality equals the " +
                    "sum of the exact fiber cardinalities. For T >= 10, every cutoff occurrence " +
                    "contributes at least 1/T^2, so count/T^2 <= the full mass " +
                    "<= (101/100)*firstLiMass < 2. Thus count < 2*T^2, and the natural-floor " +
                    "inequality displayed above follows.")),
                Describe.Lean(
                    DescribeId.Create("actualheightgtten"),
                    DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_height_gt_ten"),
                    H("First Resolvent at Six"),
                    StatementSource.FromAuthor(Disp(HeightFormula())),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The displayed telescope binds an arbitrary complex rho and assumes only the " +
                        "actual predicate IsNontrivialZero rho; its conclusion is exactly " +
                        "10 < |rho.im|. The proof first obtains the endpoint estimate S < 1/3 and " +
                        "the conjugate-pair bootstrap u > 5. The normalized resolvents at 1 and 6, " +
                        "the multiplicity-preserving reflection permutation, and the rational identity " +
                        "produce T6 = 165 * sum_n multiplicity(n) * sixWeight(zero n). The lower " +
                        "kernel is 9/(10*(u+1)*(u+31)); a zero with u ≤ 100 forces " +
                        "T6 ≥ 297/13231. Factorization at six gives " +
                        "T6 = 593/60 + 6*EulerGamma - 11*log(2) - 5*log(pi) + Q6; " +
                        "the H512 estimate, the one-term logarithm lower bound, all von Mangoldt " +
                        "prime powers, and the integrable tail 1/648 give " +
                        "T6 < 329/15000, a strict contradiction. Exhaustivity then transfers " +
                        "100 < (Im(zero n))^2 to the arbitrary rho. No height, mass, numerical, " +
                        "critical-line, or RH premise is introduced. " +
                        "These numerical reductions bound the same complete analytic quantities: " +
                        "firstLiMass_lt_one proves firstLiMass < 1, excluding real zeros and making " +
                        "conjugate indices distinct; firstLiMass_lt_third proves firstLiMass < 1/3 " +
                        "for the bootstrap u > 5. At the resolvent parameter 6, gamma_upper_r6 proves " +
                        "EulerGamma < 5787/10000, log_pi_lower_r6 proves 11447/10000 < log(pi), " +
                        "and Real.log_two_gt_d9 implies 6931/10000 < log(2). " +
                        "These upper, lower, and lower bounds have the directions required by " +
                        "the coefficients +6, -5, and -11. The gamma bound uses the exact harmonic " +
                        "sum H512 and log(512) = 9*log(2). The bound sixQ_upper proves Q6 < 7/500 " +
                        "for the actual Re(-zeta'(6)/zeta(6)), using its complete von Mangoldt " +
                        "series and every term with n >= 4 in the tail comparison. The bound " +
                        "sixDefect_upper combines these estimates to give T6 < 329/15000 for " +
                        "the same defect. The proof actual_ordinate_sq_gt_hundred consumes this " +
                        "bound with the low-zero lower bound, and actual_height_gt_ten transfers " +
                        "the contradiction to every actual nontrivial zero."))),
                    DescribeRole.Theorem),
                Paragraph(Text(
                    "For the complete-zero application, the seven CompleteZeroFamily fields are supplied by the exact zero, strip, " +
                    "height, reciprocal-square summability, reciprocal-square mass < 2, finite " +
                    "count shell, and count bound above. Soundness follows from zero_isNontrivial; " +
                    "exhaustivity follows by choosing the zero-th element of each positive finite fiber. " +
                    "The same construction over the conjugation index supplies the conjugate occurrence. " +
                    "For every h in Icc 0 2 and every real y, the literal complex spectralKernel " +
                    "equals the sum over n of multiplicity(n)*exp((zero n-h)*y)*resolventCoefficient(zero n,h). " +
                    "Absolute summability of the full natural series permits its exact equivalence " +
                    "and sigma-sum transports; finite fiber summation gives the complex multiplicity. " +
                    "The shell application holds for every m >= 1: shellWeight is summable and " +
                    "shellSum <= 10000*exp(-100*m). For every real m > 0 and every real gamma, " +
                    "lowHIntegrand is integrable on Ioi 1. The original mean bound assumes m >= 1 " +
                    "and gamma > 10. For an actual rho, it sets " +
                    "gamma = |Im rho|, so actual_height_gt_ten supplies gamma > 10. " +
                    "The Gaussian moment, absolute-convergence and extension derivation uses " +
                    "the scalar hypothesis m ≥ 1 and the bound " +
                    "m*(gamma+10)^2*(2400000*exp(-83*m) + 2400 + 384*exp(-28*m)). " +
                    "Here the inner h-domain is the full Icc 0 2 with weight 1+h, whose integral is 4; " +
                    "the Gaussian center is 16*m with variance denominator 4*m; the physical envelope " +
                    "has coefficient 3; and the shell estimate has core coefficient 20, " +
                    "giving 3*4*20 = 240 and the 2400000*exp(-83*m) term. The positive and negative " +
                    "extensions are 2400 and 384*exp(-28*m).")),
                Paragraph(Text("Complete-family first Li mass application.")),
                Paragraph(Text("The arbitrary-index reciprocal-mass Gaussian shell formula and its full weighted endpoint derivation are given in the existing CountableGaussianQuadraticFourthMoment exposition. For this actual family take I=N, t(k)=Im(actualZero(k)), w(k)=1, a=10 and any real m>=1. The actual_height_gt_ten theorem supplies the full-family height condition; actual_weighted_inverse_square_summable and actual_inverse_square_tsum_transport supply the natural-occurrence summability. The seven-field witness also retains its original strict mass <2, inclusive-cutoff finiteness and count bound. Soundness, exhaustiveness, exact analytic multiplicities, both conjugate occurrences, the exact occurrence fibers and their cardinalities, and the full complex multiplicity-reindexed kernel remain in that same witness.")),
                Paragraph(Text("Write R_Z=sum_k Im(actualZero(k))^(-2). First obtain Summable(k -> (|Im(actualZero(k))|+1)*exp(-m*Im(actualZero(k))^2)) and shell<=1100*R_Z*exp(-100*m)<=2200*exp(-100*m) directly from the original R_Z<2. Independently apply the substantive actual_inverse_square_mass_le_height theorem to this identical entire occurrence family: R_Z<=(101/100)*firstLiMass. Nonnegative multiplication and 1100*(101/100)=1111 give shell<=1111*firstLiMass*exp(-100*m). This uses the height-derived mass theorem, rather than substituting the old 2200 estimate. The exact firstLiMass is 2+EulerGamma-2*log(2*sqrt(pi)), twice the first Li endpoint 1+EulerGamma/2-log(2*sqrt(pi)). The kernel still uses both signs and every occurrence, with no finite-subset, critical-line, injectivity or desired-shell-bound premise.")),
                Paragraph(Text("The complete seven-field original-family application also keeps shell<=10000*exp(-100*m), integrability for every real gamma and m>0, and the original m>=1, gamma>10 mean bound m*(gamma+10)^2*(2400000*exp(-83*m)+2400+384*exp(-28*m)). For every actual nontrivial zero rho one may set gamma=|Im(rho)| because actual_height_gt_ten supplies that certificate. The 1111 first-Li-mass shell consequence alone does not certify a revised weighted 2400000 endpoint, the full Robin sign, retained Schur bounds, a completed carrier or RH. The complete weighted endpoint also requires the Gaussian moment, absolute convergence and extension bounds.")),
                Paragraph(Text(
                    "The proof uses endpoint " +
                    "normalization, strip and conjugation algebra, occurrence and fiber transports, " +
                    "finite cutoff membership, the real-part HasSum, kernel positivity, and the " +
                    "von Mangoldt tail comparison.")))));
    }
}

