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
            Paragraph(Text("Complete Gaussian localization uses exactly this owner's occurrence family. Write rho_k=actualZero(k), eta_k=Im(rho_k), c_k=1/(rho_k*(1-rho_k)) and R=sum_k eta_k^(-2). The public actual_sigma_inverse_square_summable transports through actualOccurrenceEquiv to summability of the natural occurrence series. The existing actual_inverse_square_mass_le_height gives R<=(101/100)*firstLiMass, and the public firstLiMass_lt_one gives R<2. These two publicizations change no proof body. Each coefficient satisfies |c_k|<=eta_k^(-2), so the complete H(y)=sum_k c_k*exp(rho_k*y) is absolutely convergent with |H(y)|<=2*exp(max(y,0)). Conjugation makes H real. No assumption of a simple, separated, rightmost or critical-line zero enters.")),
            Paragraph(Text("For gamma>10 the finite local set S={k:|eta_k-gamma|<=6} is formed from actualData.symmetricIndices(|gamma|+7), taking every finite multiplicity fiber, mapping by actualOccurrenceEquiv.symm, then filtering by this exact closed condition. The strip gives spectralRadius(rho_k)<=|eta_k|+1; every local occurrence has |eta_k|<=gamma+6 and therefore belongs to that spectral enumeration. All distance-six occurrences belong to S. Every member has |eta_k|<=gamma+10, hence 1<=(gamma+10)^2*eta_k^(-2). Summing and using R<2 yields card(S)<=2*(gamma+10)^2. Both signs remain in the underlying occurrence family; the strict complement |eta_k-gamma|>6 includes every occurrence outside S.")),
            Paragraph(Text("For any real m>=1 and real gamma put q_k=(rho_k-i*gamma)^2+16*(rho_k-i*gamma) and E=sum_k exp(m*q_k). The strip gives Re(rho_k)^2+16*Re(rho_k)<=17. With r=eta_k-gamma, r^2*exp(-m*r^2)<=1 follows from 1+m*r^2<=exp(m*r^2), and eta_k^2<=2*r^2+2*gamma^2. Consequently |exp(m*q_k)|<=exp(17*m)*(2+2*gamma^2)*eta_k^(-2). This summable majorant proves absolute convergence before splitting E into S and its entire strict complement. It does not assume a lower bound on E or a favorable sign of its complement.")),

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
                    H("Complete Complex First Li Mass"), StatementSource.FromLean(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The normalized xi resolvent gives the multiplicity-weighted complex first Li mass. Taking real parts yields the real pair-weight mass; transporting the complex sum to every analytic occurrence supplies the complete integrated series."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("firstlimasssplit"),
                    DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.firstLiMass_split"),
                    H("First Li Mass Normalization"), StatementSource.FromLean(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The first Li mass equals 2 plus the Euler constant minus twice log 2 minus log pi. This normalization supplies the height estimates and the scalar cancellation in the integrated explicit formula."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("zeroendpointlogderiv"),
                    DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.zero_endpoint_logDeriv"),
                    H("Xi Logarithmic Derivative at Zero"), StatementSource.FromLean(),
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
                Describe.Lean(
                    DescribeId.Create("actualreciprocalsquareboundsheightfourteenheight"),
                    DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_height_gt_fourteen"),
                    H("Every Nontrivial Zero Has Absolute Ordinate Greater Than Fourteen"),
                    StatementSource.FromLean(),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every complex rho satisfying IsNontrivialZero rho, the conclusion is " +
                            "14 < |rho.im|. The exhaustive actualData = zetaZeroData family contains both " +
                            "imaginary signs, and actualData.multiplicity records the positive analytic " +
                            "order of each distinct zero. The existing height-ten exclusion supplies " +
                            "u = rho.im^2 > 100 for this same complete family.")),
                        Paragraph(Text(
                            "Write q = rho*(1-rho), p = rho.re*(1-rho.re), and b = Im(q). The actual " +
                            "open strip gives 0 < p <= 1/4, while Re(q) = u+p and b^2 = u*(1-4*p). " +
                            "For c = (0,30,56,90,132,182), put v = sqrt(u*(1-4*p)), " +
                            "z_j = u+p+c_j+i*v, F = product_j z_j^(-1), and W(u,p) = Re(F). " +
                            "Since b = v or b = -v, simultaneous complex conjugation identifies this " +
                            "weight with Re(1/(q*(q+30)*(q+56)*(q+90)*(q+132)*(q+182))) for either " +
                            "signed imaginary part, including b = 0.")),
                        Paragraph(Text(
                            "The sector comparison works on the closed auxiliary range 0 <= p <= 1/4. " +
                            "With theta_j = arctan(v/(u+p+c_j)) and Theta = sum_j theta_j, each angle " +
                            "lies between 0 and 1/sqrt(u). Thus 0 <= Theta+theta_j <= 7/sqrt(u) " +
                            "< 7/10 < pi/2 for u > 100. Polar multiplication gives " +
                            "W(u,p) = (product_j |z_j|^(-1))*cos(Theta) > 0. Differentiation in u gives " +
                            "-sum_j |F/z_j|*(cos(Theta+theta_j)+(v/(2*u))*sin(Theta+theta_j)) < 0. " +
                            "For p < 1/4, differentiation in p gives " +
                            "-sum_j |F/z_j|*(cos(Theta+theta_j)-(2*u/v)*sin(Theta+theta_j)) > 0: " +
                            "the zero shift ensures Theta+theta_j >= theta_0 and " +
                            "tan(theta_0) = v/(u+p) > v/(2*u). Continuity extends the comparison " +
                            "to p = 1/4. Consequently W decreases with u and increases with p; " +
                            "100 < u <= 196 implies W(u,p) >= W(196,0). The value p = 0 is an " +
                            "auxiliary boundary used for comparison; actual zeros retain 0 < p.")),
                        Paragraph(Text(
                            "For s = 6,8,10,12,14 define D_s = (2*s-1)*firstLiMass/2 " +
                            "- Re(logDeriv xiReading s). The normalized complex xi resolvents at 1 " +
                            "and s, paired through the reflection permutation rho -> 1-rho, preserve " +
                            "every analytic multiplicity. Taking real parts and exact partial fractions " +
                            "therefore gives the full HasSum of multiplicity(n)*W(u_n,p_n), with total " +
                            "S6 = D_6/3990729600 - D_8/3555377280 + D_10/6739588800 " +
                            "- D_12/24711825600 + D_14/216459734400.")),
                        Paragraph(Text(
                            "Evaluation of the xi logarithmic derivatives and digamma values gives " +
                            "S6 = 66493177/143006288128704000 + (4/12649365729)*EulerGamma " +
                            "- log(2)/1816214400 - (9487/40477970332800)*log(pi) " +
                            "+ Q_6/3990729600 - Q_8/3555377280 + Q_10/6739588800 " +
                            "- Q_12/24711825600 + Q_14/216459734400, where " +
                            "Q_s = Re(-zeta'(s)/zeta(s)) = sum_n Lambda(n)/n^s is the complete " +
                            "von Mangoldt series. Its inclusive finite part through 64 has exactly " +
                            "the 27 nonzero prime-power terms " +
                            "2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37,41,43,47,49,53,59,61,64. " +
                            "For positive Q coefficients the upper estimate includes the entire " +
                            "remaining series n >= 65, bounded by the integral from 64 to infinity of " +
                            "x^(1-s)/2, namely 1/(2*(s-2)*64^(s-2)), using Lambda(n) <= log(n) <= n/2. " +
                            "For negative Q coefficients the finite lower estimate uses nonnegativity " +
                            "of the entire omitted tail.")),
                        Paragraph(Text(
                            "Rational atanh logarithm bounds for the prime bases give " +
                            "Q_6 <= 12633076304737/1000000000000000, " +
                            "1445084153477/500000000000000 <= Q_8, " +
                            "Q_10 <= 174085111381/250000000000000, " +
                            "2677198143/15625000000000 <= Q_12, and " +
                            "Q_14 <= 42538887969/1000000000000000. The public library theorem " +
                            "HarmonicGammaTail.eulerMascheroni_upper_128 directly supplies " +
                            "EulerGamma < 5772156650/10^10 < 5772157/10000000. " +
                            "Real.log_two_gt_d9 gives 6931471803/10000000000 < log(2); " +
                            "Real.pi_gt_d20 and the atanh expansion with parameter K = 12 give " +
                            "2289459771/2000000000 < log(pi). These inequalities have the directions " +
                            "required by the signed coefficients, yielding " +
                            "S6 <= 72126772613108177/15194418113674800000000000000000.")),
                        Paragraph(Text(
                            "If an actual zero had u <= 196, its distinct conjugate zero would have " +
                            "the same weight and multiplicity. Each analytic multiplicity is at least " +
                            "one. Positivity of every other term in the complete summable family then " +
                            "gives S6 >= 2*W(196,0) = 345650537/72636763553532703907200. " +
                            "The exact lower-minus-upper difference is " +
                            "4091911135692077535684108547/" +
                            "349994189092536057987654937200000000000000000 > 0, a strict contradiction. " +
                            "Hence u > 196 for every source zero, and exhaustivity transfers " +
                            "14 < |rho.im| to the original arbitrary nontrivial zero. The argument " +
                            "uses the complete strip family with both signs and all analytic multiplicities."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("actualreciprocalsquareboundsheightfourteenmass"),
                    DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualReciprocalSquareBounds.actual_inverse_square_mass_le_height_fourteen"),
                    H("Complete Natural Occurrence Inverse Square Mass at Height Fourteen"),
                    StatementSource.FromLean(),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The conclusion is sum'_k ((((actualZero k).im)^(-1))^2) " +
                            "<= (197/196)*firstLiMass over every natural occurrence k, with no " +
                            "hypothesis. Here actualZero k = actualData.zero (actualOccurrenceEquiv k).1, " +
                            "and actualOccurrenceEquiv is the unchanged equivalence from Nat to " +
                            "the full sigma family of Fin(actualData.multiplicity n). Each distinct " +
                            "zero therefore occurs exactly its positive analytic multiplicity, " +
                            "with both imaginary signs retained.")),
                        Paragraph(Text(
                            "For a source zero put u = Im(zero n)^2. The height theorem gives u > 196; " +
                            "the strip estimate for pairWeight rho = Re(1/(rho*(1-rho))) gives " +
                            "1/u <= (197/196)/(u+1) <= (197/196)*pairWeight(zero n). " +
                            "Multiply by the exact analytic multiplicity and compare the complete " +
                            "summable inverse-square series with actual_pairWeight_hasSum, whose " +
                            "total is firstLiMass = 2+EulerGamma-2*log(2*sqrt(pi)). The exact " +
                            "actual_inverse_square_tsum_transport then carries the weighted sum " +
                            "through every finite multiplicity fiber and actualOccurrenceEquiv to " +
                            "the entire natural-index sum. The height exclusion is supplied by " +
                            "actual_height_gt_fourteen, so no height or mass certificate is an additional premise."))),
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

