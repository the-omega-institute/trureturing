using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualIntegerOccupationCoercivityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Robin/PriceRecord/ActualIntegerOccupationCoercivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantitative second-layer occupation coercivity for every positive integer.",
        H("Actual integer occupation and the unrestricted objective defect"),
        Blocks(
            Paragraph(Text("The estimate combines exact local integer-objective losses with "
                + "uniform moving margins and the global prime-number-theorem error. "
                + "The composition is repository-derived; no historical novelty or RH "
                + "conclusion is asserted.")),
            Describe.Lean(
                DescribeId.Create("actual-local-count-maximal"),
                DeclarationHandle.Create(Prefix + "count_maximal"),
                H("The existing count optimizer is locally maximal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive real price lam, genuine prime p and exponent a, "
                    + "goldenPrimeLocalObjective(lam,p,a) is at most its value at "
                    + "optimalLayerCount(lam,p). Only private is removed from the original "
                    + "declaration; its type and proof are unchanged. The original layer-2 "
                    + "losses and the finite-gap extraction consume it here. The first-layer "
                    + "missing and occupied loss proofs consume it directly from this owner. "
                    + "This public exposure introduces no second local-maximality proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-finite-local-gap-sum"),
                DeclarationHandle.Create(Prefix + "actual_local_gap_sum_le_defect"),
                H("Any finite set of prime local gaps is paid by the same actual defect"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For z>1, n>=1 and any finite set S of genuine primes, the sum over S "
                    + "of goldenPrimeLocalObjective(referencePrice(z),p,optimalLayerCount("
                    + "referencePrice(z),p))-goldenPrimeLocalObjective(referencePrice(z),p,"
                    + "factorization(n,p)) is at most actualDefect(z,n). The proof is the "
                    + "single extraction of the existing unrestricted supremum/factorization "
                    + "argument. Both common_support_charge and actual_first_layer_charge "
                    + "consume it on their disjoint H union X. The unit, absent primes, "
                    + "primes beyond z and unbounded exponents remain in scope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-integer-quantitative-occupation-defect"),
                DeclarationHandle.Create(Prefix + "eventually_quantitative_actual_occupation_defect"),
                H("A uniform quantitative estimate on arbitrary finite actual masks"),
                StatementSource.FromAuthor(TargetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The formula uses the existing "
                        + "ActualReservePrimeMask.actualDefect(z,n) literally. The existing "
                        + "referencePrice(z) is 1/(z log z). The existing actualPressure(z) "
                        + "is the supremum of goldenResourceObjective(referencePrice(z),m) "
                        + "over ALL integers m >= 1, including the unit. Thus the defect is "
                        + "that same supremum minus the objective of the SAME n. The "
                        + "objective is the canonical log(sigma(n)/n) - log(n)/(z log z), "
                        + "by the existing objective identity. H and X are quantified finite "
                        + "sets, not newly defined global masks or masses.")),
                    Paragraph(Text("H can contain any prime p <= sqrt(2) sqrt(z) with "
                        + "factorization(n,p) <= 1, including primes absent from n. X can "
                        + "contain any prime p > sqrt(2) sqrt(z) with factorization(n,p) >= 2. "
                        + "X has no upper cutoff: primes greater than z, arbitrarily large "
                        + "prime factors, and arbitrarily large exponents are included. "
                        + "The complete hole set is finite by its bounded real endpoint; "
                        + "the complete excess set is finite because exponent >= 2 implies "
                        + "membership in n.primeFactors. Both full masks are instances of "
                        + "this submask theorem. Disjointness follows from the opposite "
                        + "inequalities at the literal included lower cutoff.")),
                    Paragraph(Text("Proof-to-code step 1: the consumed private local_step adapter "
                        + "applies GoldenLocalThreshold.golden_prime_local_objective_diff, "
                        + "normalizing only multiplication order. Its existing owner proof "
                        + "is reused after removal of private at that owner. count_maximal consumes "
                        + "positive_layers_eq_count_interval and "
                        + "golden_prime_local_objective_maximal_of_threshold. hole_loss "
                        + "uses monotonicity of the first marginal and the layer-2 increment. "
                        + "It treats exponents 0 and 1 explicitly. excess_loss uses "
                        + "golden_layer_strict_decrease and the same increment to show "
                        + "that all later included layers can only increase the loss. "
                        + "No exponent cap or strict-margin premise occurs in the target.")),
                    Paragraph(Text("Proof-to-code step 2: actual_local_gap_sum_le_defect "
                        + "extracts the original common-support decomposition once. For any finite "
                        + "prime set S it obtains U from optimal_layer_count_spec at the positive "
                        + "price, and uses golden_resource_supremum_eq_positive_part_sum together "
                        + "with objective_at_optimal_eq_positive_part_sum to identify the EXISTING "
                        + "actualPressure with U's objective. On T = U.primeFactors union "
                        + "n.primeFactors union S, golden_resource_objective_sum_on makes "
                        + "actualDefect exactly the sum of local gaps. The count specification "
                        + "rewrites U's exponents to optimalLayerCount; count_maximal makes each "
                        + "gap nonnegative. Restricting to S proves the finite-gap bound. "
                        + "common_support_charge now consumes that extraction once on H union X, "
                        + "using the original hole_loss and excess_loss comparisons. The same "
                        + "public extraction is consumed by FirstPrimePrefixLocalization. "
                        + "A missing prime has exponent zero; primes greater than z remain "
                        + "included. U remains a proof witness, never a target premise.")),
                    Paragraph(Text("Proof-to-code step 3: second_marginal identifies "
                        + "g2(p) = log(1 + 1/[p(p+1)]) and proves the needed "
                        + "bounds 1/(p^2+p+1) <= g2(p) <= p^(-2). "
                        + "The elementary log(1+u) <= u also gives the intermediate "
                        + "ordinary bound g2(p) <= 1/[p(p+1)] <= p^(-2). "
                        + "The code uses Real.one_sub_inv_le_log_of_pos for the lower "
                        + "estimate and the existing golden_layer_marginal_le_inv_pow "
                        + "for the upper estimate needed downstream. Dividing by the "
                        + "positive log p gives the actual layer-2 marginal.")),
                    Paragraph(Text("Proof-to-code step 4: put L = log z, r = sqrt z, "
                        + "c = sqrt 2 for this exposition. eventual_geometry makes L >= 32 "
                        + "and c/r + 1/z <= 1/L. far_margins works simultaneously for "
                        + "EVERY real eta with 8/L <= eta <= 1/4. For p <= (c-eta)r, "
                        + "(c-eta)^2 <= 2-2eta, c r+1 <= z/L <= eta z/8, "
                        + "and log p <= L/2+1 <= (1/2+eta/8)L. Consequently "
                        + "(p^2+p+1) log p <= (1-eta/2) z L, and "
                        + "(1+eta/2)(1-eta/2) <= 1 yields "
                        + "marginal(p,2)-referencePrice(z) >= eta/(2zL). "
                        + "For p > (c+eta)r, log p >= L/2. With t=c+eta <=2, "
                        + "t^2 >= 2+(5/2)eta and (1-eta/2)t^2 >=2. The reciprocal "
                        + "square upper bound then gives "
                        + "referencePrice(z)-marginal(p,2) >= eta/(2zL). "
                        + "This last estimate is for ALL such primes, without p <= z.")),
                    Paragraph(Text("Proof-to-code step 5: theta_error_log_power(2) supplies "
                        + "one GLOBAL real T such that for every y >= T, "
                        + "abs(theta(y)-y) <= y/log(y)^2. Both moving endpoints "
                        + "A=(c-eta)r and B=(c+eta)r are at least r, uniformly in eta. "
                        + "Thus eventual_geometry can require r >= T once, before "
                        + "quantifying eta. theta_window uses log A, log B >= L/2 and "
                        + "A+B=2cr to get theta(B)-theta(A) <= 2eta r + 8cr/L^2 "
                        + "<=4eta r. This is two applications of a global PNT error "
                        + "bound, not a short-interval PNT assumption.")),
                    Paragraph(Text("Proof-to-code step 6: fixed_eta_bound filters H at "
                        + "p <= A and X at B < p. Their complements are disjoint "
                        + "selected primes in the literal interval A < p <= B. "
                        + "sum_log_interval bounds their sum by theta(B)-theta(A), "
                        + "using Chebyshev.theta_eq_sum_primesLE and finite sum_sdiff. "
                        + "The far charge and r^2=z give, with d=r L actualDefect(z,n), "
                        + "the bound (sum_H log p + sum_X log p)/r <= 4eta + 2d/eta "
                        + "for all 8/L <= eta <=1/4. Near primes are counted once.")),
                    Paragraph(Text("Proof-to-code step 7: actual_reserve_prime_mask at "
                        + "the empty existing PrimeMask supplies nonnegativity of the "
                        + "SAME actualDefect, so d >= 0. clipped_optimization uses "
                        + "eta=max(8/L,sqrt d) when sqrt d <=1/4. Then eta <=8/L+sqrt d "
                        + "and d/eta <=sqrt d, giving 32/L+6sqrt d. When sqrt d>1/4, "
                        + "eta=1/4 gives 1+8d <=4sqrt d+8d. At d=0 the first choice "
                        + "is eta=8/L>0, so no division by sqrt 0 occurs. Adding the "
                        + "nonnegative remaining terms gives the displayed constants 6,8,32.")),
                    Paragraph(Text("The residual 32/log z pays the finite-clock displacement "
                        + "of the exact second marginal from the unshifted sqrt(2)sqrt(z) "
                        + "cutoff. The argument does not claim a pure C sqrt d estimate "
                        + "at d=0, an effective numerical Z, sharp constants, a gap bound, "
                        + "a mass premise, an assumed optimizer, a support/exponent cap, "
                        + "or any RH or Robin conclusion."))),
                DescribeRole.Theorem))));

    private static Formula TargetFormula()
    {
        Formula z = F.Id("z");
        Formula Z = F.Id("Z");
        Formula n = F.Id("n");
        Formula h = F.Id("H");
        Formula x = F.Id("X");
        Formula p = F.Id("p");
        Formula r = Call("sqrt", z);
        Formula cutoff = Mul(Call("sqrt", D(2)), r);
        Formula hp = All([Bound("p", Naturals())],
            Implies(In(p, h), And(Call("Prime", p),
                And(Le(p, cutoff), Le(Call("factorization", n, p), D(1))))));
        Formula xp = All([Bound("p", Naturals())],
            Implies(In(p, x), And(Call("Prime", p),
                And(Lt(cutoff, p), Le(D(2), Call("factorization", n, p))))));
        Formula defectScale = Mul(Mul(r, Call("log", z)),
            Call("actualDefect", z, n));
        Formula left = Div(Add(LogSum(h), LogSum(x)), r);
        Formula right = Add(Add(Mul(D(6), Call("sqrt", defectScale)),
            Mul(D(8), defectScale)), Div(D(3, 2), Call("log", z)));
        Formula masks = All([Bound("H", Call("Finset", Naturals())),
            Bound("X", Call("Finset", Naturals()))],
            Implies(hp, Implies(xp, Le(left, right))));
        Formula integers = All([Bound("n", Naturals())], Implies(Le(D(1), n), masks));
        Formula scales = All([Bound("z", Reals())], Implies(Le(Z, z), integers));
        return Disp(Exists([Bound("Z", Reals())], And(Le(D(2), Z), scales)));
    }

    private static Formula LogSum(Formula s) => Seq(Sum, Underscore,
        Grp(Seq(F.Id("p"), InMacro, Sp, s)), Sp, Call("log", F.Id("p")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula In(Formula a, Formula s) => Seq(a, InMacro, Sp, s);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
