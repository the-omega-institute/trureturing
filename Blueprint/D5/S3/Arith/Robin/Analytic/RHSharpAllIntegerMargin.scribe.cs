using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic;

// Exact whole theorem with the original arithmetic readouts and record telescope.
internal sealed class RHSharpAllIntegerMarginDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional sharp Robin margins over all sufficiently large integers.",
        H("All integers and genuine original-record attainment"),
        Blocks(
            Paragraph(Text(
                "This consumer theorem uses the public delivered theorem "
                + "PriceRecord.RHSharpOriginalRecordMargin.original_record_sharp_lower_endpoint. "
                + "It reuses that module's exact K=2*sqrt(2)-2-firstLiMass and "
                + "RHSharpArithmeticEnvelope.D(x)=sqrt(x)*log(x). The imported firstLiMass is "
                + "twice the conventional first Li coefficient and is not renormalized. Here "
                + "gamma=Real.eulerMascheroniConstant, sigma_1(n)=ArithmeticFunction.sigma 1 n, "
                + "and Delta(n)=robinLogMargin(n)=gamma+log(log(log(n)))-log(sigma_1(n)/n). "
                + "RiemannHypothesis is the only headline hypothesis; the desired record endpoint "
                + "is imported and applied in the proof, not inserted as a headline assumption.")),
            Describe.Lean(
                DescribeId.Create("all-integer-logarithmic-margin"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/RHSharpAllIntegerMargin.F"),
                H("The actual logarithmic margin sequence"),
                StatementSource.FromAuthor(FDefinition()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "F(n)=D(log(n))*robinLogMargin(n) for every natural n, with the canonical "
                    + "total real logarithm and square root. Eventual-domain inequalities are "
                    + "proved inside the theorem, not added to its assumptions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("all-integer-linear-margin"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/RHSharpAllIntegerMargin.T"),
                H("The actual divisor-sum margin sequence"),
                StatementSource.FromAuthor(TDefinition()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "T(n)=(exp(gamma)*log(log(n))-sigma_1(n)/n)*sqrt(log(n)). Natural "
                    + "arguments and sigma_1(n) are cast to the reals in this exact readout."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rh-sharp-all-integer-margin"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Robin/Analytic/RHSharpAllIntegerMargin.all_integer_sharp_margin"),
                H("Both sharp envelopes and the real liminf values"),
                StatementSource.FromAuthor(AllIntegerClaim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assuming RH: (a) for every real epsilon>0 there exists a natural N such that "
                        + "EVERY natural n>=N satisfies K-epsilon<F(n) AND exp(gamma)*K-epsilon<T(n). "
                        + "(b) For every epsilon>0 and EVERY natural N there are a natural m>=N and "
                        + "a REAL lambda>0, with m>=2, such that for EVERY positive natural k<m the "
                        + "ORIGINAL goldenResourceObjective(lambda,k) is strictly less than "
                        + "goldenResourceObjective(lambda,m), and simultaneously "
                        + "abs(F(m)-K)<epsilon and abs(T(m)-exp(gamma)*K)<epsilon. "
                        + "(c) The real Filter.liminf of F on natural atTop is K, and that of T is "
                        + "exp(gamma)*K. There is no LI premise, no rate, and no RH proof.")),
                    Paragraph(Text(
                        "For arbitrary a=log(n)>1 take lambda=1/(a*log(a)). The public "
                        + "GoldenResourceOptimalLayerCount.optimal_layer_count_spec constructs a positive "
                        + "global optimizer m with exact strict layer counts, dividing EVERY positive "
                        + "global optimizer. A positive predecessor with equal objective would also be "
                        + "a global optimizer; m dividing that smaller integer is impossible. Thus the "
                        + "selected optimizer is a genuine strict predecessor record. This uses no "
                        + "uniqueness, no-tie or Robin-failure premise. The private Contact exists for "
                        + "all sufficiently large REAL a, as paid by strict_inventory_uniform_growth.")),
                    Paragraph(Text(
                        "Write b=log(m), g(t)=gamma+log(log(t)), and O for the original goldenResourceObjective. "
                        + "The identity golden_resource_sigma_identity expresses O in terms of the actual "
                        + "logarithmic sigma ratio W. For a,b>1, the exact decomposition is "
                        + "Delta(n)-Delta(m)=[g(a)-g(b)-lambda*(a-b)]+[O(lambda,m)-O(lambda,n)]. "
                        + "The second bracket is nonnegative by global optimality; the first is "
                        + "nonnegative by RestrictedDivisorStrictInventory.loglog_tangent, with a=b "
                        + "handled separately. Hence Delta(n)>=Delta(m). ActualBalancedExtremizer "
                        + "is not used as an arbitrary-integer supplier.")),
                    Paragraph(Text(
                        "Uniform clocks are paid before choosing witnesses. EulerLayerInventoryGrowth."
                        + "strict_inventory_uniform_growth gives b/a->1 over ALL positive strict "
                        + "inventories with one real threshold. Separately lambda(a)->0, while for "
                        + "each fixed prime p its first-layer marginal log(1+1/p)/log(p) is positive. "
                        + "Eventually p divides every selected optimizer. Nat.exists_infinite_primes "
                        + "then proves P=largestPrime(m)->infinity uniformly; b->infinity alone is not "
                        + "substituted for this argument. For arbitrary filters of FULL original records, "
                        + "largestPrime(m)<=m gives b->infinity from log(P)->infinity. The PUBLIC "
                        + "FullArithmeticCorrectionSecondOrder.price_record_full_arithmetic_correction_second_order "
                        + "bounds BOTH second-order expressions for the IDENTICAL actual correction C(m). "
                        + "Its epsilon=1 bound and log(P),log(b)->infinity give D(P)*C(m)->2*sqrt(2) "
                        + "and D(b)*C(m)->2*sqrt(2) via the consumed private leading_of_second_order_bound. "
                        + "The positive first limit pays eventual C(m)!=0 BEFORE field cancellation, "
                        + "so their quotient gives R1=D(b)/D(P)->1 in record_clocks. On contacts, "
                        + "D_ratio transports b/a->1 to R2=D(b)/D(a)->1. Then R1/R2 gives "
                        + "D(a)/D(P)->1; Contact.ha, Contact.hb and eventually P>1 pay the actual "
                        + "positive D denominators. No raw b/P or a/P limit is needed, and no private "
                        + "supplier is exposed, patched or repinned. "
                        + "Subtype/comap filters and eventually_comap extract the uniform thresholds. "
                        + "The special-price price_record_largest_prime_localization is not used.")),
                    Paragraph(Text(
                        "For the logarithmic lower bound fix the SIGNED c=K-epsilon/2. The public "
                        + "record theorem gives D(P)*Delta(m)>c, so comparison yields "
                        + "F(n)>(D(a)/D(P))*c. Continuity of multiplication by FIXED c controls "
                        + "abs(ratio-1)*abs(c), without bounding the possibly large D(P)*Delta(m). "
                        + "For attainment use the public genuine record witnesses with "
                        + "abs(z-K)<min(1,epsilon/2), so abs(z)<abs(K)+1; choose the normalization "
                        + "threshold first and bound abs((ratio-1)*z). The elementary largestPrime(m)<=m "
                        + "pays arbitrarily late NATURAL m.")),
                    Paragraph(Text(
                        "Exactly T=exp(gamma)*D(a)*(1-exp(-Delta)). A consumed local calculation "
                        + "uses PUBLIC firstLiMass_split, log_two_gt_d9, log_three_gt_d9, pi_gt_three "
                        + "and eulerMascheroniConstant_lt_two_thirds to prove K>0; it exposes no private "
                        + "numerical helper. For fixed 0<q<K, eventual F>q and monotonicity give a "
                        + "lower bound through the explicit proxy D(a)*(1-exp(-q/D(a))). Its limit q "
                        + "follows from the derivative of exp at zero and D(a)->infinity. Arbitrary "
                        + "Delta(n) need not tend to zero. Universally 1-exp(-d)<=d, hence T<=exp(gamma)*F "
                        + "on the eventual domain. Tightened logarithmic witnesses and the eventual "
                        + "linear lower bound give simultaneous attainment for F and T.")),
                    Paragraph(Text(
                        "The real liminf proof follows GronwallLowerEnvelope.robin_log_margin_liminf. "
                        + "For each sequence, an actual eventual lower bound gives IsBoundedUnder "
                        + "via isBoundedUnder_of_eventually_ge; arbitrarily late upper witnesses give "
                        + "IsCoboundedUnder via of_frequently_le. Natural atTop has NeBot. The proof "
                        + "then uses liminf_le_iff' and le_liminf_iff'. No eventual upper bound is "
                        + "assumed. There is no EReal duplicate "
                        + "or default-value substitution."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Attribution and limits. Oleg R. Musin, Ramanujan's theorem and highest abundant "
                + "numbers, arXiv:1905.09327v4, Theorem 1 and Corollary 1, gives the RH-conditional "
                + "all-integer lower bound with constant exp(gamma)*(2*sqrt(2)-4-gamma+log(4*pi)), "
                + "extending the classical Ramanujan margin using Robin's comparison. The source "
                + "and its scope are recorded in Library/Analytic/musin2020strongramanujan.md. "
                + "The exact firstLiMass_split identifies it with exp(gamma)*K. That literature "
                + "entry supplies attribution for the lower bound; equality attainment additionally "
                + "depends on the public original_record_sharp_lower_endpoint theorem. "
                + "The exact D5 theorem and Reg mirror pass the native target build. "
                + "The mirror proves the whole actual law, a literal Iff.rfl source bridge, and "
                + "observational dependence of both actual readouts on the natural state. It also "
                + "proves that rejecting any alternate family for this exact RH-conditional law "
                + "entails RH. Whole-family intervention and sensitivity, and complete enrolled-template "
                + "source-selection validation, remain unfinished. No accepted four-slot registration "
                + "or declared_validated status is claimed. No novelty, RH proof or explicit finite "
                + "5040 cutoff is claimed."))
        )));

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula ExpGamma => Call("exp", F.Id("gamma"));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsOne(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula AtMost(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula ImpliesClaim(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula FDefinition()
    {
        var n = F.Id("n");
        return Disp(All("n", Nat, Equal(Call("F", n),
            Multiply(Call("D", Call("log", n)), Call("robinLogMargin", n)))));
    }

    private static Formula TDefinition()
    {
        var n = F.Id("n");
        var logn = Call("log", n);
        return Disp(All("n", Nat, Equal(Call("T", n), Multiply(
            Subtract(Multiply(ExpGamma, Call("log", logn)),
                new Formula.Fraction(Call("sigma", D(1), n), n)),
            Call("sqrt", logn)))));
    }

    private static Formula StrictRecord(Formula m, Formula price)
    {
        var k = F.Id("k");
        return All("k", Nat, ImpliesClaim(Less(D(0), k),
            ImpliesClaim(Less(k, m), Less(Call("goldenResourceObjective", price, k),
                Call("goldenResourceObjective", price, m)))));
    }

    private static Formula NatLiminf(string sequence)
    {
        var n = F.Id("n");
        return Seq(Operatorname, Grp(F.Id("liminf")), Underscore,
            Grp(n, InMacro, Sp, Nat, Comma, Sp, n, To, Sp, Infty), Sp, Call(sequence, n));
    }

    private static Formula AllIntegerClaim()
    {
        var e = F.Id("epsilon");
        var cutoff = F.Id("N");
        var n = F.Id("n");
        var m = F.Id("m");
        var price = F.Id("lambda");
        var linearEndpoint = Multiply(ExpGamma, F.Id("K"));
        var lower = All("epsilon", Real, ImpliesClaim(Less(D(0), e),
            ExistsOne("N", Nat, All("n", Nat, ImpliesClaim(AtMost(cutoff, n),
                And(Less(Subtract(F.Id("K"), e), Call("F", n)),
                    Less(Subtract(linearEndpoint, e), Call("T", n))))))));

        Formula recordData = And(
            Less(new Formula.Absolute(Subtract(Call("F", m), F.Id("K"))), e),
            Less(new Formula.Absolute(Subtract(Call("T", m), linearEndpoint)), e));
        recordData = And(StrictRecord(m, price), recordData);
        recordData = And(AtMost(D(2), m), recordData);
        recordData = And(Less(D(0), price), recordData);
        recordData = And(AtMost(cutoff, m), recordData);
        var attainment = All("epsilon", Real, ImpliesClaim(Less(D(0), e),
            All("N", Nat, ExistsOne("m", Nat, ExistsOne("lambda", Real, recordData)))));
        return Disp(ImpliesClaim(Seq(Operatorname, Grp(F.Id("RiemannHypothesis"))),
            And(lower, And(attainment,
                And(Equal(NatLiminf("F"), F.Id("K")), Equal(NatLiminf("T"), linearEndpoint))))));
    }
}
