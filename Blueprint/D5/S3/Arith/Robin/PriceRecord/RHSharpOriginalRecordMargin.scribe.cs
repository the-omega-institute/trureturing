using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class RHSharpOriginalRecordMarginDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp lower Robin-margin endpoint for original positive-price strict records",
        H("The original integer, all positive predecessors, and sharp attainment"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-record-full-c-leading"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.fullC_leading"),
                H("The unconditional full correction at original records"),
                StatementSource.FromAuthor(FullCorrectionClaim()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("C(m) denotes FullArithmeticCorrectionSecondOrder.correction(m). "
                    + "For every epsilon>0 one T>=2 works for all original positive-price strict "
                    + "records after the largest-prime cutoff, retaining both logarithmic domains."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-record-prime-prefix-cutoff"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.Pn"),
                H("The exact last prime of a real cutoff"),
                StatementSource.FromAuthor(PnDefinition()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Pn(x) is the natural Finset supremum, with the natural empty-set "
                    + "convention, of all primes at most floorNat(x)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-record-b-prefix"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.B_prefix"),
                H("B depends only on this prime prefix"),
                StatementSource.FromAuthor(Disp(All("x", Real, EqualClaim(
                    Call("B", Call("Pn", F.Id("x"))), Call("B", F.Id("x")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact identity holds for every real x, with the existing "
                    + "totalized logarithms; no asymptotic replacement of Pn is made."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-record-cutoff-record"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.cutoff_record"),
                H("Every real prime prefix has a genuine original record"),
                StatementSource.FromAuthor(CutoffClaim()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The least positive global optimizer pays strict dominance over "
                    + "every positive predecessor. Its primeFactors are exactly primesLE(floorNat(x)), "
                    + "and its largest prime is exactly Pn(x)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-record-pn-at-top"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.Pn_atTop"),
                H("The exact cutoff prime tends to infinity"),
                StatementSource.FromAuthor(Disp(Call("Tendsto", F.Id("Pn"),
                    F.Id("atTop"), F.Id("atTop")))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The natural Pn is cast to Real for this limit."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-record-normalization"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.normalization"),
                H("The true cutoff has asymptotically identical normalization"),
                StatementSource.FromAuthor(Disp(Seq(Lim, Underscore,
                    Grp(F.Id("x"), To, Infty), new Formula.Fraction(
                        Call("D", Call("Pn", F.Id("x"))), Call("D", F.Id("x"))), Eq, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D(x)=sqrt(x)*log(x); the limit is on the real atTop filter."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-record-margin-identity"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.margin_identity"),
                H("The complete original margin splits exactly"),
                StatementSource.FromAuthor(MarginClaim()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The correction C is full; the original positive-price and all "
                    + "positive strict-predecessor hypotheses remain in the public identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-record-endpoint-constant"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.K"),
                H("The complete lower endpoint constant"),
                StatementSource.FromAuthor(KDefinition()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete arithmetic correction contributes 2*sqrt(2), while the real B lower endpoint contributes -2-firstLiMass."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("original-record-sharp-lower-endpoint"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/RHSharpOriginalRecordMargin.original_record_sharp_lower_endpoint"),
                H("Both sharp-endpoint quantifiers on genuine original records"),
                StatementSource.FromAuthor(EndpointClaim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Put M=firstLiMass, D(t)=sqrt(t)*log(t) and K=2*sqrt(2)-2-M. The objective is the "
                        + "canonical GoldenResourceOptimalInteger.goldenResourceObjective(lambda,n), defined "
                        + "as log(sum_(d in n.divisors)(d:Real)^(-1))-lambda*log(n). ObjectiveCore's "
                        + "golden_resource_sigma_identity identifies it with log(sigma_1(n)/n)-lambda*log(n). "
                        + "Neither objective nor robinLogMargin is redefined.")),
                    Paragraph(Text(
                        "Under RH, for every epsilon>0 a SINGLE real T>=2 is chosen before m and lambda. "
                        + "Every original natural m>=2 and real lambda>0 with "
                        + "forall n:Nat, 0<n -> n<m -> objective(lambda,n)<objective(lambda,m), and "
                        + "P=largestPrime(m)>=T, satisfies D(P)*robinLogMargin(m)>K-epsilon. "
                        + "Also, for every epsilon>0 and every real Y, genuine m:Nat and lambda:Real exist "
                        + "with m>=2, lambda>0, that SAME FULL positive strict-predecessor condition, "
                        + "P>Y, theta(P)>1, log(m)>1 and abs(D(P)*robinLogMargin(m)-K)<epsilon. "
                        + "No all-integer RH statement, finite 5040 closure or opposite endpoint is asserted.")),
                    Paragraph(Text(
                        "For each real x>=2 set N=floorNat(x), lambda=ActualBalancedCutoff.firstLayerPrice(N+1), "
                        + "and Pn(x)=sup id (Nat.primesLE N). The logarithms make lambda positive. "
                        + "firstLayerPrice_strictAnti and golden_layer_marginal_one_eq_log_one_add_inv give, "
                        + "for EVERY prime p, strict first-layer activation iff p<N+1 iff p<=N, including "
                        + "the excluded equality p=N+1. optimal_layer_count_spec supplies a positive minimal "
                        + "optimizer m whose factorizations are the strict counts and which divides every "
                        + "positive optimizer. At k=1, positive_layers_eq_count_interval and the prime "
                        + "factorization criterion identify m.primeFactors=primesLE N. Active prime 2 gives m>=2.")),
                    Paragraph(Text(
                        "For ANY 0<n<m, global optimality gives objective(n)<=objective(m). If strictness "
                        + "failed, equality would make n another positive optimizer: every k>=1 has "
                        + "objective(k)<=objective(m)=objective(n). Minimality then gives m|n, whence m<=n, "
                        + "a contradiction. This pays the full positive predecessor telescope, including n=1 "
                        + "and n=2 when they are predecessors. Higher-layer ties stay excluded by strict "
                        + "counts. No uniqueness or noncritical-price premise is used.")),
                    Paragraph(Text(
                        "Finset.sup_le gives Pn<=N and Finset.le_sup puts every prime p<=N below Pn. "
                        + "Therefore primesLE(Pn)=primesLE(N) without needing supremum membership first, "
                        + "and largestPrime(m)=Pn. theta_eq_sum_primesLE gives theta(Pn)=theta(x). "
                        + "The E₃ definition in Third has trailing +log(log(x))+gamma OUTSIDE its prime sum. "
                        + "Using primesLE_eq_filter_Ioc_zero gives "
                        + "E₃(Pn)-log(log(Pn))=E₃(x)-log(log(x)), and hence B(Pn)=B(x) exactly. "
                        + "E₃(Pn)=E₃(x) is not used.")),
                    Paragraph(Text(
                        "For every real bound Y, Nat.exists_infinite_primes gives a fixed prime p>=ceilNat(Y). "
                        + "When x>=p, Nat.le_floor puts p in the prefix and Finset.le_sup gives Pn(x)>=p. "
                        + "Thus Pn(x)->infinity. The unconditional prime_number_limits.2 at x and Pn(x), "
                        + "together with theta(Pn)=theta(x), gives exactly "
                        + "Pn/x=(theta(x)/x)/(theta(Pn)/Pn)->1. Logarithmic continuity at 1 gives "
                        + "log(Pn/x)->0, and division by log(x)->infinity yields log(Pn)/log(x)->1. "
                        + "The square-root ratio and this logarithmic ratio give D(Pn)/D(x)->1. "
                        + "The all-real B envelope bounds abs(D(x)*B(x)) by abs(M)+3, so "
                        + "D(Pn)*B(Pn)-D(x)*B(x)=(D(Pn)/D(x)-1)*D(x)*B(x)->0. "
                        + "All denominators are justified eventually by x>1 and Pn>=2. No prime-gap estimate "
                        + "or Fourier transport of nearby endpoints enters this construction.")),
                    Paragraph(Text(
                        "For arbitrary original records, ActualPriceRecordPrimeStructure gives exact initial "
                        + "prime support. OriginalEndpointPrimeTail.tail_robin_data then gives "
                        + "robinLogMargin(m)=B(P)+C(m), where the canonical FullArithmeticCorrectionSecondOrder.correction "
                        + "is C(m)=tail(m)+log(log(log(m)))-log(log(theta(P))). The public "
                        + "price_record_full_arithmetic_correction_second_order supplies a threshold 1<T0. "
                        + "At second-order tolerance 1, it bounds "
                        + "abs(log(P)*(D(P)*C(m)-2*sqrt(2))+d)<1, d=sqrt(2)*(2+log(2)). "
                        + "Choose T>=max(T0,2,exp(1+(1+abs(d))/eta)); division by the positive log(P) gives "
                        + "abs(D(P)*C(m)-2*sqrt(2))<eta uniformly before m and lambda are chosen.")),
                    Paragraph(Text(
                        "For the universal lower bound take eta=epsilon/2 for both the real B envelope and "
                        + "fullC, then add the signed inequalities for the SAME integer m. For sharp "
                        + "attainment first choose the fullC threshold at epsilon/3 and the prime-normalization "
                        + "transfer threshold at epsilon/3, and a further x threshold ensuring "
                        + "Pn(x)>=max(TC,Y+1). Only THEN invoke arbitrarily-late real-B attainment at epsilon/3. "
                        + "Construct the cutoff record at this x. Its exact P is Pn(x), and the identity "
                        + "D(P)*margin(m)-K=[D(x)*B(x)+2+M]+[D(P)*B(P)-D(x)*B(x)] "
                        + "+[D(P)*C(m)-2*sqrt(2)] pays the three additional transfer budgets. "
                        + "The real-B attainment argument also separates the arithmetic, phase and "
                        + "WholeFormula residual errors."))),
                DescribeRole.Theorem))));


    private static Formula EqualClaim(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula FullCorrectionClaim()
    {
        var e = F.Id("epsilon"); var t = F.Id("T"); var m = F.Id("m");
        var price = F.Id("lambda"); var p = Call("largestPrime", m);
        var conclusion = And(Less(D(1), Call("theta", p)), And(Less(D(1), Call("log", m)),
            Less(new Formula.Absolute(Subtract(Multiply(Call("D", p), Call("C", m)),
                Multiply(D(2), Call("sqrt", D(2))))), e)));
        var records = All("m", Nat, ImpliesClaim(Le(D(2), m), All("lambda", Real,
            ImpliesClaim(Less(D(0), price), ImpliesClaim(StrictRecord(m, price),
                ImpliesClaim(Le(t, p), conclusion))))));
        return Disp(All("epsilon", Real, ImpliesClaim(Less(D(0), e),
            ExistsOne("T", Real, And(Le(D(2), t), records)))));
    }
    private static Formula PnDefinition() => Disp(All("x", Real, EqualClaim(Call("Pn", F.Id("x")),
        Call("FinsetSup", Call("primesLE", Call("floorNat", F.Id("x"))), F.Id("id")))));
    private static Formula CutoffClaim()
    {
        var x = F.Id("x"); var m = F.Id("m"); var price = F.Id("lambda");
        var data = And(Le(D(2), m), And(Less(D(0), price), And(StrictRecord(m, price),
            And(EqualClaim(Call("primeFactors", m), Call("primesLE", Call("floorNat", x))),
                EqualClaim(Call("largestPrime", m), Call("Pn", x))))));
        return Disp(All("x", Real, ImpliesClaim(Le(D(2), x),
            ExistsOne("m", Nat, ExistsOne("lambda", Real, data)))));
    }
    private static Formula MarginClaim()
    {
        var m = F.Id("m"); var price = F.Id("lambda");
        var identity = EqualClaim(Call("robinLogMargin", m),
            Add(Call("B", Call("largestPrime", m)), Call("C", m)));
        return Disp(All("m", Nat, ImpliesClaim(Le(D(2), m), All("lambda", Real,
            ImpliesClaim(Less(D(0), price), ImpliesClaim(StrictRecord(m, price), identity))))));
    }

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula ExistsOne(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Less(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula ImpliesClaim(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula KDefinition() => Disp(new Formula.Relation(F.Id("K"),
        FormulaRelationOperator.Equal,
        Subtract(Subtract(Multiply(D(2), Call("sqrt", D(2))), D(2)), F.Id("firstLiMass"))));

    private static Formula StrictRecord(Formula m, Formula price)
    {
        var n = F.Id("n");
        return All("n", Nat, ImpliesClaim(Less(D(0), n),
            ImpliesClaim(Less(n, m), Less(Call("goldenResourceObjective", price, n),
                Call("goldenResourceObjective", price, m)))));
    }

    private static Formula EndpointClaim()
    {
        var e = F.Id("epsilon");
        var t = F.Id("T");
        var m = F.Id("m");
        var price = F.Id("lambda");
        var y = F.Id("Y");
        var p = Call("largestPrime", m);
        var margin = Multiply(Call("D", p), Call("robinLogMargin", m));
        var afterCutoff = ImpliesClaim(Le(t, p), Less(Subtract(F.Id("K"), e), margin));
        var everyRecord = All("m", Nat, ImpliesClaim(Le(D(2), m),
            All("lambda", Real, ImpliesClaim(Less(D(0), price),
                ImpliesClaim(StrictRecord(m, price), afterCutoff)))));
        var lowerBound = All("epsilon", Real, ImpliesClaim(Less(D(0), e),
            ExistsOne("T", Real, And(Le(D(2), t), everyRecord))));

        Formula recordData = Less(new Formula.Absolute(Subtract(margin, F.Id("K"))), e);
        recordData = And(Less(D(1), Call("log", m)), recordData);
        recordData = And(Less(D(1), Call("theta", p)), recordData);
        recordData = And(Less(y, p), recordData);
        recordData = And(StrictRecord(m, price), recordData);
        recordData = And(Less(D(0), price), recordData);
        recordData = And(Le(D(2), m), recordData);
        var attainment = All("epsilon", Real, ImpliesClaim(Less(D(0), e),
            All("Y", Real, ExistsOne("m", Nat, ExistsOne("lambda", Real, recordData)))));
        return Disp(ImpliesClaim(Seq(Operatorname, Grp(F.Id("RiemannHypothesis"))),
            And(lowerBound, attainment)));
    }
}
