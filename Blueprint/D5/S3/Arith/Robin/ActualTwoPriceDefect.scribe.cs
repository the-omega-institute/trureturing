using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ActualTwoPriceDefectDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ActualTwoPriceDefect.";
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula NatPair => Seq(Nat, Sp, Times, Sp, Nat);
    private static Formula P(Formula f) => Seq(Left, Open, f, Right, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. args]);
    private static Formula All(string v, Formula t, Formula f) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), t, f);
    private static Formula Ex(string v, Formula t, Formula f) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), t, f);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula AtMost(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Less(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Divides(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Divides, y);
    private static Formula Member(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula Both(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Then(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Equivalent(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Subtract(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Multiply(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Quotient(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Power(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Absolute(Formula x) => new Formula.Absolute(x);
    private static Formula Pair(Formula x, Formula y) => P(Seq(x, Comma, Sp, y));
    private static Formula Lam(string v, Formula t, Formula f) =>
        P(Seq(LambdaLower, Sp, P(Seq(F.Id(v), Colon, t)), Sp, Mapsto, Sp, P(f)));
    private static Formula Set(string v, Formula t, Formula f) =>
        Seq(Left, OpenBrace, F.Id(v), Colon, t, Sp, Mid, Sp, f, Right, CloseBrace);
    private static Formula Case(string v, Formula condition, Formula yes, Formula no) =>
        P(Seq(Operatorname, Grp(F.Id("if")), Sp, F.Id(v), Colon, P(condition), Sp,
            Operatorname, Grp(F.Id("then")), Sp, yes, Sp, Operatorname, Grp(F.Id("else")), Sp, no));
    private static Formula Int(string v, Formula lo, Formula hi, Formula f) =>
        Seq(F.Int, Underscore, Grp(lo), Caret, Grp(hi), Sp, P(f), Thin,
            Mathrm, Grp(F.Id("d")), F.Id(v));
    private static Formula Prod(string v, Formula t, Formula domain, Formula f) =>
        Seq(F.Prod, Underscore, Grp(Seq(P(Seq(F.Id(v), Colon, t)), Sp, InMacro, Sp, domain)), Sp, P(f));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact pressure defects for the strict all-layer integer and the constructed weak-layer maximum.",
        H("Actual Two-Price Defect and the Full Layer Maximum"),
        Blocks(
            Paragraph(Text("All variables in the displays have their indicated real or natural types. valuation(n,p) means n.factorization(p), Prime means Nat.Prime, Icc and uIcc are closed and unordered closed intervals, and Finite means set finiteness. All integrals use the real variable shown by the differential and Lebesgue measure. Proof arguments are suppressed only when proof-irrelevant; the positive-price argument of weakLayerExponents is displayed. IsGoldenResourceOptimal(q,n) compares goldenResourceObjective(q,m) with goldenResourceObjective(q,n) for every natural m at least 1. The objective is log of the reciprocal-divisor sum minus q times log(n). goldenLayerMarginal(p,k) is log((1-(1/p)^(k+1))/(1-(1/p)^k))/log(p). These are the actual imported functions.")),
            Describe.Lean(
                DescribeId.Create("actual-two-price-strict-integer"),
                DeclarationHandle.Create(Prefix + "strictInteger"),
                H("strictInteger"),
                StatementSource.FromAuthor(Disp(FormulastrictInteger())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive q, choose exactly the integer supplied by optimal_layer_count_spec. It has every strict positive layer and divides every positive optimizer. The value at nonpositive q is the total-definition convention 1. optimalLayerCountSpec denotes that existing existence proof with its positive-price argument."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-two-price-strict-integer-pos"),
                DeclarationHandle.Create(Prefix + "strictInteger_pos"),
                H("strictInteger pos"),
                StatementSource.FromAuthor(Disp(FormulastrictIntegerpos())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The chosen strict inventory is a positive natural integer at every positive price."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-price-strict-integer-counts"),
                DeclarationHandle.Create(Prefix + "strictInteger_counts"),
                H("strictInteger counts"),
                StatementSource.FromAuthor(Disp(FormulastrictIntegercounts())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every natural prime direction has the original strict count; nonprime directions are included as zero directions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-price-strict-layer-iff"),
                DeclarationHandle.Create(Prefix + "strict_layer_iff"),
                H("strict layer iff"),
                StatementSource.FromAuthor(Disp(Formulastrictlayeriff())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every prime and every positive layer index, occupation is equivalent to a strict price inequality. Equality layers are excluded."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-price-strict-integer-eq-product"),
                DeclarationHandle.Create(Prefix + "strictInteger_eq_product"),
                H("strictInteger eq product"),
                StatementSource.FromAuthor(Disp(FormulastrictIntegereqproduct())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product reconstructs the same chosen strict integer from all of its prime directions, using the original strict layer counts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-price-weak-layers-finite"),
                DeclarationHandle.Create(Prefix + "weak_layers_finite"),
                H("weak layers finite"),
                StatementSource.FromAuthor(Disp(Formulaweaklayersfinite())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a positive price the entire set of weak layers is finite. Both prime and positive exponent indices range over all naturals, and every equality layer is included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-price-weak-layer-count"),
                DeclarationHandle.Create(Prefix + "weakLayerCount"),
                H("weakLayerCount"),
                StatementSource.FromAuthor(Disp(FormulaweakLayerCount())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The natural set cardinality counts all weak layers in a direction. This is a total definition; finiteness is asserted separately at positive prices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-two-price-weak-layers-eq-count-interval"),
                DeclarationHandle.Create(Prefix + "weak_layers_eq_count_interval"),
                H("weak layers eq count interval"),
                StatementSource.FromAuthor(Disp(Formulaweaklayerseqcountinterval())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Strict decrease of the actual marginal makes each finite weak layer set a complete positive prefix, including its last equality layer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-price-weak-layer-exponents"),
                DeclarationHandle.Create(Prefix + "weakLayerExponents"),
                H("weakLayerExponents"),
                StatementSource.FromAuthor(Disp(FormulaweakLayerExponents())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite support is the image of the first projection of the entire weak-layer set. onFinset has exactly the displayed values; its proof-irrelevant support certificate is the one in weakLayerExponents. weakLayersFinite denotes weak_layers_finite, and toFinset uses that finite-set proof."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-two-price-maximal-integer"),
                DeclarationHandle.Create(Prefix + "maximalInteger"),
                H("maximalInteger"),
                StatementSource.FromAuthor(Disp(FormulamaximalInteger())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At positive q this is the finite prime-power product of weakLayerExponents. finsuppProd sums no exponents: it multiplies p raised to k over the support. At other prices its value is 1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-two-price-optimizer-exponent-bounds"),
                DeclarationHandle.Create(Prefix + "optimizer_exponent_bounds"),
                H("optimizer exponent bounds"),
                StatementSource.FromAuthor(Disp(Formulaoptimizerexponentbounds())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every positive global optimizer has each exponent between the original strict count and the full weak count."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-price-maximal-integer-spec"),
                DeclarationHandle.Create(Prefix + "maximalInteger_spec"),
                H("maximalInteger spec"),
                StatementSource.FromAuthor(Disp(FormulamaximalIntegerspec())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The constructed product is positive, has exactly the weak counts and is globally optimal. Every positive optimizer divides it and is at most it. No optimizer or finite-closure premise is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-price-maximal-integer-all-ties"),
                DeclarationHandle.Create(Prefix + "maximalInteger_all_ties"),
                H("maximalInteger all ties"),
                StatementSource.FromAuthor(Disp(FormulamaximalIntegerallties())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All simultaneous equality layers form a finite set and are exactly the layers added between the strict and maximal integers, for every prime and every positive index."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-price-price"),
                DeclarationHandle.Create(Prefix + "price"),
                H("price"),
                StatementSource.FromAuthor(Disp(Formulaprice())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real price is total; its positivity and analytic use below are on x greater than 1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-two-price-weight"),
                DeclarationHandle.Create(Prefix + "weight"),
                H("weight"),
                StatementSource.FromAuthor(Disp(Formulaweight())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The square applies separately to x and to log(x). The denominator is x squared times the square of log(x)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-two-price-integer-at"),
                DeclarationHandle.Create(Prefix + "integerAt"),
                H("integerAt"),
                StatementSource.FromAuthor(Disp(FormulaintegerAt())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integer at x is the original strict inventory evaluated at price(x)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-two-price-clock"),
                DeclarationHandle.Create(Prefix + "clock"),
                H("clock"),
                StatementSource.FromAuthor(Disp(Formulaclock())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The clock is the logarithm of that integer. It is not the price parameter x."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-two-price-w"),
                DeclarationHandle.Create(Prefix + "W"),
                H("W"),
                StatementSource.FromAuthor(Disp(FormulaW())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("sigma(1,n) is the natural divisor sum and real denotes the natural-to-real cast. The definition uses real division and the total real logarithm."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-two-price-pressure"),
                DeclarationHandle.Create(Prefix + "pressure"),
                H("pressure"),
                StatementSource.FromAuthor(Disp(Formulapressure())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This total sSup ranges over objectives of all positive natural integers. Boundedness and unconditional attainment below are proved only at positive prices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-two-price-defect"),
                DeclarationHandle.Create(Prefix + "defect"),
                H("defect"),
                StatementSource.FromAuthor(Disp(Formuladefect())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same specified integer n is evaluated at price(a). Its own logarithm is retained in the linear resource term."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-two-price-compact-layer-support"),
                DeclarationHandle.Create(Prefix + "compact_layer_support"),
                H("compact layer support"),
                StatementSource.FromAuthor(Disp(Formulacompactlayersupport())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One finite set contains every weakly active prime layer throughout the whole closed interval, with no exponent cutoff. The finite set also contains only prime positive layers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-price-clock-monotone"),
                DeclarationHandle.Create(Prefix + "clock_monotone"),
                H("clock monotone"),
                StatementSource.FromAuthor(Disp(Formulaclockmonotone())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("MonotoneOn is written out with both real arguments in the open interval above 1. It follows from divisibility growth as price decreases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-price-pressure-eq-of-optimal"),
                DeclarationHandle.Create(Prefix + "pressure_eq_of_optimal"),
                H("pressure eq of optimal"),
                StatementSource.FromAuthor(Disp(Formulapressureeqofoptimal())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This conditional equality has no positive-price hypothesis. It takes a positive optimizer as input and asserts no optimizer exists at a nonpositive price."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-price-pressure-maximal-spec"),
                DeclarationHandle.Create(Prefix + "pressure_maximal_spec"),
                H("pressure maximal spec"),
                StatementSource.FromAuthor(Disp(Formulapressuremaximalspec())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At every positive price the proved constructed optimizer supplies an upper bound for the entire objective set and attains its real supremum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-price-pressure-integral"),
                DeclarationHandle.Create(Prefix + "pressure_integral"),
                H("pressure integral"),
                StatementSource.FromAuthor(Disp(Formulapressureintegral())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integral is oriented and allows a less than b, b less than a and equal endpoints. Strict left stability at every activation event supplies the one-sided derivative; reflection gives the right-sided fundamental theorem of calculus."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-price-two-price-oriented"),
                DeclarationHandle.Create(Prefix + "two_price_oriented"),
                H("two price oriented"),
                StatementSource.FromAuthor(Disp(Formulatwopriceoriented())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both real centers are arbitrary above 1. The same original source integer is retained. Pressure at the comparison price is attained by the constructed full weak product; integration gives its exact comparison cost."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-price-npc5-oriented"),
                DeclarationHandle.Create(Prefix + "npc5_oriented"),
                H("npc5 oriented"),
                StatementSource.FromAuthor(Disp(Formulanpc5oriented())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Set a equal to the source integer logarithm A=clock(x). Both x>1 and A>1 remain hypotheses, and the original source is integerAt(x)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-price-npc5"),
                DeclarationHandle.Create(Prefix + "npc5"),
                H("npc5"),
                StatementSource.FromAuthor(Disp(Formulanpc5())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both price orders and all activation ties are included. Monotonicity of the strict clock converts orientation into the absolute integrand over the sorted endpoints. The case A=clock(x)=x>1 is included in the same formulas: both integration endpoints coincide, so the oriented and absolute integrals and defect are zero. This conditional case does not assert the existence of a fixed point."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-two-price-npc5-any-comparison-optimizer"),
                DeclarationHandle.Create(Prefix + "npc5_any_comparison_optimizer"),
                H("npc5 any comparison optimizer"),
                StatementSource.FromAuthor(Disp(Formulanpc5anycomparisonoptimizer())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every positive optimizer at the source own price gives the same cost. C is an arbitrary optimizer in this conditional statement. For any x>1 with A=clock(x)>1, take q=price(A)>0 and M=maximalInteger(q). maximalInteger_spec constructs M without an optimizer certificate and proves every positive global optimizer divides M and is at most M. maximalInteger_all_ties gives the finite set of all simultaneous equality layers and, for every prime p and every k>=1, valuation(strictInteger(q),p)<k<=valuation(M,p) if and only if goldenLayerMarginal(p,k)=q. pressure_maximal_spec and the sigma identity identify defect(A,integerAt(x)) with objective(q,M)-objective(q,integerAt(x)); two_price_oriented, npc5_oriented and npc5 supply both the oriented and absolute integrals for this same source. Thus all constructed-maximal comparison clauses remain consequences of the complete general statements, including A=x and all ties, without a separate tracked conjunction."))),
                DescribeRole.Theorem),
            Paragraph(Text("These identities and optimizer constructions do not establish the original signed-floor estimate, NPC7, the full Robin inequality on the 5040 family, or the Riemann hypothesis.")))));

    private static Formula FormulastrictInteger() =>
        All("q", Real, Equal(Call("strictInteger", F.Id("q")), Case("hq", Less(D(0), F.Id("q")), Call("choose", Call("optimalLayerCountSpec", F.Id("q"), F.Id("hq"))), D(1))));

    private static Formula FormulastrictIntegerpos() =>
        All("q", Real, Then(Less(D(0), F.Id("q")), AtMost(D(1), Call("strictInteger", F.Id("q")))));

    private static Formula FormulastrictIntegercounts() =>
        All("q", Real, Then(Less(D(0), F.Id("q")), All("p", Nat, Equal(Call("valuation", Call("strictInteger", F.Id("q")), F.Id("p")), Call("optimalLayerCount", F.Id("q"), F.Id("p"))))));

    private static Formula Formulastrictlayeriff() =>
        All("q", Real, Then(Less(D(0), F.Id("q")), All("p", Nat, All("k", Nat, Then(Call("Prime", F.Id("p")), Then(AtMost(D(1), F.Id("k")), Equivalent(AtMost(F.Id("k"), Call("valuation", Call("strictInteger", F.Id("q")), F.Id("p"))), Less(F.Id("q"), Call("goldenLayerMarginal", F.Id("p"), F.Id("k"))))))))));

    private static Formula FormulastrictIntegereqproduct() =>
        All("q", Real, Then(Less(D(0), F.Id("q")), Equal(Call("strictInteger", F.Id("q")), Prod("p", Nat, Call("primeFactors", Call("strictInteger", F.Id("q"))), Power(F.Id("p"), Call("optimalLayerCount", F.Id("q"), F.Id("p")))))));

    private static Formula Formulaweaklayersfinite() =>
        All("q", Real, Then(Less(D(0), F.Id("q")), Call("Finite", Set("pk", NatPair, Both(AtMost(D(1), Call("snd", F.Id("pk"))), Both(Call("Prime", Call("fst", F.Id("pk"))), AtMost(F.Id("q"), Call("goldenLayerMarginal", Call("fst", F.Id("pk")), Call("snd", F.Id("pk"))))))))));

    private static Formula FormulaweakLayerCount() =>
        All("q", Real, All("p", Nat, Equal(Call("weakLayerCount", F.Id("q"), F.Id("p")), Call("ncard", Set("k", Nat, Both(AtMost(D(1), F.Id("k")), Both(Call("Prime", F.Id("p")), AtMost(F.Id("q"), Call("goldenLayerMarginal", F.Id("p"), F.Id("k"))))))))));

    private static Formula Formulaweaklayerseqcountinterval() =>
        All("q", Real, Then(Less(D(0), F.Id("q")), All("p", Nat, Then(Call("Prime", F.Id("p")), Equal(Set("k", Nat, Both(AtMost(D(1), F.Id("k")), Both(Call("Prime", F.Id("p")), AtMost(F.Id("q"), Call("goldenLayerMarginal", F.Id("p"), F.Id("k")))))), Call("Icc", D(1), Call("weakLayerCount", F.Id("q"), F.Id("p"))))))));

    private static Formula FormulaweakLayerExponents() =>
        All("q", Real, All("hq", Less(D(0), F.Id("q")), Equal(Call("weakLayerExponents", F.Id("q"), F.Id("hq")), Call("onFinset", Call("image", Call("fst"), Call("toFinset", Set("pk", NatPair, Both(AtMost(D(1), Call("snd", F.Id("pk"))), Both(Call("Prime", Call("fst", F.Id("pk"))), AtMost(F.Id("q"), Call("goldenLayerMarginal", Call("fst", F.Id("pk")), Call("snd", F.Id("pk"))))))), Call("weakLayersFinite", F.Id("q"), F.Id("hq")))), Lam("p", Nat, Call("weakLayerCount", F.Id("q"), F.Id("p")))))));

    private static Formula FormulamaximalInteger() =>
        All("q", Real, Equal(Call("maximalInteger", F.Id("q")), Case("hq", Less(D(0), F.Id("q")), Call("finsuppProd", Call("weakLayerExponents", F.Id("q"), F.Id("hq")), Lam("p", Nat, Lam("k", Nat, Power(F.Id("p"), F.Id("k"))))), D(1))));

    private static Formula Formulaoptimizerexponentbounds() =>
        All("q", Real, Then(Less(D(0), F.Id("q")), All("n", Nat, Then(AtMost(D(1), F.Id("n")), Then(Call("IsGoldenResourceOptimal", F.Id("q"), F.Id("n")), All("p", Nat, Both(AtMost(Call("optimalLayerCount", F.Id("q"), F.Id("p")), Call("valuation", F.Id("n"), F.Id("p"))), AtMost(Call("valuation", F.Id("n"), F.Id("p")), Call("weakLayerCount", F.Id("q"), F.Id("p"))))))))));

    private static Formula FormulamaximalIntegerspec() =>
        All("q", Real, Then(Less(D(0), F.Id("q")), Both(AtMost(D(1), Call("maximalInteger", F.Id("q"))), Both(All("p", Nat, Equal(Call("valuation", Call("maximalInteger", F.Id("q")), F.Id("p")), Call("weakLayerCount", F.Id("q"), F.Id("p")))), Both(Call("IsGoldenResourceOptimal", F.Id("q"), Call("maximalInteger", F.Id("q"))), All("n", Nat, Then(AtMost(D(1), F.Id("n")), Then(Call("IsGoldenResourceOptimal", F.Id("q"), F.Id("n")), Both(Divides(F.Id("n"), Call("maximalInteger", F.Id("q"))), AtMost(F.Id("n"), Call("maximalInteger", F.Id("q"))))))))))));

    private static Formula FormulamaximalIntegerallties() =>
        All("q", Real, Then(Less(D(0), F.Id("q")), Both(Call("Finite", Set("pk", NatPair, Both(AtMost(D(1), Call("snd", F.Id("pk"))), Both(Call("Prime", Call("fst", F.Id("pk"))), Equal(Call("goldenLayerMarginal", Call("fst", F.Id("pk")), Call("snd", F.Id("pk"))), F.Id("q")))))), All("p", Nat, All("k", Nat, Then(Call("Prime", F.Id("p")), Then(AtMost(D(1), F.Id("k")), Equivalent(Both(Less(Call("valuation", Call("strictInteger", F.Id("q")), F.Id("p")), F.Id("k")), AtMost(F.Id("k"), Call("valuation", Call("maximalInteger", F.Id("q")), F.Id("p")))), Equal(Call("goldenLayerMarginal", F.Id("p"), F.Id("k")), F.Id("q"))))))))));

    private static Formula Formulaprice() =>
        All("x", Real, Equal(Call("price", F.Id("x")), Quotient(D(1), Multiply(F.Id("x"), Call("log", F.Id("x"))))));

    private static Formula Formulaweight() =>
        All("x", Real, Equal(Call("weight", F.Id("x")), Quotient(Add(D(1), Call("log", F.Id("x"))), Multiply(Power(F.Id("x"), D(2)), Power(Call("log", F.Id("x")), D(2))))));

    private static Formula FormulaintegerAt() =>
        All("x", Real, Equal(Call("integerAt", F.Id("x")), Call("strictInteger", Call("price", F.Id("x")))));

    private static Formula Formulaclock() =>
        All("x", Real, Equal(Call("clock", F.Id("x")), Call("log", Call("integerAt", F.Id("x")))));

    private static Formula FormulaW() =>
        All("n", Nat, Equal(Call("W", F.Id("n")), Call("log", Quotient(Call("real", Call("sigma", D(1), F.Id("n"))), Call("real", F.Id("n"))))));

    private static Formula Formulapressure() =>
        All("q", Real, Equal(Call("pressure", F.Id("q")), Call("sSup", Set("v", Real, Ex("n", Nat, Both(AtMost(D(1), F.Id("n")), Equal(F.Id("v"), Call("goldenResourceObjective", F.Id("q"), F.Id("n")))))))));

    private static Formula Formuladefect() =>
        All("a", Real, All("n", Nat, Equal(Call("defect", F.Id("a"), F.Id("n")), Add(Subtract(Call("pressure", Call("price", F.Id("a"))), Call("W", F.Id("n"))), Multiply(Call("price", F.Id("a")), Call("log", F.Id("n")))))));

    private static Formula Formulacompactlayersupport() =>
        All("a", Real, All("b", Real, Then(Less(D(1), F.Id("a")), Then(AtMost(F.Id("a"), F.Id("b")), Ex("S", Call("Finset", NatPair), Both(All("pk", NatPair, Then(Member(F.Id("pk"), F.Id("S")), Both(AtMost(D(1), Call("snd", F.Id("pk"))), Call("Prime", Call("fst", F.Id("pk")))))), All("u", Real, Then(Member(F.Id("u"), Call("Icc", F.Id("a"), F.Id("b"))), All("p", Nat, All("k", Nat, Then(AtMost(D(1), F.Id("k")), Then(Call("Prime", F.Id("p")), Then(AtMost(Call("price", F.Id("u")), Call("goldenLayerMarginal", F.Id("p"), F.Id("k"))), Member(Pair(F.Id("p"), F.Id("k")), F.Id("S")))))))))))))));

    private static Formula Formulaclockmonotone() =>
        All("x", Real, All("y", Real, Then(Less(D(1), F.Id("x")), Then(Less(D(1), F.Id("y")), Then(AtMost(F.Id("x"), F.Id("y")), AtMost(Call("clock", F.Id("x")), Call("clock", F.Id("y"))))))));

    private static Formula Formulapressureeqofoptimal() =>
        All("q", Real, All("n", Nat, Then(AtMost(D(1), F.Id("n")), Then(Call("IsGoldenResourceOptimal", F.Id("q"), F.Id("n")), Equal(Call("pressure", F.Id("q")), Call("goldenResourceObjective", F.Id("q"), F.Id("n")))))));

    private static Formula Formulapressuremaximalspec() =>
        All("q", Real, Then(Less(D(0), F.Id("q")), Both(Call("BddAbove", Set("v", Real, Ex("n", Nat, Both(AtMost(D(1), F.Id("n")), Equal(F.Id("v"), Call("goldenResourceObjective", F.Id("q"), F.Id("n"))))))), Equal(Call("pressure", F.Id("q")), Call("goldenResourceObjective", F.Id("q"), Call("maximalInteger", F.Id("q")))))));

    private static Formula Formulapressureintegral() =>
        All("a", Real, All("b", Real, Then(Less(D(1), F.Id("a")), Then(Less(D(1), F.Id("b")), Equal(Int("u", F.Id("a"), F.Id("b"), Multiply(Call("clock", F.Id("u")), Call("weight", F.Id("u")))), Subtract(Call("pressure", Call("price", F.Id("b"))), Call("pressure", Call("price", F.Id("a")))))))));

    private static Formula Formulatwopriceoriented() =>
        All("x", Real, All("a", Real, Then(Less(D(1), F.Id("x")), Then(Less(D(1), F.Id("a")), Equal(Call("defect", F.Id("a"), Call("integerAt", F.Id("x"))), Int("u", F.Id("x"), F.Id("a"), Multiply(Subtract(Call("clock", F.Id("u")), Call("clock", F.Id("x"))), Call("weight", F.Id("u")))))))));

    private static Formula Formulanpc5oriented() =>
        All("x", Real, Then(Less(D(1), F.Id("x")), Then(Less(D(1), Call("clock", F.Id("x"))), Equal(Call("defect", Call("clock", F.Id("x")), Call("integerAt", F.Id("x"))), Int("u", F.Id("x"), Call("clock", F.Id("x")), Multiply(Subtract(Call("clock", F.Id("u")), Call("clock", F.Id("x"))), Call("weight", F.Id("u"))))))));

    private static Formula Formulanpc5() =>
        All("x", Real, Then(Less(D(1), F.Id("x")), Then(Less(D(1), Call("clock", F.Id("x"))), Equal(Call("defect", Call("clock", F.Id("x")), Call("integerAt", F.Id("x"))), Int("u", Call("min", F.Id("x"), Call("clock", F.Id("x"))), Call("max", F.Id("x"), Call("clock", F.Id("x"))), Multiply(Absolute(Subtract(Call("clock", F.Id("u")), Call("clock", F.Id("x")))), Call("weight", F.Id("u"))))))));

    private static Formula Formulanpc5anycomparisonoptimizer() =>
        All("x", Real, Then(Less(D(1), F.Id("x")), Then(Less(D(1), Call("clock", F.Id("x"))), All("C", Nat, Then(AtMost(D(1), F.Id("C")), Then(Call("IsGoldenResourceOptimal", Call("price", Call("clock", F.Id("x"))), F.Id("C")), Equal(Subtract(Call("goldenResourceObjective", Call("price", Call("clock", F.Id("x"))), F.Id("C")), Call("goldenResourceObjective", Call("price", Call("clock", F.Id("x"))), Call("integerAt", F.Id("x")))), Int("u", Call("min", F.Id("x"), Call("clock", F.Id("x"))), Call("max", F.Id("x"), Call("clock", F.Id("x"))), Multiply(Absolute(Subtract(Call("clock", F.Id("u")), Call("clock", F.Id("x")))), Call("weight", F.Id("u")))))))))));

}
