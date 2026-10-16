using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class DisorderedExclusionQuadraticResponseRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/StatisticalMechanics/DisorderedExclusionQuadraticResponseRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/sakaiakimoto2026currentresponse");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A four-site exclusion ring has zero quadratic current response despite failing both proposed rate-symmetry conditions.",
        H("Vanishing quadratic response without either rate symmetry"), Blocks(
            Paragraph(Text(
                "The sites form Fin L, the residues 0 through L − 1, with addition and subtraction modulo L. "
                    + "A configuration is a finite subset of occupied sites; at most one particle occupies a site. "
                    + "Finset.card counts occupied sites, Finset.erase removes a site, and insert adds one. "
                    + "Sums and products with a displayed type range over every element of that finite type; "
                    + "a sum over i in s ranges only over the occupied sites. The anonymous assumption [NeZero L] "
                    + "requires L to be nonzero. The rates wp and wm and all probabilities are real-valued. "
                    + "The definitions allow arbitrary real bias; positive hopping rates describe the exclusion "
                    + "process when wp and wm are positive and −1 < ε < 1.")),
            Node("p", "Rightward hopping rates", RightRateFormula(),
                "Equation (1) multiplies the rightward trap or bond rate wp(i) by (1 + ε)/2. "
                    + "A positive ε favours hopping from i to i + 1."),
            Node("q", "Leftward hopping rates", LeftRateFormula(),
                "Equation (1) multiplies the leftward rate wm(i) by (1 − ε)/2. "
                    + "A particle at i attempts a hop to i − 1 with this rate."),
            Node("rate", "Transitions between exclusion configurations", TransitionFormula(),
                "Each occupied site contributes its rightward and leftward rates precisely when the destination "
                    + "is empty and moving that particle produces t. The two contributions are added, "
                    + "including when both directions lead to the same configuration. These are the "
                    + "single-particle transitions of the exclusion ring in Section II."),
            Node("IsStationary", "The stationary probability law", StationaryFormula(),
                "A stationary law vanishes outside configurations with N particles, is nonnegative everywhere, "
                    + "and has total mass one. For every target configuration t, the incoming probability flux "
                    + "equals the outgoing flux. Both balance sums range over all finite subsets of the ring. "
                    + "This gives the finite-state stationary law for the dynamics of Section II."),
            Node("current", "Current across the bond from 0 to 1", CurrentFormula(),
                "The expectation of the rightward hopping rate minus the leftward hopping rate gives the "
                    + "current across the bond (0,1). A hop contributes only when its origin is occupied "
                    + "and its destination is empty. Under a stationary law this is the bond current of "
                    + "equation (2), written as the occupation-probability expression in Appendix C, equation (C1)."),
            Node("BondRatioUniform", "Condition (i): the same ratio on every bond", UniformRatioFormula(),
                "The bond-bias ratio of equation (5) is p(wp,ε,i)/q(wm,ε,i + 1). "
                    + "Condition (i) in Section III.D requires equality of these ratios for every pair of "
                    + "sites at every bias strictly between −1 and 1."),
            Node("InversionCorrespondence", "Condition (ii): inversion and bias reversal", InversionFormula(),
                "Condition (ii) in Section III.D and Appendix C uses one centre k for the whole ring. "
                    + "For each site offset i, either the reflected site k − i or the shifted reflected site "
                    + "k − i + 1 has the matching leftward rate at reversed bias. The choice may depend on i, "
                    + "but each chosen equality must hold for every real ε."),
            Node("claim", "The proposed nonzero quadratic coefficient", ClaimFormula(),
                "Section III.D conjectures an ε² contribution whenever neither condition (i) nor condition (ii) "
                    + "holds. Here the statement is restricted to at least two particles and at least two holes; "
                    + "Section III.F already gives an odd current for a single particle. The rates are positive "
                    + "and their two products agree, expressing the unbiased equilibrium constraint of Section II. "
                    + "For every positive δ and every family π that is the unique stationary law for |ε| < δ, "
                    + "every quadratic expansion of its current must have c₂ nonzero. Asymptotics.IsLittleO "
                    + "at nhds(0) means that the remainder is o(ε²) as the real bias tends to zero; "
                    + "the two displayed lambda expressions are functions of that bias.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("disordered-exclusion-quadratic-response-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Four trap sites with a zero quadratic coefficient"),
                StatementSource.FromAuthor(Disp(Not(Q("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take L = 4 and N = 2, and give both directions the trap rates (2,4,3,41) "
                            + "at sites 0,1,2,3. The rates are positive and their products agree. At ε = 0, "
                            + "the ratios across the first two bonds are 1/2 and 4/3, so condition (i) fails. "
                            + "For any centre k, the offset i = 1 compares the rate at k + 1 with the rates "
                            + "at k − 1 and k. These three sites are distinct modulo 4 and all four trap rates "
                            + "are distinct. Thus neither alternative is possible at ε = 0, and condition (ii) fails.")),
                    Paragraph(Text(
                        "For |ε| < 1/100, the stationary probabilities on the ordered configurations "
                            + "({0,1},{0,2},{0,3},{1,2},{1,3},{2,3}) are the following six entries divided by "
                            + "5(223175 + 17022ε² − 1628ε³ − 114725ε⁴ + 1628ε⁵): "
                            + "123(2825 − 1612ε + 390ε² + 1256ε³ − 1695ε⁴ + 148ε⁵), "
                            + "164(2825 + 518ε − 928ε² − 370ε³ − 1033ε⁴ − 148ε⁵), "
                            + "12(2825 + 5608ε + 4830ε² + 3036ε³ + 1265ε⁴ + 148ε⁵), "
                            + "82(2825 + 1008ε + 1150ε² − 1564ε³ − 2415ε⁴ + 148ε⁵), "
                            + "6(2825 − 222ε + 2672ε² + 370ε³ − 2873ε⁴ − 148ε⁵), and "
                            + "8(2825 − 4412ε + 2630ε² − 1544ε³ + 545ε⁴ + 148ε⁵). "
                            + "The law is zero on all other configurations. The six numerators sum to the "
                            + "denominator and satisfy the balance equations. They and the denominator are "
                            + "positive on this interval. The balance equations together with total mass one "
                            + "determine these probabilities uniquely.")),
                    Paragraph(Text(
                        "The resulting bond current is "
                            + "7872ε(25 + 9ε² − 16ε⁴)/(223175 + 17022ε² − 1628ε³ − 114725ε⁴ + 1628ε⁵). "
                            + "Its linear coefficient is 7872/8927 and its quadratic coefficient is zero: "
                            + "subtracting (7872/8927)ε leaves ε³ times a function continuous at zero, "
                            + "hence a remainder o(ε²). Its ε⁴ coefficient is 7872·25·1628/223175², "
                            + "which is positive, so the current is not odd. The vanishing quadratic term "
                            + "therefore does not require either rate condition and does not imply bias-reversal symmetry."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sakai-akimoto-2026-disordered-exclusion-quadratic-response"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance? provenance = null) => Describe.Lean(
            DescribeId.Create("disordered-exclusion-quadratic-response-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => name switch
    {
        "epsilon" => Varepsilon,
        "mu" => Mu,
        "pi" => Pi,
        "delta" => DeltaLower,
        "c1" => new Formula.Subscript(F.Id("c"), D(1)),
        "c2" => new Formula.Subscript(F.Id("c"), D(2)),
        _ => F.Id(name),
    };
    private static Formula Q(string name)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Q(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Sites() => Call("Fin", V("L"));
    private static Formula Configurations() => Call("Finset", Sites());
    private static Formula SiteRates() => Arrow(Sites(), Real());
    private static Formula Laws() => Arrow(Configurations(), Real());
    private static Formula Size(Formula body) => All("L", Nat(), body);
    private static Formula RingSize(Formula body) => Size(Instance(Call("NeZero", V("L")), body));
    private static Formula Rates(Formula body) => All("wp", SiteRates(), All("wm", SiteRates(), body));
    private static Formula Bias(Formula body) => All("epsilon", Real(), body);
    private static Formula P(Formula site) => Call("p", V("wp"), V("epsilon"), site);
    private static Formula LeftRate(Formula bias, Formula site) => Call("q", V("wm"), bias, site);
    private static Formula R(Formula from, Formula to) => Call("rate", V("wp"), V("wm"), V("epsilon"), from, to);
    private static Formula Stationary(Formula law) => Call("IsStationary", V("N"), V("wp"), V("wm"), V("epsilon"), law);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(V(name), type)), Sp, Parenthesized(body));
    private static Formula SumIn(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Member(V(name), set)), Sp, Parenthesized(body));
    private static Formula Product(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Prod, Typed(V(name), type)), Sp, Parenthesized(body));
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Parenthesized(Seq(Q("if"), Sp, Parenthesized(condition), Sp, Q("then"), Sp,
            Parenthesized(yes), Sp, Q("else"), Sp, Parenthesized(no)));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessEq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula value, Formula set) => new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Not(Formula value) => new Formula.Not(Parenthesized(value));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula RightRateFormula() => Size(All("wp", SiteRates(), Bias(All("i", Sites(),
        Equal(P(V("i")), Multiply(new Formula.Fraction(Add(D(1), V("epsilon")), D(2)), At(V("wp"), V("i"))))))));

    private static Formula LeftRateFormula() => Size(All("wm", SiteRates(), Bias(All("i", Sites(),
        Equal(LeftRate(V("epsilon"), V("i")),
            Multiply(new Formula.Fraction(Subtract(D(1), V("epsilon")), D(2)), At(V("wm"), V("i"))))))));

    private static Formula TransitionFormula()
    {
        var next = Add(V("i"), D(1));
        var previous = Subtract(V("i"), D(1));
        var erased = Call("Finset.erase", V("s"), V("i"));
        var right = Conditional(And(Not(Member(next, V("s"))), Equal(V("t"), Call("insert", next, erased))),
            P(V("i")), D(0));
        var left = Conditional(And(Not(Member(previous, V("s"))), Equal(V("t"), Call("insert", previous, erased))),
            LeftRate(V("epsilon"), V("i")), D(0));
        return RingSize(Rates(Bias(All("s", Configurations(), All("t", Configurations(),
            Equal(R(V("s"), V("t")), SumIn("i", V("s"), Add(right, left))))))));
    }

    private static Formula StationaryFormula()
    {
        var support = All("s", Configurations(),
            Imp(NotEqual(Call("Finset.card", V("s")), V("N")), Equal(At(V("mu"), V("s")), D(0))));
        var positive = All("s", Configurations(), LessEq(D(0), At(V("mu"), V("s"))));
        var normalized = Equal(SumOver("s", Configurations(), At(V("mu"), V("s"))), D(1));
        var balance = All("t", Configurations(),
            Equal(SumOver("s", Configurations(), Multiply(At(V("mu"), V("s")), R(V("s"), V("t")))),
                Multiply(At(V("mu"), V("t")), SumOver("s", Configurations(), R(V("t"), V("s"))))));
        return RingSize(All("N", Nat(), Rates(Bias(All("mu", Laws(),
            IffOf(Stationary(V("mu")), And(support, And(positive, And(normalized, balance)))))))));
    }

    private static Formula CurrentFormula()
    {
        var right = Conditional(And(Member(D(0), V("s")), Not(Member(D(1), V("s")))), P(D(0)), D(0));
        var left = Conditional(And(Member(D(1), V("s")), Not(Member(D(0), V("s")))),
            LeftRate(V("epsilon"), D(1)), D(0));
        return RingSize(Rates(Bias(All("mu", Laws(),
            Equal(Call("current", V("wp"), V("wm"), V("epsilon"), V("mu")),
                SumOver("s", Configurations(), Multiply(At(V("mu"), V("s")), Subtract(right, left))))))));
    }

    private static Formula UniformRatioFormula()
    {
        var ratios = Equal(new Formula.Fraction(P(V("i")), LeftRate(V("epsilon"), Add(V("i"), D(1)))),
            new Formula.Fraction(P(V("j")), LeftRate(V("epsilon"), Add(V("j"), D(1)))));
        return RingSize(Rates(IffOf(Call("BondRatioUniform", V("wp"), V("wm")),
            Bias(Imp(Less(new Formula.Negate(D(1)), V("epsilon")), Imp(Less(V("epsilon"), D(1)),
                All("i", Sites(), All("j", Sites(), ratios))))))));
    }

    private static Formula InversionFormula()
    {
        var right = P(Add(V("k"), V("i")));
        var reversed = new Formula.Negate(V("epsilon"));
        var reflected = Subtract(V("k"), V("i"));
        var alternatives = Or(Bias(Equal(right, LeftRate(reversed, reflected))),
            Bias(Equal(right, LeftRate(reversed, Add(reflected, D(1))))));
        return RingSize(Rates(IffOf(Call("InversionCorrespondence", V("wp"), V("wm")),
            Some("k", Sites(), All("i", Sites(), alternatives)))));
    }

    private static Formula ClaimFormula()
    {
        var law = At(V("pi"), V("epsilon"));
        var uniqueLaw = Bias(Imp(Less(Seq(Lvert, V("epsilon"), Rvert), V("delta")),
            And(Stationary(law), All("mu", Laws(), Imp(Stationary(V("mu")), Equal(V("mu"), law))))));
        var remainder = Subtract(Subtract(Call("current", V("wp"), V("wm"), V("epsilon"), law),
            Multiply(V("c1"), V("epsilon"))), Multiply(V("c2"), Square(V("epsilon"))));
        var expansion = Call("Asymptotics.IsLittleO", Call("nhds", Typed(D(0), Real())),
            LambdaOf("epsilon", Real(), remainder), LambdaOf("epsilon", Real(), Square(V("epsilon"))));
        var coefficients = All("c1", Real(), All("c2", Real(), Imp(expansion, NotEqual(V("c2"), D(0)))));
        var families = All("delta", Real(), Imp(Less(D(0), V("delta")),
            All("pi", Arrow(Real(), Laws()), Imp(uniqueLaw, coefficients))));
        Formula body = Imp(All("i", Sites(), And(Less(D(0), At(V("wp"), V("i"))), Less(D(0), At(V("wm"), V("i"))))),
            Imp(Equal(Product("i", Sites(), At(V("wm"), V("i"))), Product("i", Sites(), At(V("wp"), V("i")))),
                Imp(Not(Call("BondRatioUniform", V("wp"), V("wm"))),
                    Imp(Not(Call("InversionCorrespondence", V("wp"), V("wm"))), families))));
        body = Instance(Call("NeZero", V("L")),
            Imp(LessEq(D(2), V("N")), Imp(LessEq(Add(V("N"), D(2)), V("L")), Rates(body))));
        return IffOf(Q("claim"), Size(All("N", Nat(), body)));
    }
}
