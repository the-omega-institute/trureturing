using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class GlobalGcdSamplingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/GlobalGcdSampling.";
    private static Formula Natural => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integer => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula State => Seq(Integer, Times, Integer);
    private static Formula PrimeRing => Call("ZMod", F.Id("p"));
    private static Formula ParentExponent => Sub(F.Id("e"), D(1));
    private static Formula ParentRank => Rank(Pow(F.Id("p"), ParentExponent));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual sparse phase criterion identifies all signed and actual natural gcd futures; its failure produces fixed signed and bounded natural collisions on the complete query table.",
        H("Actual Fibonacci Sparse Child Law"),
        Blocks(
            Paragraph(Text("N includes zero. Integer division ediv and natural division ndiv are the corresponding Lean quotient operations. "
                + "F(0)=0 and F(1)=1. The function r(m) is TimeSampling.zeroRank(m), the natural infimum of the positive Fibonacci zero indices modulo m. "
                + "The infimum is zero when that set is empty; the proof reuses verified nonemptiness for every positive prime power. "
                + "Coordinates of x in Z times Z are x_1 and x_2. The value y(k,x) is the actual signed recurrence observation for positive k. "
                + "All queried observations are positive-time readings. Capped-content divisibility also holds at index zero, without supplying a time-zero reading. "
                + "ZMod(m) denotes Z/mZ, with ZMod(0)=Z. In formulas involving this ring, integers and natural numbers are coerced into it. "
                + "In particular A and B take values in ZMod(p); c and f take values in ZMod(p^e). "
                + "The proof-local inverse of c is the ZMod inverse; the affine calculation proves c is a unit for prime p and e>=2. "
                + "For a in ZMod(p), val(a) is its canonical natural representative. castZMod(r,n) is the natural coercion into ZMod(r). "
                + "Finset denotes finite sets of distinct values.")),
            Node("signedValue", "Positive-time signed observation", Disp(
                All(Natural, ["k"], All(State, ["x"], Equal(Value(F.Id("k"), "x"),
                    Add(Mul(Call("F", Sub(F.Id("k"), D(1))), Coordinate("x", 1)),
                        Mul(Call("F", F.Id("k")), Coordinate("x", 2))))))),
                "Subtraction on the natural index is truncated. Only positive indices are used by the theorem.", DescribeRole.Definition),
            Node("Primitive", "Prime-local primitive state", Disp(
                All(Natural, ["p"], All(State, ["x"], IffFormula(Primitive("x"),
                    Or(Not(Divides(F.Id("p"), Coordinate("x", 1))),
                        Not(Divides(F.Id("p"), Coordinate("x", 2)))))))),
                "At least one signed coordinate is not divisible by p; integer coprimality of the coordinates is not required.", DescribeRole.Definition),
            Node("gcdValue", "Complete signed gcd answer", Disp(
                All(Natural, ["H", "k"], All(State, ["x"], Equal(Gcd(F.Id("H"), F.Id("k"), "x"),
                    Call("gcd", Call("natAbs", Value(F.Id("k"), "x")), F.Id("H")))))),
                "The answer includes the zero signed observation and uses its natural absolute value.", DescribeRole.Definition),
            Node("actualGcd", "Actual forward-source gcd answer", Disp(
                All(Natural, ["H", "k"], All(NaturalState, ["v"], Equal(Actual(F.Id("H"), F.Id("k"), "v"),
                    Call("gcd", Call("quantity", Call("stepIterate", F.Id("k"), F.Id("v"))), F.Id("H")))))),
                "The imported step is (a,b) maps to (b,a+b), quantity is 2a+3b, and stepIterate(k,v) is k forward steps. "
                + "Thus this is the actual qM^k source observation, not an independently chosen list of residues.", DescribeRole.Definition),
            Node("cappedContent", "Unknown capped common content", Disp(
                All(Natural, ["p", "e"], All(State, ["x"], Equal(Content("x"),
                    Call("gcd", Call("gcd", Call("natAbs", Coordinate("x", 1)), Call("natAbs", Coordinate("x", 2))), Pow(F.Id("p"), F.Id("e"))))))),
                "The natural capped common divisor includes the zero pair. minGcdTable(P,S,x) denotes the minimum of g(P,k,x) over k in the nonempty S.", DescribeRole.Definition),
            Node("rootBase", "Actual affine root base", Disp(
                All(Natural, ["p", "e", "t"], All(State, ["x"], Equal(Base("x"),
                    Mul(Call("natCast", Call("F", Sub(ParentRank, D(1))), PrimeRing),
                        Call("intCast", Call("ediv", Value(Add(F.Id("t"), D(1)), "x"),
                            Pow(F.Id("p"), ParentExponent)), PrimeRing)))))),
                "The signed quotient is taken before coercion to ZMod(p).", DescribeRole.Definition),
            Node("rootSlope", "Actual affine root slope", Disp(
                All(Natural, ["p", "e", "t"], All(State, ["x"], Equal(Slope("x"),
                    Mul(Call("natCast", Call("ndiv", Call("F", ParentRank),
                        Pow(F.Id("p"), ParentExponent)), PrimeRing),
                        Call("intCast", Value(Add(F.Id("t"), D(2)), "x"), PrimeRing)))))),
                "The Fibonacci quotient is natural division before coercion to ZMod(p).", DescribeRole.Definition),
            Node("queryChildren", "Queried children in a shifted parent phase", Disp(QueryFormula()),
                "A child belongs exactly when some positive-table query has its top residue. The finite image of range(p) supplies all residues for p>0; repeated visits count once. "
                + "The child formula uses k-1 at the terminal rank.", DescribeRole.Definition),
            Node("D", "Actual terminal phase coverage", Disp(CoverageFormula()),
                "At the first layer, the full-orbit case allows one missing phase, whereas the optional-hit case requires every phase. "
                + "At a higher stagnant layer every phase is required. At a growth layer each parent requires at least p-1 distinct children. "
                + "These are conditions on actual phase images, not on the number of query times.", DescribeRole.Definition),
            Node("Identifies", "Same-table positive-future identification", Disp(IdentificationFormula()),
                "The source type A is a Type, read maps N times A to N, and S is a finite set of natural times. "
                + "The implication compares the same two fixed sources at every queried time and every positive future time.", DescribeRole.Definition),
            Node("IdentifiesOn", "Domain-restricted positive-future identification", Disp(IdentificationFormula(true)),
                "Both sources satisfy the same domain predicate; table and future still concern the same fixed pair.", DescribeRole.Definition),
            Node("sparse_gcd_sampling", "Affine child decoding and complete-answer collisions", Disp(ResultFormula()),
                "For every finite positive query table failing D, two fixed primitive signed states agree on every complete gcd reading in that table. "
                + "The states are chosen before Q. For each Q>0, two actual natural sources are then fixed before every late cutoff. "
                + "Both coordinates are below Qp^e, and every positive-time natural answer is exactly Q times its signed answer, including when p divides Q. "
                + "Source primitiveness is asserted only when p does not divide Q. The late separating answers are p^e and p^(e-1), and Qp^e and Qp^(e-1). "
                + "At growth, the actual square-zero Fibonacci block calculation decodes affine child hits; inverse-action kernel states realize the two omitted children. "
                + "At stagnation an inverse-action state exits permanently at the top precision while retaining the lower supports. "
                + "The same-table minimum recovers capped content whenever two distinct first-layer phases are queried, including zero and saturation. "
                + "At precision e>=2, terminal coverage also represents every phase at each precision 1<=j<e, after any simultaneous translation in its rank ring. "
                + "At every positive precision, D identifies the entire positive-time gcd future of any two signed states and any two actual natural sources from their same-table readings, including zero, saturation, and unknown nonprimitive content. "
                + "The shared actual affine law gives a mandatory unique child hit whenever the slope is nonzero, including p=2. "
                + "A complement of at most one child forces the two roots to agree, and phase transport handles arbitrary positive query times and parent wrap. "
                + "Equal lower-precision future readings determine whether the two slopes vanish. In the zero-slope case, one queried child determines the constant affine hit condition. "
                + "The actual C coordinates and frozen whole-time source transport transfer the signed result to natural sources. "
                + "For every exact local factor p^e || H, failure of D yields a p-unit quotient H/p^e and bounded actual sources whose complete H-table agrees before a late H versus H/p separation. "
                + "For every H>0, the same positive table identifies all actual natural futures exactly when D holds at every complete prime-power factor of H. "
                + "The proof projects each full gcd answer to its local gcd, then recombines the nonzero gcd readings by unique factorization; raw observations need not be nonzero. "
                + "At H=1 every reading is one, including zero sources and time zero, and the empty table identifies all positive futures. "
                + "The terminal condition itself gives a nonempty S with two distinct first-layer phases, and its local minimum recovers capped common content on that same S. "
                + "The terminal condition, its conjunction with every lower-level condition, primitive signed identification, all signed identification, "
                + "all actual-natural identification, and primitive actual-natural identification are equivalent on the same positive S. "
                + "For every prime p, e>=2, signed x and natural parent t, divisibility of y(t+1,x) by p^(e-1) implies "
                + "that the top hit at t+1+j r(p^(e-1)) is equivalent to A(p,e,t,x)+j B(p,e,t,x)=0 in ZMod(p), for every natural j. "
                + "This native normalized affine law is shared by the sufficiency and fixed-collision proofs. "
                + "On every sufficient positive table, the minimum of actual-natural local readings equals gcd(gcd(v_1,v_2),p^e), "
                + "by the same signed minimum and the frozen gcd-preserving C observation. This includes zero sources and saturation. "
                + "minActualGcdTable(P,S,v) denotes the numerical minimum of gActual(P,k,v) over nonempty S. "
                + "This closed unit asserts the sparse criterion, fixed collisions, affine decoding and local content recovery; "
                + "sharp horizon, query cardinality, common exponent, global content meet and phase-carry formulas are outside this theorem.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create("global-gcd-sampling-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Pow(Formula value, Formula exponent) => Seq(Par(value), Caret, Grp(exponent));
    private static Formula Add(Formula first, Formula second) => Seq(first, Plus, second);
    private static Formula Sub(Formula first, Formula second) => Seq(first, Minus, second);
    private static Formula Mul(Formula first, Formula second) => Seq(Par(first), Sp, Par(second));
    private static Formula Equal(Formula first, Formula second) => Seq(first, Sp, Eq, Sp, second);
    private static Formula Divides(Formula first, Formula second) => Seq(first, Sp, Mid, Sp, second);
    private static Formula Not(Formula value) => Seq(Neg, Par(value));
    private static Formula Or(Formula first, Formula second) => Seq(Par(first), Sp, Lor, Sp, Par(second));
    private static Formula Imply(Formula first, Formula second) => Seq(Par(first), Sp, Implies, Sp, Par(second));
    private static Formula IffFormula(Formula first, Formula second) => Seq(Par(first), Sp, Leftrightarrow, Sp, Par(second));
    private static Formula All(Formula type, string[] names, Formula value) => Quant(Forall, type, names, value);
    private static Formula Some(Formula type, string[] names, Formula value) => Quant(Exists, type, names, value);
    private static Formula Quant(Formula quantifier, Formula type, string[] names, Formula value)
    {
        for (int index = names.Length - 1; index >= 0; index--)
            value = Seq(quantifier, Sp, F.Id(names[index]), Colon, type, Comma, Sp, Par(value));
        return value;
    }
    private static Formula And(params Formula[] values)
    {
        Formula value = values[^1];
        for (int index = values.Length - 2; index >= 0; index--)
            value = Seq(Par(values[index]), Sp, Land, Sp, Par(value));
        return value;
    }
    private static Formula Coordinate(string name, byte coordinate) => Seq(F.Id(name), Underscore, Grp(D(coordinate)));
    private static Formula Value(Formula time, string state) => Call("y", time, F.Id(state));
    private static Formula Rank(Formula modulus) => Call("r", modulus);
    private static Formula Primitive(string state) => Call("Primitive", F.Id("p"), F.Id(state));
    private static Formula Base(string state) => Call("A", F.Id("p"), F.Id("e"), F.Id("t"), F.Id(state));
    private static Formula Slope(string state) => Call("B", F.Id("p"), F.Id("e"), F.Id("t"), F.Id(state));
    private static Formula Bound(byte lower, Formula value) => Seq(D(lower), Sp, Le, Sp, value);
    private static Formula Val(string name) => Call("val", F.Id(name));
    private static Formula NaturalState => Seq(Natural, Sp, Times, Sp, Natural);
    private static Formula Mod(Formula value, Formula modulus) => Call("mod", value, modulus);
    private static Formula Gcd(Formula modulus, Formula time, string state) => Call("g", modulus, time, F.Id(state));
    private static Formula Content(string state) => Call("content", F.Id("p"), F.Id("e"), F.Id(state));
    private static Formula Actual(Formula modulus, Formula time, string state) => Call("gActual", modulus, time, F.Id(state));
    private static Formula Less(Formula first, Formula second) => Seq(first, Sp, Lt, Sp, second);
    private static Formula MemberS(Formula value) => Seq(value, Sp, InMacro, Sp, F.Id("S"));
    private static Formula TotalModulus => Mul(F.Id("Q"), Pow(F.Id("p"), F.Id("e")));
    private static Formula SourceBounds(string state) => And(Less(Coordinate(state, 1), TotalModulus), Less(Coordinate(state, 2), TotalModulus));
    private static Formula SourcePrimitive(string state) => Or(Not(Divides(F.Id("p"), Coordinate(state, 1))), Not(Divides(F.Id("p"), Coordinate(state, 2))));
    private static Formula P => F.Id("p");
    private static Formula E => F.Id("e");
    private static Formula Hmod => F.Id("H");
    private static Formula K => F.Id("k");
    private static Formula S => F.Id("S");
    private static Formula PrimePower => Pow(P, E);
    private static Formula FirstRank => Rank(P);
    private static Formula Children => Call("queryChildren", P, E, F.Id("t"), S);
    private static Formula Coverage(Formula exponent) => Call("D", P, exponent, S);
    private static Formula PositiveTable => All(Natural, ["k"], Imply(MemberS(K), Less(D(0), K)));
    private static Formula Table(bool actual, Formula modulus) => All(Natural, ["k"], Imply(MemberS(K), Equal(
        actual ? Actual(modulus, K, "v") : Gcd(modulus, K, "x"),
        actual ? Actual(modulus, K, "w") : Gcd(modulus, K, "y"))));
    private static Formula ShiftedPhase => Mod(Sub(K, D(1)), Rank(PrimePower));
    private static Formula ChildPhase => Mod(Add(F.Id("t"), Mul(Val("a"), ParentRank)), Rank(PrimePower));

    private static Formula QueryFormula() => All(Natural, ["p", "e", "t"], All(Call("Finset", Natural), ["S"],
        All(PrimeRing, ["a"], IffFormula(Seq(F.Id("a"), Sp, InMacro, Sp, Children),
            And(Some(Natural, ["j"], And(Less(F.Id("j"), P), Equal(F.Id("a"), Call("natCast", F.Id("j"))))),
                Some(Natural, ["k"], And(MemberS(K), Equal(ShiftedPhase, ChildPhase))))))));

    private static Formula CoverageFormula()
    {
        Formula phaseImage = Call("image", Seq(K, Sp, Mapsto, Sp, Mod(K, FirstRank)), S);
        Formula first = Seq(Call("if", Equal(FirstRank, Add(P, D(1))), Sub(FirstRank, D(1)), FirstRank),
            Sp, Le, Sp, Call("card", phaseImage));
        Formula stagnant = All(Natural, ["t"], Imply(Less(F.Id("t"), Rank(PrimePower)),
            Some(Natural, ["k"], And(MemberS(K), Equal(ShiftedPhase, F.Id("t"))))));
        Formula growth = All(Natural, ["t"], Imply(Less(F.Id("t"), ParentRank),
            Seq(Sub(P, D(1)), Sp, Le, Sp, Call("card", Children))));
        return All(Natural, ["p", "e"], All(Call("Finset", Natural), ["S"], IffFormula(Coverage(E),
            Call("if", Equal(E, D(1)), first,
                Call("if", Equal(Rank(PrimePower), ParentRank), stagnant, growth)))));
    }

    private static Formula IdentificationFormula(bool restricted = false)
    {
        Formula source = F.Id("A");
        Formula readType = Seq(Natural, Sp, To, Sp, source, Sp, To, Sp, Natural);
        Formula read = F.Id("read");
        Formula table = All(Natural, ["k"], Imply(MemberS(K),
            Equal(new Formula.Apply(read, [K, F.Id("x")]), new Formula.Apply(read, [K, F.Id("y")]))));
        Formula future = All(Natural, ["k"], Imply(Less(D(0), K),
            Equal(new Formula.Apply(read, [K, F.Id("x")]), new Formula.Apply(read, [K, F.Id("y")]))));
        Formula implication = Imply(table, future);
        if (restricted)
            implication = Imply(And(new Formula.Apply(F.Id("domain"), [F.Id("x")]),
                new Formula.Apply(F.Id("domain"), [F.Id("y")])), implication);
        Formula predicate = restricted ? Call("IdentifiesOn", F.Id("domain"), read, S) : Call("Identifies", read, S);
        Formula formula = All(readType, ["read"], All(Call("Finset", Natural), ["S"],
            IffFormula(predicate, All(source, ["x", "y"], implication))));
        if (restricted)
            formula = All(Seq(source, Sp, To, Sp, F.Id("Prop")), ["domain"], formula);
        return All(F.Id("Type"), ["A"], formula);
    }

    private static Formula LocalFormula()
    {
        Formula lower = Pow(P, ParentExponent);
        Formula whole = All(Natural, ["k"], Imply(Less(D(0), K), And(
            Equal(Actual(TotalModulus, K, "v"), Mul(F.Id("Q"), Gcd(PrimePower, K, "x"))),
            Equal(Actual(TotalModulus, K, "w"), Mul(F.Id("Q"), Gcd(PrimePower, K, "y"))))));
        Formula late = All(Natural, ["B"], Some(Natural, ["k"], And(Less(F.Id("B"), K), Less(D(0), K), Not(MemberS(K)),
            Equal(Gcd(PrimePower, K, "x"), PrimePower), Equal(Gcd(PrimePower, K, "y"), lower),
            Equal(Actual(TotalModulus, K, "v"), TotalModulus), Equal(Actual(TotalModulus, K, "w"), Mul(F.Id("Q"), lower)))));
        Formula natural = All(Natural, ["Q"], Imply(Less(D(0), F.Id("Q")), Some(NaturalState, ["v", "w"], And(
            SourceBounds("v"), SourceBounds("w"), Imply(Not(Divides(P, F.Id("Q"))), And(SourcePrimitive("v"), SourcePrimitive("w"))),
            whole, Table(true, TotalModulus), late))));
        Formula failed = All(Natural, ["e"], Imply(Bound(1, E), All(Call("Finset", Natural), ["S"],
            Imply(PositiveTable, Imply(Not(Coverage(E)), Some(State, ["x", "y"],
                And(Primitive("x"), Primitive("y"), Table(false, PrimePower), natural)))))));
        Formula distinct = Some(Natural, ["s", "t"], And(MemberS(F.Id("s")), MemberS(F.Id("t")),
            Not(Equal(Mod(F.Id("s"), FirstRank), Mod(F.Id("t"), FirstRank)))));
        Formula minimum = All(Natural, ["e"], Imply(Bound(1, E), All(Call("Finset", Natural), ["S"],
            Imply(Call("Nonempty", S), Imply(PositiveTable, Imply(distinct, All(State, ["x"],
                Equal(Call("minGcdTable", PrimePower, S, F.Id("x")), Content("x")))))))));
        Formula lowerRank = Rank(Pow(P, F.Id("j")));
        Formula lowerPrecision = All(Natural, ["e"], Imply(Bound(2, E),
            All(Call("Finset", Natural), ["S"], Imply(Coverage(E), All(Natural, ["j"],
                Imply(And(Bound(1, F.Id("j")), Less(F.Id("j"), E)),
                    All(Call("ZMod", lowerRank), ["a", "b"], Some(Natural, ["k"],
                        And(MemberS(K), Equal(Add(Call("castZMod", lowerRank, Sub(K, D(1))),
                            F.Id("a")), F.Id("b")))))))))));
        Formula signedRestricted = All(State, ["x", "y"], Imply(And(Primitive("x"), Primitive("y")),
            Imply(Table(false, PrimePower), All(Natural, ["k"], Imply(Less(D(0), K),
                Equal(Gcd(PrimePower, K, "x"), Gcd(PrimePower, K, "y")))))));
        Formula naturalRestricted = All(NaturalState, ["v", "w"], Imply(And(SourcePrimitive("v"), SourcePrimitive("w")),
            Imply(Table(true, PrimePower), All(Natural, ["k"], Imply(Less(D(0), K),
                Equal(Actual(PrimePower, K, "v"), Actual(PrimePower, K, "w")))))));
        Formula tower = And(Coverage(E), All(Natural, ["j"],
            Imply(And(Bound(1, F.Id("j")), Less(F.Id("j"), E)), Coverage(F.Id("j")))));
        Formula equivalence = All(Natural, ["e"], Imply(Bound(1, E),
            All(Call("Finset", Natural), ["S"], Imply(PositiveTable, And(
                IffFormula(Coverage(E), tower), IffFormula(Coverage(E), signedRestricted),
                IffFormula(Coverage(E), Call("Identifies", Call("gcdValue", PrimePower), S)),
                IffFormula(Coverage(E), Call("Identifies", Call("actualGcd", PrimePower), S)),
                IffFormula(Coverage(E), naturalRestricted))))));
        Formula factorLate = All(Natural, ["B"], Some(Natural, ["k"], And(
            Less(F.Id("B"), K), Less(D(0), K), Not(MemberS(K)),
            Equal(Actual(Hmod, K, "v"), Hmod), Equal(Actual(Hmod, K, "w"), Call("div", Hmod, P)))));
        Formula factorSources = Some(NaturalState, ["v", "w"], And(
            Less(Coordinate("v", 1), Hmod), Less(Coordinate("v", 2), Hmod),
            Less(Coordinate("w", 1), Hmod), Less(Coordinate("w", 2), Hmod),
            Table(true, Hmod), factorLate));
        Formula factorConclusion = And(Not(Divides(P, Call("div", Hmod, PrimePower))), factorSources);
        Formula completeFactor = And(Less(D(0), Hmod), Divides(PrimePower, Hmod),
            Not(Divides(Pow(P, Add(E, D(1))), Hmod)));
        Formula factorFailure = All(Natural, ["e"], Imply(Bound(1, E),
            All(Call("Finset", Natural), ["S"], Imply(And(PositiveTable, Not(Coverage(E))),
                All(Natural, ["H"], Imply(completeFactor, factorConclusion))))));
        Formula recovered = All(Natural, ["e"], Imply(Bound(1, E),
            All(Call("Finset", Natural), ["S"], Imply(And(PositiveTable, Coverage(E)),
                And(Call("Nonempty", S), distinct, All(State, ["x"],
                    Equal(Call("minGcdTable", PrimePower, S, F.Id("x")), Content("x"))))))));
        return All(Natural, ["p"], Imply(Call("Prime", P),
            And(And(failed, minimum, lowerPrecision, equivalence, factorFailure, recovered), AffineFormula())));
    }

    private static Formula AffineFormula() => All(Natural, ["e"], Imply(Bound(2, E),
        All(Natural, ["t"], All(State, ["x"], Imply(
            Divides(Pow(P, ParentExponent), Value(Add(F.Id("t"), D(1)), "x")),
            All(Natural, ["j"], IffFormula(
                Divides(PrimePower, Value(Add(Add(F.Id("t"), D(1)),
                    Mul(F.Id("j"), ParentRank)), "x")),
                Equal(Add(Base("x"), Mul(Call("natCast", F.Id("j"), PrimeRing), Slope("x"))), D(0)))))))));

    private static Formula ResultFormula()
    {
        Formula factors = All(Natural, ["p"], Imply(Call("Prime", P), All(Natural, ["e"],
            Imply(And(Bound(1, E), Divides(PrimePower, Hmod),
                Not(Divides(Pow(P, Add(E, D(1))), Hmod))), Coverage(E)))));
        Formula global = All(Natural, ["H"], Imply(Less(D(0), Hmod),
            All(Call("Finset", Natural), ["S"], Imply(PositiveTable,
                IffFormula(Call("Identifies", Call("actualGcd", Hmod), S), factors)))));
        Formula unit = All(Natural, ["k"], All(NaturalState, ["v"],
            Equal(Actual(D(1), K, "v"), D(1))));
        Formula sourceMinimum = All(NaturalState, ["v"],
            Equal(Call("minActualGcdTable", PrimePower, S, F.Id("v")),
                Call("gcd", Call("gcd", Coordinate("v", 1), Coordinate("v", 2)), PrimePower)));
        Formula tableMinimum = Imply(And(PositiveTable, Coverage(E)),
            And(Call("Nonempty", S), sourceMinimum));
        Formula naturalMinimum = All(Natural, ["p"], Imply(Call("Prime", P),
            All(Natural, ["e"], Imply(Bound(1, E), All(Call("Finset", Natural), ["S"], tableMinimum)))));
        return And(LocalFormula(), global, unit, naturalMinimum);
    }
}
