using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Codes;

internal sealed class PurificationCircuitMonotonicityRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Codes/PurificationCircuitMonotonicityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Hamming/barbergillespietaylor2023purification");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A tight purification circuit has strictly decreasing output error between two preparation error rates.",
        H("Preparation error need not increase purification output error"),
        Blocks(
            Definition("gate", "Gate", "CNOT and Toffoli gates", GateFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Gate n is the disjoint sum of ordered pairs of distinct qubits and ordered triples "
                    + "of pairwise distinct qubits. A pair specifies a CNOT control and target; a triple "
                    + "specifies two Toffoli controls followed by its target. Qubits n means Fin n → Bool. "
                    + "These are the gate types used in purification circuits (purification.tex, line 203)."),
            Definition("gate-set", "gateSet", "The qubits touched by a gate", GateSetFormula(),
                AssessedProvenance.FromRepo(Source),
                "The support of a CNOT is its control and target; the support of a Toffoli is its two "
                    + "controls and target. Taking a finite set forgets their order while retaining exactly "
                    + "the qubits exposed to that gate's depolarisation."),
            Definition("is-purification", "IsPurification", "Clearing all low-weight inputs", PurificationFormula(),
                AssessedProvenance.FromLiterature(Source),
                "A circuit purifies through weight e when every input with at most e true bits gives false "
                    + "at each nominated output after the ideal gates. The gates act in list order: a CNOT "
                    + "flips its target when its control is true, and a Toffoli flips its target when both "
                    + "controls are true. This is the purification condition of purification.tex, line 203; "
                    + "the number of nominated outputs is their finite-set cardinality."),
            Definition("p-out", "pOut", "Expected output error under independent noise", OutputFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The initial mass is the product of independent Bernoulli masses with parameter p0. "
                    + "Each round first applies its ideal gate, then depolarises the gate's support with "
                    + "probability pC or pT, then independently depolarises each remaining qubit with "
                    + "probability pI. Depolarising a set retains the old mass with weight 1 − p and adds "
                    + "p times the uniform average over all assignments agreeing outside that set. "
                    + "The final mass is summed over states true at each output and divided by the "
                    + "output cardinality, explicitly cast from ℕ to ℝ. This is the error model at "
                    + "purification.tex, lines 219–243, and the average output error at lines 711–713, "
                    + "specialised to one gate per round. The real-valued formula is defined for every "
                    + "parameter and output set; an empty output set gives zero by real division by zero."),
            Definition("claim", "claim", "Coordinatewise monotonicity for tight circuits", ClaimFormula(),
                AssessedProvenance.FromRepo(Source),
                "For natural n, k and e with 1 ≤ k ≤ n and 1 ≤ e ≤ n, choose any circuit and exactly k "
                    + "outputs. If it purifies through weight e and the binomial space bound is an equality, "
                    + "the assertion requires output error to be nondecreasing separately in each of p0, "
                    + "pI, pC and pT, holding the other three fixed. Both parameter vectors must satisfy "
                    + "0 ≤ p0 < 1/2 and 0 ≤ pI, pC, pT ≤ 1. This is the nondecreasing reading of the "
                    + "question at purification.tex, lines 859–862, for circuits with one gate per round; "
                    + "the space bound and its parameter range appear at lines 265–270."),
            Describe.Lean(
                DescribeId.Create("purification-monotonicity-result"),
                DeclarationHandle.Create(Module + "result"),
                H("A six-gate circuit refutes monotonicity"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "At depolarisation probability zero, the retained mass has coefficient one and "
                            + "the averaged mass has coefficient zero. Thus each such operation is the identity, "
                            + "and folding zero-probability idle operations also leaves the distribution unchanged. "
                            + "There are exactly eight states on three qubits, obtained by independently choosing "
                            + "false or true at coordinates 0, 1 and 2.")),
                    Paragraph(Text(
                        "If two distinct coordinates are true, the Hamming distance from the all-false state "
                            + "is at least two. Now take n = 3, k = 1, e = 1, output set {0}, and the gate list "
                            + "CNOT(0→1), CNOT(1→2), CNOT(1→0), CNOT(0→2), CNOT(1→0), Toffoli(1,2→0). "
                            + "Splitting on the three input bits gives eight cases. Direct gate evaluation makes "
                            + "output 0 false in the all-false case and the three cases with one true bit. "
                            + "Each remaining case has two distinct true coordinates, contradicting weight at "
                            + "most one. The circuit therefore purifies through weight one. Its space bound is "
                            + "tight because the two binomial coefficients are 1 and 3, with sum 4 = 2^(3−1).")),
                    Paragraph(Text(
                        "Set pI = pT = 0 and pC = 1/4. Expand the six rounds of the distribution, remove "
                            + "the zero-probability idle operations, and sum over the eight states. The preparation "
                            + "law is the product of the three Bernoulli masses. With p0 = 0, exact arithmetic "
                            + "gives output error 1481/4096. The same finite calculation with p0 = 1/100 gives "
                            + "23121347/64000000.")),
                    Paragraph(Text(
                        "Assume the coordinatewise assertion. Apply it to this circuit, these outputs and "
                            + "n = 3, k = e = 1, using the purification property and space equality just established. "
                            + "Its first conjunct gives monotonicity in p0. Both (0,0,1/4,0) and "
                            + "(1/100,0,1/4,0) lie in the required parameter region, and their last three "
                            + "coordinates agree. Since 0 ≤ 1/100, monotonicity would give "
                            + "1481/4096 ≤ 23121347/64000000. Subtracting the right side from the left "
                            + "gives 9639/32000000 > 0, a contradiction. Thus the full coordinatewise assertion "
                            + "fails already in the preparation coordinate. This conclusion imposes no claim "
                            + "about monotonicity in the other three coordinates or about shortest circuits."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("barber-gillespie-taylor-2023-purification-monotonicity"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string declaration, string title, Formula formula,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("purification-monotonicity-" + id),
            DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula GateFormula() => All("n", Naturals(),
        Equal(LocalCall("Gate", X("n")), At(Qualified("Sum"), CnotType(), ToffoliType())));

    private static Formula CnotType() => At(Qualified("Subtype"),
        LambdaOf("p", Product(FinOf(X("n")), FinOf(X("n"))),
            NotEqual(First(X("p")), Second(X("p")))));

    private static Formula ToffoliType() => At(Qualified("Subtype"),
        LambdaOf("p", Product(FinOf(X("n")), Product(FinOf(X("n")), FinOf(X("n")))),
            And(NotEqual(First(X("p")), First(Second(X("p")))),
                And(NotEqual(First(X("p")), Second(Second(X("p")))),
                    NotEqual(First(Second(X("p"))), Second(Second(X("p"))))))));

    private static Formula GateSetFormula() => All("n", Naturals(),
        Equal(Typed(Local("gateSet"), Arrow(LocalCall("Gate", X("n")), FinsetOf(FinOf(X("n"))))),
            At(Qualified("Sum", "elim"),
                LambdaOf("p", CnotType(), Set(First(Value(X("p"))), Second(Value(X("p"))))),
                LambdaOf("p", ToffoliType(), Set(First(Value(X("p"))),
                    First(Second(Value(X("p")))), Second(Second(Value(X("p")))))))));

    private static Formula GateImage(Formula gate, Formula state)
    {
        Formula p = Value(X("p"));
        Formula cnot = LambdaOf("p", CnotType(), LambdaOf("state", StateType(),
            At(Qualified("Function", "update"), X("state"), Second(p),
                If(IsTrue(At(X("state"), First(p))),
                    At(Qualified("Bool", "not"), At(X("state"), Second(p))),
                    At(X("state"), Second(p))))));
        Formula toffoli = LambdaOf("p", ToffoliType(), LambdaOf("state", StateType(),
            At(Qualified("Function", "update"), X("state"), Second(Second(p)),
                If(IsTrue(At(Qualified("Bool", "and"), At(X("state"), First(p)),
                        At(X("state"), First(Second(p))))),
                    At(Qualified("Bool", "not"), At(X("state"), Second(Second(p)))),
                    At(X("state"), Second(Second(p)))))));
        return At(Qualified("Sum", "elim"), cnot, toffoli, gate, state);
    }

    private static Formula PurificationFormula()
    {
        Formula image = At(Qualified("List", "foldl"),
            LambdaOf("current", StateType(), LambdaOf("gate", LocalCall("Gate", X("n")),
                GateImage(X("gate"), X("current")))), X("state"), X("circuit"));
        Formula condition = All("state", StateType(), Imp(
            LE(At(Qualified("hammingDist"), X("state"),
                At(Qualified("Function", "const"), FinOf(X("n")), Qualified("false"))), X("e")),
            All("i", FinOf(X("n")), Imp(Member(X("i"), X("outputs")),
                Equal(At(Parenthesized(image), X("i")), Qualified("false"))))));
        return CircuitBinders(All("e", Naturals(), Iff(
            LocalCall("IsPurification", X("circuit"), X("outputs"), X("e")), condition)));
    }

    private static Formula AveragedMass(Formula qubits, Formula p, Formula distribution)
    {
        Formula sameOutside = All("i", FinOf(X("n")), Imp(
            new Formula.Not(Parenthesized(Member(X("i"), qubits))),
            Equal(At(X("candidate"), X("i")), At(X("state"), X("i")))));
        Formula candidates = At(Qualified("Finset", "filter"),
            LambdaOf("candidate", StateType(), sameOutside), Universe(StateType()));
        Formula mass = At(Qualified("Finset", "sum"), candidates,
            LambdaOf("other", StateType(), At(Parenthesized(distribution), X("other"))));
        return LambdaOf("state", StateType(), Add(
            Multiply(Subtract(Typed(D(1), Reals()), p), At(Parenthesized(distribution), X("state"))),
            Multiply(new Formula.Fraction(p,
                new Formula.Power(Typed(D(2), Reals()), At(Qualified("Finset", "card"), qubits))), mass)));
    }

    private static Formula RoundMass()
    {
        Formula probability = At(Qualified("Sum", "elim"),
            At(Qualified("Function", "const"), CnotType(), X("pC")),
            At(Qualified("Function", "const"), ToffoliType(), X("pT")), X("gate"));
        Formula permuted = LambdaOf("state", StateType(),
            At(X("distribution"), Parenthesized(GateImage(X("gate"), X("state")))));
        Formula afterGate = AveragedMass(LocalCall("gateSet", X("gate")), X("gateProbability"), permuted);
        Formula remaining = Seq(Universe(FinOf(X("n"))), Sp, Setminus, Sp,
            LocalCall("gateSet", X("gate")));
        Formula idle = At(Qualified("List", "foldl"),
            LambdaOf("current", DistributionType(), LambdaOf("qubit", FinOf(X("n")),
                AveragedMass(Set(X("qubit")), X("pI"), X("current")))),
            X("afterGate"), At(Qualified("Finset", "toList"), Parenthesized(remaining)));
        return Let("gateProbability", Reals(), probability,
            Let("afterGate", DistributionType(), afterGate, idle));
    }

    private static Formula OutputFormula()
    {
        Formula initial = At(Qualified("D5", "S3", "Entropy", "NamingWindow", "GreenClassWindowEntropy", "windowLaw"),
            At(Qualified("Function", "const"), FinOf(X("n")),
                At(Qualified("D5", "S3", "Arith", "FibonacciAtomic", "Learning", "RawCorrelationConfidenceFailure",
                    "ScoreBridge", "bernoulliMass"), X("p0"))));
        Formula final = At(Qualified("List", "foldl"),
            LambdaOf("distribution", DistributionType(), LambdaOf("gate", LocalCall("Gate", X("n")), RoundMass())),
            initial, X("circuit"));
        Formula numerator = At(Qualified("Finset", "sum"), X("outputs"),
            LambdaOf("i", FinOf(X("n")), At(Qualified("Finset", "sum"), Universe(StateType()),
                LambdaOf("state", StateType(), If(IsTrue(At(X("state"), X("i"))),
                    At(Parenthesized(final), X("state")), Typed(D(0), Reals()))))));
        Formula equation = Equal(LocalCall("pOut", X("p0"), X("pI"), X("pC"), X("pT"),
            X("circuit"), X("outputs")), new Formula.Fraction(numerator,
                Typed(At(Qualified("Nat", "cast"), At(Qualified("Finset", "card"), X("outputs"))), Reals())));
        return All("n", Naturals(), All("p0", Reals(), All("pI", Reals(), All("pC", Reals(), All("pT", Reals(),
            All("circuit", At(Qualified("List"), LocalCall("Gate", X("n"))),
                All("outputs", FinsetOf(FinOf(X("n"))), equation)))))));
    }

    private static Formula ParameterRegion(string p0, string pI, string pC, string pT) =>
        And(LE(Typed(D(0), Reals()), X(p0)),
            And(LT(X(p0), new Formula.Fraction(Typed(D(1), Reals()), Typed(D(2), Reals()))),
                And(LE(Typed(D(0), Reals()), X(pI)), And(LE(X(pI), Typed(D(1), Reals())),
                    And(LE(Typed(D(0), Reals()), X(pC)), And(LE(X(pC), Typed(D(1), Reals())),
                        And(LE(Typed(D(0), Reals()), X(pT)), LE(X(pT), Typed(D(1), Reals())))))))));

    private static Formula CoordinateCondition(string coordinate)
    {
        Formula outputComparison = LE(
            LocalCall("pOut", X("p0"), X("pI"), X("pC"), X("pT"), X("circuit"), X("outputs")),
            LocalCall("pOut", X("q0"), X("qI"), X("qC"), X("qT"), X("circuit"), X("outputs")));
        Formula body = coordinate switch
        {
            "p0" => Imp(LE(X("p0"), X("q0")), Imp(Equal(X("pI"), X("qI")),
                Imp(Equal(X("pC"), X("qC")), Imp(Equal(X("pT"), X("qT")), outputComparison)))),
            "pI" => Imp(LE(X("pI"), X("qI")), Imp(Equal(X("p0"), X("q0")),
                Imp(Equal(X("pC"), X("qC")), Imp(Equal(X("pT"), X("qT")), outputComparison)))),
            "pC" => Imp(LE(X("pC"), X("qC")), Imp(Equal(X("p0"), X("q0")),
                Imp(Equal(X("pI"), X("qI")), Imp(Equal(X("pT"), X("qT")), outputComparison)))),
            _ => Imp(LE(X("pT"), X("qT")), Imp(Equal(X("p0"), X("q0")),
                Imp(Equal(X("pI"), X("qI")), Imp(Equal(X("pC"), X("qC")), outputComparison)))),
        };
        body = Imp(ParameterRegion("p0", "pI", "pC", "pT"),
            Imp(ParameterRegion("q0", "qI", "qC", "qT"), body));
        return All("p0", Reals(), All("pI", Reals(), All("pC", Reals(), All("pT", Reals(),
            All("q0", Reals(), All("qI", Reals(), All("qC", Reals(), All("qT", Reals(), body))))))));
    }

    private static Formula ClaimFormula()
    {
        Formula space = Equal(At(Qualified("Finset", "sum"),
            At(Qualified("Finset", "range"), Add(X("e"), D(1))),
            LambdaOf("j", Naturals(), At(Qualified("Nat", "choose"), X("n"), X("j")))),
            new Formula.Power(Typed(D(2), Naturals()), Subtract(X("n"), X("k"))));
        Formula conclusion = And(CoordinateCondition("p0"), And(CoordinateCondition("pI"),
            And(CoordinateCondition("pC"), CoordinateCondition("pT"))));
        Formula body = Imp(LE(D(1), X("k")), Imp(LE(X("k"), X("n")),
            Imp(LE(D(1), X("e")), Imp(LE(X("e"), X("n")),
                Imp(Equal(At(Qualified("Finset", "card"), X("outputs")), X("k")),
                    Imp(LocalCall("IsPurification", X("circuit"), X("outputs"), X("e")),
                        Imp(space, conclusion)))))));
        return Iff(Local("claim"), All("n", Naturals(), All("k", Naturals(), All("e", Naturals(),
            All("circuit", At(Qualified("List"), LocalCall("Gate", X("n"))),
                All("outputs", FinsetOf(FinOf(X("n"))), body))))));
    }

    private static Formula CircuitBinders(Formula body) => All("n", Naturals(),
        All("circuit", At(Qualified("List"), LocalCall("Gate", X("n"))),
            All("outputs", FinsetOf(FinOf(X("n"))), body)));
    private static Formula StateType() => Arrow(FinOf(X("n")), Qualified("Bool"));
    private static Formula DistributionType() => Arrow(StateType(), Reals());
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula FinsetOf(Formula type) => At(Qualified("Finset"), type);
    private static Formula Universe(Formula type) => Typed(Qualified("Finset", "univ"), FinsetOf(type));
    private static Formula Product(Formula a, Formula b) => At(Qualified("Prod"), a, b);
    private static Formula First(Formula p) => At(Qualified("Prod", "fst"), p);
    private static Formula Second(Formula p) => At(Qualified("Prod", "snd"), p);
    private static Formula Value(Formula p) => At(Qualified("Subtype", "val"), p);
    private static Formula Set(params Formula[] elements) =>
        Typed(new Formula.SetLiteral([.. elements]), FinsetOf(FinOf(X("n"))));
    private static Formula X(string name) => F.Id(name);
    private static Formula Local(string name) => Qualified(name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Let(string name, Formula type, Formula value, Formula body) =>
        Seq(Qualified("let"), Sp, Typed(X(name), type), Sp, Eq, Sp, Parenthesized(value), Semi, Sp,
            Parenthesized(body));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula If(Formula condition, Formula yes, Formula no) => At(Qualified("ite"), condition, yes, no);
    private static Formula IsTrue(Formula value) => Equal(value, Qualified("true"));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NotEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LT(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
}
