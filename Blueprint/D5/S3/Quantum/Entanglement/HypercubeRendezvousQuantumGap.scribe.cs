using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class HypercubeRendezvousQuantumGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/HypercubeRendezvousQuantumGap.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/wang2026rendezvous");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For t ≥ 2 and d > 2t, the quantum supremum is strictly below the no-signalling supremum in balanced hypercube rendezvous.",
        H("The quantum gap in hypercube rendezvous"), Blocks(
            Node("correlation", "Real correlation arrays", "Correlation",
                Parameters(Equal(Local("Correlation", X("d"), X("t")),
                    Arrow(Vertex(), Arrow(Vertex(), Arrow(Output(), Arrow(Output(), Reals())))))),
                "The array assigns a real number to each ordered pair of inputs and outputs. Positivity, normalization and the choice of strategy class are imposed separately, as in §2.",
                DescribeRole.Definition),
            Node("promised", "Promised inputs", "Promised",
                Parameters(All("sigma", Vertex(), All("tau", Vertex(),
                    IffOf(Local("Promised", X("d"), X("t"), X("sigma"), X("tau")),
                        Equal(Card(Call("symmDiff", X("sigma"), X("tau"))), Mul(Num(2), X("t"))))))),
                "The two starting vertices have Hamming distance 2t, the promise in §2.",
                DescribeRole.Definition),
            Node("inputs", "The finite input set", "Inputs", InputsFormula(),
                "Filter the set of all ordered vertex pairs by the distance promise. The value averages uniformly over this finite set, as in Eq. (2.7).",
                DescribeRole.Definition),
            Node("value", "Average winning probability", "value", ValueFormula(),
                "Equation (2.7) sums the winning probabilities and divides by the number of promised ordered input pairs. The cardinality in the denominator is cast to the real numbers.",
                DescribeRole.Definition),
            Node("quantum-strategy", "Finite-dimensional states and POVMs", "QStrategy", StrategyFormula(),
                "A strategy consists of a positive semidefinite complex density matrix of trace one on the product of two finite index types, together with a POVM for each local input. Every effect is positive semidefinite, and each measurement sums to the identity. These are finite-dimensional quantum strategies in the sense of §2, Eq. (2.8). The local dimensions are arbitrary.",
                DescribeRole.Definition),
            Node("quantum-probability", "The Born correlation", "QStrategy.prob", ProbabilityFormula(),
                "For each input and output pair, take the real part of the trace of rho times the Kronecker product of the two POVM effects. This is the real-valued Born correlation used for the quantum strategies in §2.",
                DescribeRole.Definition),
            Node("is-quantum", "Quantum realizability", "IsQuantum", QuantumFormula(),
                "There exist two types in Type, finite enumerations and decidable equalities on those types, and a strategy with induced correlation equal to P. The existential instances are the instances used to form the strategy and its probability array.",
                DescribeRole.Definition),
            Node("is-ns", "No-signalling correlations", "IsNS", NSFormula(),
                "All entries are nonnegative, every input pair has total probability one, and each party's marginal is independent of the other party's input. These conditions apply to all input pairs, as in the no-signalling strategy class of §2.",
                DescribeRole.Definition),
            Node("quantum-values", "Values of quantum correlations", "QValues", ValuesFormula("QValues", "IsQuantum"),
                "A real number belongs to this set precisely when it is the value of a finite-dimensional quantum correlation, as in Eq. (2.8).",
                DescribeRole.Definition),
            Node("ns-values", "Values of no-signalling correlations", "NSValues", ValuesFormula("NSValues", "IsNS"),
                "A real number belongs to this set precisely when it is the value of a no-signalling correlation, as in Eq. (2.8).",
                DescribeRole.Definition),
            Node("omega-q", "The quantum supremum", "omegaQ",
                Parameters(Equal(Local("omegaQ", X("d"), X("t")),
                    Call("sSup", Local("QValues", X("d"), X("t"))))),
                "The quantum value is sSup of the set of quantum values. Equation (2.8) uses a supremum because finite-dimensional quantum correlations need not form a closed set.",
                DescribeRole.Definition),
            Node("omega-ns", "The no-signalling supremum", "omegaNS",
                Parameters(Equal(Local("omegaNS", X("d"), X("t")),
                    Call("sSup", Local("NSValues", X("d"), X("t"))))),
                "The no-signalling value is also expressed as sSup. Equation (2.8) expresses the optimum as a maximum; the formula here states the supremum definition used by the Lean module.",
                DescribeRole.Definition),
            Node("claim", "Wang's strict-gap question", "claim",
                IffOf(Name("claim"), ClaimFormula()),
                "Section 7 asks whether the quantum value is strictly below the no-signalling value for t at least two and d greater than 2t. This proposition quantifies over exactly that range.",
                DescribeRole.Definition),
            Node("result", "The strict gap", "result", Name("claim"),
                "The proposition holds. Averaging over translations and coordinate permutations gives a positive semidefinite vector system to which the quantitative vector bound applies. Every finite-dimensional quantum strategy has value at most (Nat.choose (2t) t / Nat.choose d t) times (1 − RendezvousVectorSystemGap.kappa d t), with the binomial coefficients cast to the real numbers. A no-signalling correlation attains the ratio of the two binomial coefficients. The positive factor kappa therefore separates the two suprema and answers the strict-gap question in Wang's §7.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))
        )));

    private static Formula InputsFormula() => Parameters(Equal(Local("Inputs", X("d"), X("t")),
        At(Qualified("Finset", "filter"), LambdaOf("p", Product(Vertex(), Vertex()),
            Local("Promised", X("d"), X("t"), First(X("p")), Second(X("p")))),
            Typed(Qualified("Finset", "univ"), Call("Finset", Product(Vertex(), Vertex()))))));

    private static Formula ValueFormula() => Parameters(All("P", Correlation(),
        Equal(Local("value", X("P")), new Formula.Fraction(
            SumIn("p", Local("Inputs", X("d"), X("t")),
                SumOver("A", Output(), SumOver("B", Output(),
                    Call("ite", Abstract("Wins", First(X("p")), Second(X("p")), X("A"), X("B")),
                        At(X("P"), First(X("p")), Second(X("p")), X("A"), X("B")), Num(0))))),
            CastReal(Card(Local("Inputs", X("d"), X("t"))))))));

    private static Formula StrategyFormula()
    {
        Formula rho = Rho, e = X("E"), f = X("F");
        Formula ea = At(e, X("sigma"), X("A"));
        Formula fb = At(f, X("tau"), X("B"));
        Formula fields = Seq(Mathrm, Grp(X("structure")), Sp, OpenBrace,
            rho, Colon, Sp, Matrix(Product(X("alpha"), X("beta"))), Semi, Sp,
            FieldName("rho", "psd"), Colon, Sp, PSD(rho), Semi, Sp,
            FieldName("rho", "trace"), Colon, Sp, Equal(At(Qualified("Matrix", "trace"), rho), Typed(Num(1), Complexes())), Semi, Sp,
            e, Colon, Sp, Arrow(Vertex(), Arrow(Output(), Matrix(X("alpha")))), Semi, Sp,
            f, Colon, Sp, Arrow(Vertex(), Arrow(Output(), Matrix(X("beta")))), Semi, Sp,
            FieldName("E", "psd"), Colon, Sp, All("sigma", Vertex(), All("A", Output(), PSD(ea))), Semi, Sp,
            FieldName("F", "psd"), Colon, Sp, All("tau", Vertex(), All("B", Output(), PSD(fb))), Semi, Sp,
            FieldName("E", "sum"), Colon, Sp, All("sigma", Vertex(),
                Equal(SumOver("A", Output(), ea), Typed(Num(1), Matrix(X("alpha"))))), Semi, Sp,
            FieldName("F", "sum"), Colon, Sp, All("tau", Vertex(),
                Equal(SumOver("B", Output(), fb), Typed(Num(1), Matrix(X("beta"))))), CloseBrace);
        return Parameters(FiniteTypes(Equal(Strategy(), fields)));
    }

    private static Formula ProbabilityFormula() => Parameters(FiniteTypes(All("S", Strategy(),
        All("sigma", Vertex(), All("tau", Vertex(), All("A", Output(), All("B", Output(),
            Equal(At(Probability(), X("S"), X("sigma"), X("tau"), X("A"), X("B")),
                At(Qualified("Complex", "re"), At(Qualified("Matrix", "trace"),
                    Mul(Seq(X("S"), Dot, Rho), At(Qualified("Matrix", "kronecker"),
                        At(Seq(X("S"), Dot, X("E")), X("sigma"), X("A")),
                        At(Seq(X("S"), Dot, X("F")), X("tau"), X("B"))))))))))))));

    private static Formula QuantumFormula() => Parameters(All("P", Correlation(),
        IffOf(Local("IsQuantum", X("P")),
            Ex("alpha", X("Type"), Ex("beta", X("Type"),
            Ex("falpha", Call("Fintype", X("alpha")), Ex("fbeta", Call("Fintype", X("beta")),
            Ex("dalpha", Call("DecidableEq", X("alpha")), Ex("dbeta", Call("DecidableEq", X("beta")),
            Ex("S", Strategy(), Equal(At(Probability(), X("S")), X("P"))))))))))));

    private static Formula NSFormula()
    {
        Formula entry = At(X("P"), X("sigma"), X("tau"), X("A"), X("B"));
        Formula positive = All("sigma", Vertex(), All("tau", Vertex(), All("A", Output(),
            All("B", Output(), LE(Num(0), entry)))));
        Formula normalized = All("sigma", Vertex(), All("tau", Vertex(),
            Equal(SumOver("A", Output(), SumOver("B", Output(), entry)), Num(1))));
        Formula alice = All("sigma", Vertex(), All("tau", Vertex(), All("tauprime", Vertex(),
            All("A", Output(), Equal(SumOver("B", Output(), entry),
                SumOver("B", Output(), At(X("P"), X("sigma"), X("tauprime"), X("A"), X("B"))))))));
        Formula bob = All("sigma", Vertex(), All("sigmaprime", Vertex(), All("tau", Vertex(),
            All("B", Output(), Equal(SumOver("A", Output(), entry),
                SumOver("A", Output(), At(X("P"), X("sigmaprime"), X("tau"), X("A"), X("B"))))))));
        return Parameters(All("P", Correlation(), IffOf(Local("IsNS", X("P")),
            And(positive, And(normalized, And(alice, bob))))));
    }

    private static Formula ValuesFormula(string values, string condition) => Parameters(
        Equal(Local(values, X("d"), X("t")), Seq(OpenBrace, Typed(X("r"), Reals()), Sp, Mid, Sp,
            Ex("P", Correlation(), And(Local(condition, X("P")), Equal(Local("value", X("P")), X("r")))),
            CloseBrace)));

    private static Formula ClaimFormula() => All("t", Naturals(), All("d", Naturals(),
        Imp(LE(Num(2), X("t")), Imp(LT(Mul(Num(2), X("t")), X("d")),
            LT(Local("omegaQ", X("d"), X("t")), Local("omegaNS", X("d"), X("t")))))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance? provenance = null) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + (declaration == "QStrategy.prob" ? "prob" : declaration)), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role,
            declaration == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("wang-2026-hypercube-rendezvous-quantum-gap"),
                ResolutionKind.Proved) : null);
    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(X(owner), Dot, X(name)));
    private static Formula Name(string name) => Qualified("HypercubeRendezvousQuantumGap", name);
    private static Formula Local(string name, params Formula[] args) => At(Name(name), args);
    private static Formula Abstract(string name, params Formula[] args) => At(Qualified("RendezvousVectorSystemGap", name), args);
    private static Formula Probability() => Seq(Operatorname,
        Grp(X("HypercubeRendezvousQuantumGap"), Dot, X("QStrategy"), Dot, X("prob")));
    private static Formula At(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula FieldName(string a, string b) => new Formula.Subscript(X(a), X(b));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula CastReal(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Reals());
    private static Formula Vertex() => Abstract("Vertex", X("d"));
    private static Formula Output() => Abstract("Output", X("d"), X("t"));
    private static Formula Correlation() => Local("Correlation", X("d"), X("t"));
    private static Formula Card(Formula value) => At(Qualified("Finset", "card"), value);
    private static Formula First(Formula value) => At(Qualified("Prod", "fst"), value);
    private static Formula Second(Formula value) => At(Qualified("Prod", "snd"), value);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Product(Formula a, Formula b) => Parenthesized(Seq(a, Sp, Times, Sp, b));
    private static Formula Matrix(Formula index) => Call("Matrix", index, index, Complexes());
    private static Formula PSD(Formula matrix) => At(Qualified("Matrix", "PosSemidef"), matrix);
    private static Formula Strategy() => Local("QStrategy", X("d"), X("t"), X("alpha"), X("beta"),
        X("falpha"), X("fbeta"), X("dalpha"), X("dbeta"));
    private static Formula FiniteTypes(Formula body) => All("alpha", Seq(X("Type"), Star),
        All("beta", Seq(X("Type"), Star), All("falpha", Call("Fintype", X("alpha")),
        All("fbeta", Call("Fintype", X("beta")), All("dalpha", Call("DecidableEq", X("alpha")),
        All("dbeta", Call("DecidableEq", X("beta")), body))))));
    private static Formula Parameters(Formula body) => All("d", Naturals(), All("t", Naturals(), body));
    private static Formula All(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Ex(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), domain, body);
    private static Formula LambdaOf(string v, Formula domain, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(v), domain), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string v, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(v), domain)), Sp, Parenthesized(body));
    private static Formula SumIn(string v, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, new Formula.Relation(X(v), FormulaRelationOperator.MemberOf, set)),
            Sp, Parenthesized(body));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LT(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
}
