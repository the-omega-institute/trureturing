using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.SicKFidelity;

internal sealed class SicKFidelityAchievableRegionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityAchievableRegion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/mayer2021zerofidelity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact planar regions of pairs (F_k(Lambda), F(Lambda)) realized by n-qubit completely positive trace-preserving maps across k = 0, 1 <= k <= n - 1, and k >= n, closed-form upper and lower process-fidelity envelopes at prescribed 0-fidelity, unimodal maximizer analysis of the binomial weight kernel, and non-identifiability of F(Lambda) from any single F_k(Lambda) for n >= 2 and k <= n - 1.",
        H("Achievable (k-fidelity, process fidelity) regions and single-fidelity non-identifiability"),
        Blocks(
            Node("sickfidelityregion-achievable-region-definition",
                "Achievable (k-fidelity, process fidelity) region", "achievableRegion",
                AchievableRegionFormula(),
                "For n qubits and truncation order k, achievableRegion(n, k, rho) is the subset of R^2 consisting of all pairs (realKFidelity(rho, k, Lambda), realProcessFidelity(Lambda)) as Lambda ranges over completely positive trace-preserving n-qubit maps.",
                DescribeRole.Definition),
            Node("sickfidelityregion-tail-coeff-definition",
                "Unsigned Pauli-weight binomial kernel", "tailCoeff",
                TailCoeffFormula(),
                "Defines g_k(w) = 3^{-w} C(w - 1, k) for natural numbers k and w.",
                DescribeRole.Definition),
            Node("sickfidelityregion-opt-weight-definition",
                "Maximizing Hamming weight w*", "optWeight",
                OptWeightFormula(),
                "Defines w*(n, k) = min(n, floor(3 k / 2) + 1).",
                DescribeRole.Definition),
            Node("sickfidelityregion-extremal-abscissa-definition",
                "Signed extremal horizontal vertex abscissa", "extremalAbscissa",
                ExtremalAbscissaFormula(),
                "Defines x_k(n) = (-1)^k g_k(w*(n, k)), the nonzero horizontal coordinate among vertices on the axis F = 0 for 1 <= k <= n - 1.",
                DescribeRole.Definition),
            Node("sickfidelityregion-zero-characterization-theorem",
                "Exact 0-fidelity achievable triangle, single-qubit segment, and extremal envelopes",
                "achievableRegion_zero_characterization",
                ZeroCharacterizationFormula(),
                "For every n >= 1, R_0 equals the closed convex hull of (1, 1), (3^{-n}, 0), and (1 / 3, 0). When n >= 2, (F_0, F) belongs to R_0 if and only if F >= 0 and 1 - (3 / 2)(1 - F_0) <= F <= (F_0 - 3^{-n}) / (1 - 3^{-n}), with the upper edge attained by mixtures t id + (1 - t) Z^{tensor n} (.) Z^{tensor n} and the lower edge attained by weight-1 Pauli mixtures; at every prescribed F_0 in [3^{-n}, 1], the maximum of F is (F_0 - 3^{-n}) / (1 - 3^{-n}) (strictly below F_0 for F_0 < 1 with gap (1 - F_0) 3^{-n} / (1 - 3^{-n})) and the minimum of F is max(0, 1 - (3 / 2)(1 - F_0)). When n = 1, R_0 collapses to the line segment F = 1 - (3 / 2)(1 - F_0) over 1 / 3 <= F_0 <= 1.",
                DescribeRole.Theorem),
            Node("sickfidelityregion-intermediate-and-high-characterization-theorem",
                "Intermediate achievable triangles, unimodal maximizers, and high-order diagonal segment",
                "achievableRegion_intermediate_and_high_characterization",
                IntermediateAndHighCharacterizationFormula(),
                "For 1 <= k <= n - 1, the kernel g_k(w) = 3^{-w} C(w - 1, k) satisfies 0 < g_k(w*) < 1 and attains its maximum over 1 <= w <= n uniquely at w* = min(n, floor(3 k / 2) + 1), except when k is even and 3 k / 2 + 1 <= n where the maximum is attained at {3 k / 2, 3 k / 2 + 1}; the achievable region R_k is the closed triangle conv{(1, 1), (0, 0), (x_k, 0)}, cut out by F >= 0 and F_k <= F <= (F_k - x_k) / (1 - x_k) for odd k and by F >= 0 and (F_k - x_k) / (1 - x_k) <= F <= F_k for even k (implying 0 <= F <= 1), with vertices attained by the identity map, weight-1 Pauli conjugation, and weight-w* Pauli conjugation. For k >= n >= 1, R_k is the diagonal segment {(F_k, F) | F_k = F and 0 <= F <= 1}.",
                DescribeRole.Theorem),
            Node("sickfidelityregion-non-identifiability-theorem",
                "Non-identifiability of process fidelity from a single lower-order k-fidelity",
                "kFidelity_non_identifiability_of_processFidelity",
                NonIdentifiabilityFormula(),
                "For every n >= 2 and every 0 <= k <= n - 1, there exist two n-qubit completely positive trace-preserving maps with the same k-fidelity F_k, one having zero entanglement process fidelity and one having strictly positive entanglement process fidelity (and hence distinct process fidelities).",
                DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Var(string x) => new Formula.Symbol(FormulaIdentifier.Create(x));
    private static Formula Field(string x) => Seq(Mathbb, Grp(F.Id(x)));
    private static Formula Named(string x) => Seq(Operatorname, Grp(F.Id(x)));
    private static Formula Fn(string name, params Formula[] args) => Call(name, args);
    private static Formula At(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Paren(Formula a) => Seq(Left, Open, a, Right, Close);
    private static Formula ProdType(Formula a, Formula b) => Seq(Left, Open, a, Sp, Times, Sp, b, Right, Close);
    private static Formula Pair(Formula a, Formula b) => Seq(Left, Open, a, Comma, Sp, b, Right, Close);
    private static Formula SetOf(params Formula[] items) => new Formula.SetLiteral([.. items]);
    private static Formula FilterSet(string x, Formula domain, Formula pred) =>
        Seq(Left, OpenBrace, MemRel(Var(x), domain), Sp, Mid, Sp, pred, Right, CloseBrace);
    private static Formula NegOf(Formula a) => new Formula.Negate(a);
    private static Formula FracOf(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula FloorOf(Formula a) => new Formula.Floor(a);
    private static Formula Inv(Formula a) => Pow(a, NegOf(Num(1)));
    private static Formula Eqn(Formula a, Formula b) => Equal(a, b);
    private static Formula NeqRel(Formula a, Formula b) => NotEqual(a, b);
    private static Formula LtRel(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeRel(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula MemRel(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Conj(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Conj3(Formula a, Formula b, Formula c) => Conj(a, Conj(b, c));
    private static Formula Conj4(Formula a, Formula b, Formula c, Formula d) => Conj(a, Conj3(b, c, d));
    private static Formula Conj6(Formula a, Formula b, Formula c, Formula d, Formula e, Formula f) =>
        Conj(a, Conj(b, Conj4(c, d, e, f)));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffRel(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Ex(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), domain, body);
    private static Formula Ite(Formula cond, Formula t, Formula e) => Fn("ite", cond, t, e);
    private static Formula Fun1(string x, Formula dx, Formula body) =>
        Paren(Seq(LambdaLower, Sp, MemRel(Var(x), dx), Sp, Mapsto, Sp, body));

    private static Formula NatT => Field("N");
    private static Formula RealT => Field("R");
    private static Formula Real2 => ProdType(RealT, RealT);
    private static Formula FinK(long k) => Fn("Fin", Num(k));
    private static Formula FinN(Formula n) => Fn("Fin", n);
    private static Formula PLbl(Formula n) => Fn("PauliLabel", n);
    private static Formula QMap(Formula n) => Fn("QubitMap", n);
    private static Formula QMat => Named("QubitMatrix");
    private static Formula SicFamN(Formula n) => Arrow(FinN(n), Arrow(FinK(4), QMat));
    private static Formula Inv3 => Inv(Num(3));
    private static Formula Inv3Pow(Formula n) => Pow(Inv3, n);
    private static Formula ThreeHalves => FracOf(Num(3), Num(2));
    private static Formula LowerLine(Formula x) =>
        Subtract(Num(1), Multiply(ThreeHalves, Subtract(Num(1), x)));

    private static Formula AchievableRegionFormula()
    {
        Formula n = Var("n"), k = Var("k"), r = Var("r"), p = Var("p"), l = Var("L");
        var set = FilterSet("p", Real2, Ex("L", QMap(n), Conj3(
            Fn("IsCompletelyPositive", l),
            Fn("IsTracePreserving", l),
            Eqn(p, Pair(Fn("realKFidelity", r, k, l), Fn("realProcessFidelity", l))))));
        return All("n", NatT, All("k", NatT, All("r", SicFamN(n),
            Eqn(Fn("achievableRegion", n, k, r), set))));
    }

    private static Formula TailCoeffFormula()
    {
        Formula k = Var("k"), w = Var("w");
        return All("k", NatT, All("w", NatT,
            Eqn(Fn("tailCoeff", k, w), Multiply(Pow(Inv3, w), Fn("choose", Subtract(w, Num(1)), k)))));
    }

    private static Formula OptWeightFormula()
    {
        Formula n = Var("n"), k = Var("k");
        var half3k = FloorOf(FracOf(Multiply(Num(3), k), Num(2)));
        return All("n", NatT, All("k", NatT,
            Eqn(Fn("optWeight", n, k), Fn("min", n, Add(half3k, Num(1))))));
    }

    private static Formula ExtremalAbscissaFormula()
    {
        Formula n = Var("n"), k = Var("k");
        return All("n", NatT, All("k", NatT,
            Eqn(Fn("extremalAbscissa", n, k),
                Multiply(Pow(NegOf(Num(1)), k), Fn("tailCoeff", k, Fn("optWeight", n, k))))));
    }

    private static Formula ChannelAttains(Formula r, Formula k, Formula qDist, Formula pt)
    {
        var ch = Fn("pauliChannel", qDist);
        return Conj3(
            Fn("IsCompletelyPositive", ch),
            Fn("IsTracePreserving", ch),
            Eqn(Pair(Fn("realKFidelity", r, k, ch), Fn("realProcessFidelity", ch)), pt));
    }

    private static Formula ZeroCharacterizationFormula()
    {
        Formula n = Var("n"), r = Var("r"), i = Var("i"), p = Var("p");
        Formula t = Var("t"), g = Var("g"), b = Var("b"), x = Var("x"), y = Var("y");
        var localR = All("i", FinN(n), Fn("IsQubitSICProjector", At(r, i)));
        var reg0 = Fn("achievableRegion", n, Num(0), r);
        var p1 = Fn("fst", p);
        var p2 = Fn("snd", p);
        var inv3n = Inv3Pow(n);
        var upperP = FracOf(Subtract(p1, inv3n), Subtract(Num(1), inv3n));
        var upperX = FracOf(Subtract(x, inv3n), Subtract(Num(1), inv3n));
        var c1 = Eqn(reg0, Fn("convexHull", RealT,
            SetOf(Pair(Num(1), Num(1)), Pair(inv3n, Num(0)), Pair(Inv3, Num(0)))));
        var c2 = Imp(LeRel(Num(2), n), All("p", Real2, IffRel(
            MemRel(p, reg0),
            Conj3(LeRel(Num(0), p2), LeRel(LowerLine(p1), p2), LeRel(p2, upperP)))));
        var c3 = Imp(Eqn(n, Num(1)), All("p", Real2, IffRel(
            MemRel(p, reg0),
            Conj3(Eqn(p2, LowerLine(p1)), LeRel(Inv3, p1), LeRel(p1, Num(1))))));
        var allZ = Fun1("i", FinN(n), Num(3));
        var qUpper = Fun1("g", PLbl(n),
            Ite(Eqn(g, Num(0)), t, Ite(Eqn(g, allZ), Subtract(Num(1), t), Num(0))));
        var c4 = All("t", RealT, Imp(LeRel(Num(0), t), Imp(LeRel(t, Num(1)),
            ChannelAttains(r, Num(0), qUpper,
                Pair(Add(t, Multiply(Subtract(Num(1), t), inv3n)), t)))));
        var qLower = Fun1("g", PLbl(n),
            Ite(Eqn(g, Num(0)), t, Ite(Eqn(g, b), Subtract(Num(1), t), Num(0))));
        var c5 = All("b", PLbl(n), Imp(Eqn(Fn("hammingWeight", b), Num(1)),
            All("t", RealT, Imp(LeRel(Num(0), t), Imp(LeRel(t, Num(1)),
                ChannelAttains(r, Num(0), qLower,
                    Pair(Add(t, Multiply(Subtract(Num(1), t), Inv3)), t)))))));
        var fiberX = FilterSet("y", RealT, MemRel(Pair(x, y), reg0));
        var gapX = FracOf(Multiply(Subtract(Num(1), x), inv3n), Subtract(Num(1), inv3n));
        var c6 = Imp(LeRel(Num(2), n), All("x", RealT, Imp(LeRel(inv3n, x), Imp(LeRel(x, Num(1)),
            Conj4(
                Fn("IsGreatest", fiberX, upperX),
                Imp(LtRel(x, Num(1)), LtRel(upperX, x)),
                Eqn(Subtract(x, upperX), gapX),
                Fn("IsLeast", fiberX, Fn("max", Num(0), LowerLine(x))))))));
        return All("n", NatT, Imp(LeRel(Num(1), n), All("r", SicFamN(n),
            Imp(localR, Conj6(c1, c2, c3, c4, c5, c6)))));
    }

    private static Formula IntermediateAndHighCharacterizationFormula()
    {
        Formula n = Var("n"), k = Var("k"), r = Var("r"), i = Var("i"), w = Var("w");
        Formula p = Var("p"), b = Var("b"), g = Var("g");
        var localR = All("i", FinN(n), Fn("IsQubitSICProjector", At(r, i)));
        var regK = Fn("achievableRegion", n, k, r);
        var optW = Fn("optWeight", n, k);
        var optVal = Fn("tailCoeff", k, optW);
        var extX = Fn("extremalAbscissa", n, k);
        var p1 = Fn("fst", p);
        var p2 = Fn("snd", p);
        var chord = FracOf(Subtract(p1, extX), Subtract(Num(1), extX));
        var half3k = FloorOf(FracOf(Multiply(Num(3), k), Num(2)));
        var icc1n = Fn("Icc", Num(1), n);
        var maxSet = FilterSet("w", icc1n, Eqn(Fn("tailCoeff", k, w), optVal));
        var tieSet = Ite(Conj(Fn("Even", k), LeRel(Add(half3k, Num(1)), n)),
            SetOf(half3k, Add(half3k, Num(1))), SetOf(optW));
        var deltaB = Fun1("g", PLbl(n), Ite(Eqn(g, b), Num(1), Num(0)));
        var idMap = Named("id");
        var m1 = Conj(LtRel(Num(0), optVal), LtRel(optVal, Num(1)));
        var m2 = All("w", icc1n, LeRel(Fn("tailCoeff", k, w), optVal));
        var m3 = Eqn(maxSet, tieSet);
        var m4 = Eqn(regK, Fn("convexHull", RealT,
            SetOf(Pair(Num(1), Num(1)), Pair(Num(0), Num(0)), Pair(extX, Num(0)))));
        var m5 = Imp(Fn("Odd", k), All("p", Real2, IffRel(
            MemRel(p, regK),
            Conj3(LeRel(Num(0), p2), LeRel(p1, p2), LeRel(p2, chord)))));
        var m6 = Imp(Fn("Even", k), All("p", Real2, IffRel(
            MemRel(p, regK),
            Conj3(LeRel(Num(0), p2), LeRel(chord, p2), LeRel(p2, p1)))));
        var m7 = All("p", Real2, Imp(MemRel(p, regK), Conj(LeRel(Num(0), p2), LeRel(p2, Num(1)))));
        var m8 = Conj3(
            Fn("IsCompletelyPositive", idMap),
            Fn("IsTracePreserving", idMap),
            Eqn(Pair(Fn("realKFidelity", r, k, idMap), Fn("realProcessFidelity", idMap)),
                Pair(Num(1), Num(1))));
        var m9 = All("b", PLbl(n), Imp(Eqn(Fn("hammingWeight", b), Num(1)),
            ChannelAttains(r, k, deltaB, Pair(Num(0), Num(0)))));
        var m10 = Ex("b", PLbl(n), Eqn(Fn("hammingWeight", b), optW));
        var m11 = All("b", PLbl(n), Imp(Eqn(Fn("hammingWeight", b), optW),
            ChannelAttains(r, k, deltaB, Pair(extX, Num(0)))));
        var interRegime = Imp(Conj(LeRel(Num(1), k), LeRel(Add(k, Num(1)), n)),
            Conj(m1, Conj(m2, Conj(m3, Conj(m4, Conj(m5, Conj6(m6, m7, m8, m9, m10, m11)))))));
        var highRegime = Imp(Conj(LeRel(Num(1), n), LeRel(n, k)), Conj(
            Eqn(regK, Fn("convexHull", RealT, SetOf(Pair(Num(0), Num(0)), Pair(Num(1), Num(1))))),
            Eqn(regK, FilterSet("p", Real2,
                Conj3(Eqn(p1, p2), LeRel(Num(0), p2), LeRel(p2, Num(1)))))));
        return All("n", NatT, All("k", NatT, All("r", SicFamN(n),
            Imp(localR, Conj(interRegime, highRegime)))));
    }

    private static Formula NonIdentifiabilityFormula()
    {
        Formula n = Var("n"), k = Var("k"), r = Var("r"), i = Var("i");
        Formula l = Var("L"), m = Var("M");
        var localR = All("i", FinN(n), Fn("IsQubitSICProjector", At(r, i)));
        var witness = Ex("L", QMap(n), Ex("M", QMap(n), Conj(
            Fn("IsCompletelyPositive", l),
            Conj(Fn("IsTracePreserving", l),
                Conj6(
                    Fn("IsCompletelyPositive", m),
                    Fn("IsTracePreserving", m),
                    Eqn(Fn("realKFidelity", r, k, l), Fn("realKFidelity", r, k, m)),
                    Eqn(Fn("realProcessFidelity", l), Num(0)),
                    LtRel(Num(0), Fn("realProcessFidelity", m)),
                    NeqRel(Fn("realProcessFidelity", l), Fn("realProcessFidelity", m)))))));
        return All("n", NatT, All("k", NatT, Imp(LeRel(Num(2), n),
            Imp(LeRel(Add(k, Num(1)), n), All("r", SicFamN(n), Imp(localR, witness))))));
    }
}
