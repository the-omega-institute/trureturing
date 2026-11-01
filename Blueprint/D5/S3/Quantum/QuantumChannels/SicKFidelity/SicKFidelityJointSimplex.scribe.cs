using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.SicKFidelity;

internal sealed class SicKFidelityJointSimplexDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/QuantumChannels/SicKFidelity/SicKFidelityJointSimplex.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/mayer2021zerofidelity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal alternating linear relation among F_0, ..., F_{n-1} and the entanglement process fidelity F for arbitrary trace-preserving linear qubit maps, affine independence of the n + 1 Pauli-weight vertices in R^n, and exact n-simplex characterization of the joint CPTP k-fidelity range with unique barycentric recovery of (Q_0, ..., Q_n) and F.",
        H("Trace-preserving linear reconstruction and CPTP joint k-fidelity simplex geometry"),
        Blocks(
            Node("sickfidelitysimplex-vertex-definition",
                "Joint k-fidelity simplex vertices", "simplexVertex",
                SimplexVertexFormula(),
                "Defines the n + 1 vectors V_0, ..., V_n in R^n by V_0 = (1, ..., 1) and (V_w)_k = (-1)^k 3^{-w} C(w - 1, k) for 1 <= w <= n and 0 <= k <= n - 1.",
                DescribeRole.Definition),
            Node("sickfidelitysimplex-joint-vec-definition",
                "Joint lower-order k-fidelity vector", "jointKFidelityVec",
                JointKFidelityVecFormula(),
                "Collects the first n real SIC k-fidelities (F_0(Lambda), ..., F_{n-1}(Lambda)) in R^n for an n-qubit map Lambda.",
                DescribeRole.Definition),
            Node("sickfidelitysimplex-joint-range-definition",
                "CPTP joint k-fidelity range", "jointKFidelityRange",
                JointKFidelityRangeFormula(),
                "Defines the subset of R^n consisting of all joint vectors (F_0(Lambda), ..., F_{n-1}(Lambda)) realized by completely positive trace-preserving n-qubit maps Lambda.",
                DescribeRole.Definition),
            Node("sickfidelitysimplex-tp-exact-reconstruction-theorem",
                "Universal linear relation and exact fidelity reconstruction for trace-preserving maps",
                "tp_exact_fidelity_reconstruction",
                TpExactReconstructionFormula(),
                "For every n, every choice of single-qubit SICs, and every trace-preserving complex-linear map Lambda on M_{2^n}(C) (without requiring complete positivity), 3 sum_{k=0}^{n-1} (-2)^k F_k(Lambda) + (-2)^n F(Lambda) = 1, equivalently F(Lambda) = (-2)^{-n} (1 - 3 sum_{k=0}^{n-1} (-2)^k F_k(Lambda)), together with the corresponding real identity when Lambda is completely positive.",
                DescribeRole.Theorem),
            Node("sickfidelitysimplex-cptp-joint-range-theorem",
                "Affine independence, n-simplex joint range, and unique barycentric Pauli-weight recovery",
                "cptp_joint_kFidelity_simplex_range",
                CptpJointRangeFormula(),
                "For every n, the n + 1 vertices V_0, ..., V_n in R^n are affinely independent, the set of joint k-fidelity vectors (F_0(Lambda), ..., F_{n-1}(Lambda)) over completely positive trace-preserving n-qubit maps equals the n-simplex conv{V_0, ..., V_n}, the Pauli-weight sums (Q_0(Lambda), ..., Q_n(Lambda)) are the unique barycentric coordinates of (F_0(Lambda), ..., F_{n-1}(Lambda)) in this simplex, and F(Lambda) = Q_0(Lambda) = (-2)^{-n} (1 - 3 sum_{k=0}^{n-1} (-2)^k F_k(Lambda)).",
                DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Var(string x) => new Formula.Symbol(FormulaIdentifier.Create(x));
    private static Formula Field(string x) => Seq(Mathbb, Grp(F.Id(x)));
    private static Formula Fn(string name, params Formula[] args) => Call(name, args);
    private static Formula At(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula FilterSet(string x, Formula domain, Formula pred) =>
        Seq(Left, OpenBrace, MemRel(Var(x), domain), Sp, Mid, Sp, pred, Right, CloseBrace);
    private static Formula NegOf(Formula a) => new Formula.Negate(a);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Subscript(a, b);
    private static Formula Inv(Formula a) => Pow(a, NegOf(Num(1)));
    private static Formula Eqn(Formula a, Formula b) => Equal(a, b);
    private static Formula LeRel(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula MemRel(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Conj(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Conj3(Formula a, Formula b, Formula c) => Conj(a, Conj(b, c));
    private static Formula Conj4(Formula a, Formula b, Formula c, Formula d) => Conj(a, Conj3(b, c, d));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), domain, body);
    private static Formula Ex(string x, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), domain, body);
    private static Formula SumIn(string x, Formula set, Formula body) =>
        Seq(Sub(Sum, MemRel(Var(x), set)), Sp, body);

    private static Formula NatT => Field("N");
    private static Formula RealT => Field("R");
    private static Formula ComplexT => Field("C");
    private static Formula FinK(long k) => Fn("Fin", Num(k));
    private static Formula FinN(Formula n) => Fn("Fin", n);
    private static Formula QMap(Formula n) => Fn("QubitMap", n);
    private static Formula Mat2C => Fn("Matrix", FinK(2), FinK(2), ComplexT);
    private static Formula SicFamN(Formula n) => Arrow(FinN(n), Arrow(FinK(4), Mat2C));
    private static Formula NegTwoPow(Formula k) => Pow(NegOf(Num(2)), k);

    private static Formula SimplexVertexFormula()
    {
        Formula n = Var("n"), j = Var("j"), k = Var("k");
        var v0 = All("k", FinN(n), Eqn(At(Fn("simplexVertex", n, Num(0)), k), Num(1)));
        var vj = All("j", FinN(n), All("k", FinN(n),
            Eqn(At(Fn("simplexVertex", n, Fn("succ", j)), k),
                Multiply(Multiply(Pow(NegOf(Num(1)), k), Pow(Inv(Num(3)), Add(j, Num(1)))),
                    Fn("choose", j, k)))));
        return All("n", NatT, Conj(v0, vj));
    }

    private static Formula JointKFidelityVecFormula()
    {
        Formula n = Var("n"), r = Var("r"), l = Var("L"), k = Var("k");
        return All("n", NatT, All("r", SicFamN(n), All("L", QMap(n), All("k", FinN(n),
            Eqn(At(Fn("jointKFidelityVec", r, l), k), Fn("realKFidelity", r, k, l))))));
    }

    private static Formula JointKFidelityRangeFormula()
    {
        Formula n = Var("n"), r = Var("r"), v = Var("v"), l = Var("L");
        var set = FilterSet("v", Arrow(FinN(n), RealT), Ex("L", QMap(n), Conj3(
            Fn("IsCompletelyPositive", l),
            Fn("IsTracePreserving", l),
            Eqn(v, Fn("jointKFidelityVec", r, l)))));
        return All("n", NatT, All("r", SicFamN(n), Eqn(Fn("jointKFidelityRange", n, r), set)));
    }

    private static Formula TpExactReconstructionFormula()
    {
        Formula n = Var("n"), r = Var("r"), i = Var("i"), l = Var("L"), k = Var("k");
        var localR = All("i", FinN(n), Fn("IsQubitSICProjector", At(r, i)));
        var cSum = SumIn("k", Fn("range", n), Multiply(NegTwoPow(k), Fn("kFidelity", r, k, l)));
        var rSum = SumIn("k", Fn("range", n), Multiply(NegTwoPow(k), Fn("realKFidelity", r, k, l)));
        var invNeg2n = Inv(NegTwoPow(n));
        var cRel = Eqn(Add(Multiply(Num(3), cSum), Multiply(NegTwoPow(n), Fn("processFidelity", l))), Num(1));
        var cRec = Eqn(Fn("processFidelity", l), Multiply(invNeg2n, Subtract(Num(1), Multiply(Num(3), cSum))));
        var rRel = Eqn(Add(Multiply(Num(3), rSum), Multiply(NegTwoPow(n), Fn("realProcessFidelity", l))), Num(1));
        var rRec = Eqn(Fn("realProcessFidelity", l),
            Multiply(invNeg2n, Subtract(Num(1), Multiply(Num(3), rSum))));
        return All("n", NatT, All("r", SicFamN(n), Imp(localR, All("L", QMap(n),
            Imp(Fn("IsTracePreserving", l), Conj3(cRel, cRec,
                Imp(Fn("IsCompletelyPositive", l), Conj(rRel, rRec))))))));
    }

    private static Formula CptpJointRangeFormula()
    {
        Formula n = Var("n"), r = Var("r"), i = Var("i"), l = Var("L"), c = Var("c"), k = Var("k");
        var localR = All("i", FinN(n), Fn("IsQubitSICProjector", At(r, i)));
        var finN1 = FinN(Add(n, Num(1)));
        var sv = Fn("simplexVertex", n);
        var jVec = Fn("jointKFidelityVec", r, l);
        var c1 = Fn("AffineIndependent", RealT, sv);
        var c2 = Eqn(Fn("jointKFidelityRange", n, r), Fn("convexHull", RealT, Fn("range", sv)));
        var baryUnique = All("c", Arrow(finN1, RealT),
            Imp(Eqn(SumIn("i", finN1, At(c, i)), Num(1)),
                Imp(Eqn(SumIn("i", finN1, Multiply(At(c, i), Fn("simplexVertex", n, i))), jVec),
                    All("i", finN1, Eqn(At(c, i), Fn("realWeightSum", l, i))))));
        var c3 = All("L", QMap(n), Imp(Fn("IsCompletelyPositive", l), Imp(Fn("IsTracePreserving", l),
            Conj4(
                All("i", finN1, LeRel(Num(0), Fn("realWeightSum", l, i))),
                Eqn(SumIn("i", finN1, Fn("realWeightSum", l, i)), Num(1)),
                Eqn(SumIn("i", finN1, Multiply(Fn("realWeightSum", l, i), Fn("simplexVertex", n, i))), jVec),
                baryUnique))));
        var recSum = SumIn("k", FinN(n), Multiply(NegTwoPow(k), At(jVec, k)));
        var c4 = All("L", QMap(n), Imp(Fn("IsCompletelyPositive", l), Imp(Fn("IsTracePreserving", l),
            Conj(
                Eqn(Fn("realProcessFidelity", l), Fn("realWeightSum", l, Num(0))),
                Eqn(Fn("realProcessFidelity", l),
                    Multiply(Inv(NegTwoPow(n)), Subtract(Num(1), Multiply(Num(3), recSum))))))));
        return All("n", NatT, All("r", SicFamN(n), Imp(localR, Conj4(c1, c2, c3, c4))));
    }
}
