using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class ConcentratableEntanglementSubsystemRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/ConcentratableEntanglementSubsystemRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/liu2025generalized");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Liu, Knörzer, Wang and Tura (arXiv:2406.18517, Phys. Rev. Research 7, L032022) define the generalized concentratable entanglement C^{(K)}_psi(s) = (1 - 2^{-|s|} sum_{alpha in P(s)} Tr(rho_alpha^K)) / (K - 1) of an n-qubit pure state, with Tr(rho_emptyset^K) = 1, and conjecture that C^{(K)}_psi(s') <= C^{(K)}_psi(s) whenever s' is a subset of s, for every real K > 1. It fails at K = 5/2 for a four-qubit state with integer amplitudes: removing one qubit from {0, 1, 2} raises the value.",
        H("Generalized concentratable entanglement is not monotone under enlarging the subsystem"),
        Blocks(
            Node("power-trace", "The trace of a power of a reduced state", PowerTraceFormula(),
                "Tr(rho_alpha^K) is the real part of the trace of the K-th power, in the continuous functional calculus, of the existing reducedState of psi on the qubits alpha; the empty set contributes 1, as the paper takes Tr(rho_emptyset^K) = 1.",
                "powerTrace", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("gce", "Generalized concentratable entanglement", GceFormula(),
                "Eq. (defeq): C^{(K)}_psi(s) = (1 - 2^{-|s|} sum_{alpha in P(s)} Tr(rho_alpha^K)) / (K - 1), the sum running over all subsets alpha of s.",
                "gce", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured monotonicity", ClaimFormula(),
                "Conjecture 1(1): for every number of qubits N, every normalized N-qubit vector psi, all subsets t of s of the qubits and every real K > 1, the value on t is at most the value on s.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("coeff", "The amplitudes", CoeffFormula(),
                "The unnormalized amplitudes are -1100, -100, -100, 75 and -9 on the basis states |0000>, |0101>, |1010>, |1100> and |1111>; their squares sum to 1235706.",
                "coeff", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("psi", "The counterexample state", PsiFormula(),
                "The state is the amplitude vector divided by sqrt(1235706).",
                "psi", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("triple-equiv", "Coordinates of three qubits", TripleEquivFormula(),
                "tripleEquiv reads a configuration x of the qubits {0, 1, 2} as (x(0), x(1), x(2)).",
                "tripleEquiv", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("out1-equiv", "Coordinate outside three qubits", Out1EquivFormula(),
                "out1Equiv reads a configuration z of the qubit outside {0, 1, 2} as its value z(3).",
                "out1Equiv", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "Enlarging the subsystem can lower the value", Disp(new Formula.Not(F.Id("claim"))),
                "Take N = 4, K = 5/2, t = {0, 1} and s = {0, 1, 2}. The reduced states of psi, scaled by 1235706, are: on one qubit diag(1220000, 15706) for the qubits 0 and 1 and diag(1225625, 10081) for the qubit 2; on {0, 1}, {0, 2} and {1, 2} a direct sum of diagonal entries and one 2 x 2 block, with block determinants 9900^2, 100^2 and 10000^2; on {0, 1, 2} the rank-two matrix u u^T + w w^T with u and w orthogonal of squared norms 1225625 and 10081. Write Q = 1235706 rho for each of them. Each Q has an explicit positive semidefinite square root S, with S^2 = Q: square roots of the diagonal entries, (M + sqrt(det M) I) / sqrt(tr M + 2 sqrt(det M)) on a 2 x 2 block M, and u u^T / |u| + w w^T / |w|. Hence rho^{5/2} = (S / sqrt(1235706))^5 and Tr(rho^{5/2}) = Tr(Q^2 S) / 1235706^{5/2}. With T_alpha = Tr(rho_alpha^{5/2}), 8 (K - 1) (C(t) - C(s)) = T_2 + T_{02} + T_{12} + T_{012} - 1 - T_0 - T_1 - T_{01}; rational bounds for eight square roots show that it is about 5.77 * 10^{-7} > 0, so C^{(5/2)}({0, 1}) > C^{(5/2)}({0, 1, 2}).",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("liu-2025-gce-subsystem-monotonicity"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("gce-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Of(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula EqTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula LeTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Frac(Formula top, Formula bottom) => new Formula.Fraction(top, bottom);
    private static Formula Pow(Formula b, Formula e) => new Formula.Power(b, e);
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula Root(Formula x) => Seq(Sqrt, Grp(x));
    private static Formula NumberSet(Formula name) => Seq(Mathbb, Grp(name));
    private static Formula Real() => NumberSet(F.Id("R"));
    private static Formula Complex() => NumberSet(F.Id("C"));
    private static Formula Nat() => NumberSet(F.Id("N"));
    private static Formula Fin(Formula n) => Call(F.Id("Fin"), n);
    private static Formula Vars(params Formula[] names)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        for (var i = 0; i < names.Length; i++)
        {
            if (i > 0)
            {
                parts.Add(Comma);
                parts.Add(Sp);
            }
            parts.Add(names[i]);
        }
        return Seq([.. parts]);
    }
    private static Formula SetOf(params Formula[] items) => Seq(Esc, OpenBrace, Vars(items), Esc, CloseBrace);
    private static Formula Configs(Formula set) => Parenthesized(Seq(set, Sp, To, Sp, Fin(D(2))));
    private static Formula Vectors(Formula n) =>
        Seq(Parenthesized(Seq(Fin(n), Sp, To, Sp, Fin(D(2)))), Sp, To, Sp, Complex());
    private static Formula Subsets(Formula n) => Call(F.Id("Finset"), Fin(n));
    private static Formula ReTr(Formula x) => Call(F.Id("ReTr"), x);
    private static Formula Ket(params byte[] digits) => Seq(Bar, D(digits), Rangle);

    private static Formula PowerTraceFormula()
    {
        Formula n = F.Id("N"), k = F.Id("K"), psi = F.Id("psi"), alpha = F.Id("alpha");
        Formula empty = EqTo(Call(F.Id("powerTrace"), k, psi, Emptyset), D(1));
        Formula nonempty = Imp(Rel(alpha, FormulaRelationOperator.NotEqual, Emptyset),
            EqTo(Call(F.Id("powerTrace"), k, psi, alpha),
                ReTr(Pow(Call(F.Id("reducedState"), alpha, psi), k))));
        return Disp(All(n, Nat(), All(k, Real(), All(psi, Vectors(n),
            Logic(empty, FormulaLogicOperator.And, All(alpha, Subsets(n), nonempty))))));
    }

    private static Formula GceFormula()
    {
        Formula n = F.Id("N"), k = F.Id("K"), psi = F.Id("psi"), s = F.Id("s"), alpha = F.Id("alpha");
        Formula sum = Seq(Sum, Underscore, Grp(Seq(alpha, Sp, Subseteq, Sp, s)), Sp,
            Call(F.Id("powerTrace"), k, psi, alpha));
        Formula value = Mul(Frac(D(1), Sub(k, D(1))),
            Parenthesized(Sub(D(1), Mul(Frac(D(1), Pow(D(2), Seq(Bar, s, Bar))), sum))));
        return Disp(All(n, Nat(), All(k, Real(), All(psi, Vectors(n), All(s, Subsets(n),
            EqTo(Call(F.Id("gce"), k, psi, s), value))))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("N"), psi = F.Id("psi"), w = F.Id("w"), t = F.Id("t"), s = F.Id("s"), k = F.Id("K");
        Formula normalized = EqTo(Seq(Sum, Underscore, Grp(w), Sp, Pow(Norm(Of(psi, w)), D(2))), D(1));
        Formula mono = LeTo(Call(F.Id("gce"), k, psi, t), Call(F.Id("gce"), k, psi, s));
        Formula body = Imp(normalized, All(Vars(t, s), Subsets(n),
            Imp(Rel(t, FormulaRelationOperator.SubsetOf, s),
                All(k, Real(), Imp(Rel(D(1), FormulaRelationOperator.LessThan, k), mono)))));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            All(n, Nat(), All(psi, Vectors(n), body))));
    }

    private static Formula Amplitudes() =>
        Sub(Add(Sub(Sub(Mul(Seq(Minus, D(1, 1, 0, 0)), Ket(0, 0, 0, 0)), Mul(D(1, 0, 0), Ket(0, 1, 0, 1))),
            Mul(D(1, 0, 0), Ket(1, 0, 1, 0))), Mul(D(7, 5), Ket(1, 1, 0, 0))), Mul(D(9), Ket(1, 1, 1, 1)));

    private static Formula CoeffFormula() => Disp(EqTo(F.Id("coeff"), Amplitudes()));

    private static Formula PsiFormula()
    {
        Formula w = F.Id("w");
        return Disp(All(w, Configs(Fin(D(4))),
            EqTo(Of(F.Id("psi"), w), Frac(Of(F.Id("coeff"), w), Root(D(1, 2, 3, 5, 7, 0, 6))))));
    }

    private static Formula TripleEquivFormula()
    {
        Formula x = F.Id("x");
        return Disp(All(x, Configs(SetOf(D(0), D(1), D(2))),
            EqTo(Call(F.Id("tripleEquiv"), x), Parenthesized(Vars(Of(x, D(0)), Of(x, D(1)), Of(x, D(2)))))));
    }

    private static Formula Out1EquivFormula()
    {
        Formula z = F.Id("z");
        return Disp(All(z, Configs(Call(F.Id("Outside"), SetOf(D(0), D(1), D(2)))),
            EqTo(Call(F.Id("out1Equiv"), z), Of(z, D(3)))));
    }
}
