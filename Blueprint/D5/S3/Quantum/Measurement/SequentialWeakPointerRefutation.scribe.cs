using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class SequentialWeakPointerRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/abbott2019anomalous");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For three sequential weak measurements of projection observables on a pure state, without post-selection, the mean product of the pointer positions can be -1/6, below -1/8. This refutes the conjecture of A. A. Abbott, R. Silva, J. Wechs, N. Brunner and C. Branciard (arXiv:1805.09364) that -1/8 bounds this mean for every number of projection observables.",
        H("Three weak measurements of projections below minus one eighth"),
        Blocks(
            Node("nested", "Nested anticommutator", NestedFormula(),
                "The nested anticommutator of n + 1 matrices A_0, ..., A_n is A_0 for n = 0 and {A_0, {A_1, ..., {A_(n-1), A_n}...}} in general, defined by recursion on n; A o succ denotes the family A_1, ..., A_n.",
                "nestedAnti", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("mean", "Mean product of the pointer positions", MeanFormula(),
                "In the weak regime without post-selection, the mean product of the pointer positions of n + 1 sequential measurements of A_0, ..., A_n on the pure state psi is 2^(-n) times the real part of <psi, N psi>, where N is the nested anticommutator and <psi, phi> is the sum over i of the conjugate of psi_i times phi_i.",
                "pointerMean", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured bound minus one eighth", ClaimFormula(),
                "The conjecture: for every dimension d, every number n + 1 of observables, every family of orthogonal projections A_i on C^d (A_i^2 = A_i and A_i^* = A_i, the projection observables with eigenvalues 0 and 1) and every unit vector psi, the mean product of the pointer positions is at least -1/8. The paper proves this bound for two observables.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A sequence of three projections below minus one eighth",
                Disp(new Formula.Not(F.Id("claim"))),
                "Take d = 3, the state e_3, and the rational projections P_1 = (1/3)[[1, 1, -1], [1, 1, -1], [-1, -1, 1]] onto (1, 1, -1), P_2 = [[1, 0, 0], [0, 1/2, 1/2], [0, 1/2, 1/2]] = I - v v^* with v = (0, 1, -1)/sqrt(2), and P_3 = [[1/2, 0, 1/2], [0, 1, 0], [1/2, 0, 1/2]] = I - w w^* with w = (1, 0, -1)/sqrt(2). Each satisfies P^2 = P = P^*, checked entrywise, and e_3 is a unit vector. Evaluating the nested anticommutator gives (1/4) <e_3, {P_1, {P_2, P_3}} e_3> = -1/6 < -1/8, so the conjectured bound fails for three observables.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("weakpointer-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula FinOf(Formula n) => Call(F.Id("Fin"), n);
    private static Formula MatrixType(Formula d) =>
        Seq(Complexes(), Caret, Grp(d, F.Times, Sp, d));
    private static Formula FamilyType(Formula n, Formula d) =>
        Seq(FinOf(Add(n, D(1))), Sp, To, Sp, MatrixType(d));
    private static Formula Inner(Formula left, Formula right) =>
        Seq(Langle, left, Comma, Sp, right, Rangle);
    private static Formula Nested(Formula n, Formula family) => Call(F.Id("nestedAnti"), n, family);
    private static Formula Mean(Formula family, Formula state) =>
        Call(F.Id("pointerMean"), family, state);

    private static Formula NestedFormula()
    {
        Formula n = F.Id("n"), a = F.Id("A");
        Formula a0 = new Formula.Apply(a, [D(0)]);
        Formula tail = Seq(a, Sp, Circ, Sp, Named(F.Id("succ")));
        Formula inner = Nested(n, tail);
        Formula zero = Equal(Nested(D(0), a), a0);
        Formula step = Equal(Nested(Add(n, D(1)), a), Add(Mul(a0, inner), Mul(inner, a0)));
        return Disp(Seq(zero, Comma, Qquad, step));
    }

    private static Formula MeanFormula()
    {
        Formula n = F.Id("n"), a = F.Id("A"), psi = Psi;
        Formula scale = Seq(D(2), Caret, Grp(Minus, n));
        Formula value = Seq(Operatorname, Grp(F.Id("Re")), Sp,
            Inner(psi, Seq(Nested(n, a), Sp, psi)));
        return Disp(Equal(Mean(a, psi), Mul(scale, value)));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("d"), n = F.Id("n"), a = F.Id("A"), i = F.Id("i"), psi = Psi;
        Formula ai = new Formula.Apply(a, [i]);
        Formula projections = All(i, FinOf(Add(n, D(1))), Call(F.Id("IsStarProjection"), ai));
        Formula unit = Equal(Inner(psi, psi), D(1));
        Formula bound = Rel(new Formula.Negate(new Formula.Fraction(D(1), D(8))),
            FormulaRelationOperator.LessThanOrEqual, Mean(a, psi));
        Formula stateType = Seq(Complexes(), Caret, Grp(d));
        Formula body = All(d, Naturals(), All(n, Naturals(), All(a, FamilyType(n, d),
            Implies(projections, All(psi, stateType, Implies(unit, bound))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
