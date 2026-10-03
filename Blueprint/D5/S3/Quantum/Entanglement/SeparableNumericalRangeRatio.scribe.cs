using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class SeparableNumericalRangeRatioDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SeparableNumericalRangeRatio.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/simnacher2021separable");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a single two-qubit observable A, the length of the separable numerical range is at least half the length of the numerical range, and the projector onto (|00> + |11>)/sqrt(2) attains one half. This proves Conjecture 8 of T. Simnacher, J. Czartowski, K. Szymański and K. Życzkowski (arXiv:2107.04365): the minimal volume ratio mu_{2,1} equals 1/2.",
        H("The separable numerical range of one two-qubit observable"),
        Blocks(
            Node("separable", "Separable states", SeparableFormula(),
                "A separable two-qubit state is a state that is a finite sum of Kronecker products of positive semidefinite 2 x 2 matrices; equivalently, a convex combination of product states.",
                "separableStates", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("range", "Restricted numerical ranges", RangeFormula(),
                "For a set X of states and a matrix A, the restricted numerical range L_X(A) is the set of real parts of Tr(rho A) over rho in X. For Hermitian A and a state rho the trace is real.",
                "numericalRange", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimFormula(),
                "One half is the least value of vol L_Sep(A) / vol L(A) over Hermitian two-qubit matrices A with vol L(A) not zero, where vol is Lebesgue measure on the real line, L(A) is the numerical range over all two-qubit density matrices (IsDensity: positive semidefinite with trace 1) and L_Sep(A) the numerical range over separable states. For scalar A both ranges are points, so the ratio is defined exactly when A is not scalar. The least value is attained, so it is the minimum of the paper's Definition 2 for n = 2, d = 2 and k = 1.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The minimal ratio is one half", Disp(F.Id("claim")),
                "In the magic basis a two-qubit vector u is a product vector exactly when the sum of the squares of its four coordinates vanishes. After a phase, a unit vector z has z^T z = C with 0 <= C <= 1. For a real unit vector r orthogonal to the real part of z, the vectors z + i t r with t = -eta +- sqrt(eta^2 + C), eta = (Im z) . r, are product vectors, and a convex combination of their projectors equals zz^* + C rr^T; so zz^* + C rr^T is separable. For two unit vectors u and v, two orthonormal real vectors r and s orthogonal to the real parts of both give one separable noise N = (rr^T + ss^T)/2 with trace 1, and with c = max(C_u, C_v) the matrices (P_u + cN)/(1 + c) and (P_v + cN)/(1 + c) are separable states whose difference is (P_u - P_v)/(1 + c). Hence the expectation values of A at two pure states differ by at most 2 times the length of L_Sep(A); by the spectral decomposition of states the same holds for any two states, so vol L(A) <= 2 vol L_Sep(A), using that L_Sep(A) is an interval. For the Bell projector, L(A) contains [0, 1] and every product state has expectation (1/2) times the sum over a, b of sigma_ab tau_ab, which lies in [0, 1/2]; so the ratio is at most 1/2, and therefore equal to 1/2.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("simnacher-2021-two-qubit-separable-numerical-range-ratio"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("snr-" + id), DeclarationHandle.Create(Prefix + declaration),
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
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Frac(Formula top, Formula bottom) => new Formula.Fraction(top, bottom);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Mat() =>
        Seq(Mathbb, Grp(F.Id("C")), Caret, Grp(Seq(D(4), Times, D(4))));
    private static Formula Member(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula SetOf(Formula element, Formula binder, Formula domain) =>
        Seq(Esc, OpenBrace, element, Sp, Mid, Sp, Member(binder, domain), Esc, CloseBrace);
    private static Formula SetOfWhere(Formula element, Formula binder, Formula domain, Formula condition) =>
        Seq(Esc, OpenBrace, element, Sp, Mid, Sp, Member(binder, domain), Comma, Sp, condition,
            Esc, CloseBrace);
    private static Formula Trace(Formula m) => Call(F.Id("Tr"), m);

    private static Formula SeparableFormula()
    {
        Formula rho = Rho;
        return Disp(All(rho, Mat(), Iff(Member(rho, Named(F.Id("separableStates"))),
            And(Call(F.Id("separableCone"), rho), Equal(Trace(rho), D(1))))));
    }

    private static Formula RangeFormula()
    {
        Formula rho = Rho, a = F.Id("A"), x = F.Id("X");
        Formula value = Call(F.Id("Re"), Trace(Seq(rho, Sp, a)));
        return Disp(Seq(Forall, Sp, x, Sp, Subseteq, Sp, Mat(), Comma, Sp,
            All(a, Mat(), Equal(Call(F.Id("numericalRange"), x, a), SetOf(value, rho, x)))));
    }

    private static Formula ClaimFormula()
    {
        Formula a = F.Id("A");
        Formula vol = F.Id("vol");
        Formula rho = Rho;
        Formula densities = SetOfWhere(rho, rho, Mat(), Call(F.Id("IsDensity"), rho));
        Formula full = Call(vol, Call(F.Id("numericalRange"), densities, a));
        Formula sep = Call(vol, Call(F.Id("numericalRange"), Named(F.Id("separableStates")), a));
        Formula hermitian = Equal(Seq(a, Caret, Grp(Star)), a);
        Formula nonzero = Rel(full, FormulaRelationOperator.NotEqual, D(0));
        Formula ratios = SetOfWhere(Frac(sep, full), a, Mat(), And(hermitian, nonzero));
        return Disp(Iff(F.Id("claim"), Call(F.Id("IsLeast"), ratios, Frac(D(1), D(2)))));
    }
}
