using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class PropertyTCirculantUniversalTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/PropertyTCirculantUniversalTransfer.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/connelly2017universality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The circulant Circ(0, a, conj(a)) with a = (-4 sqrt(3) + i)/7 is a Hermitian circulant on three vertices whose nonzero entries have modulus 1 and whose continuous-time quantum walk has perfect state transfer between every pair of vertices, yet it is switching equivalent neither to K_2 nor to Circ(0, -i, i). This refutes the conjecture of E. Connelly, N. Grammel, M. Kraut, L. Serazo and C. Tamon (arXiv:1701.04145) that these two are the only circulants with property T and universal perfect state transfer.",
        H("A property-T circulant with universal perfect state transfer"),
        Blocks(
            Node("property-t", "Property T", PropertyTFormula(),
                "A matrix A has property T when every nonzero entry of A has modulus 1. For the adjacency matrix of a graph this says that the graph is a complex unit gain graph.",
                "PropertyT", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("upst", "Universal perfect state transfer", UpstFormula(),
                "The continuous-time quantum walk of a Hermitian matrix A is U(t) = exp(-i t A). There is perfect state transfer from u to v at time t when the (v, u) entry of U(t) has modulus 1, and A has universal perfect state transfer when this happens, at some real time, for all vertices u and v.",
                "UPST", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("switching", "Switching equivalence", SwitchingFormula(),
                "A monomial matrix is the product of a permutation matrix and an invertible diagonal matrix, and two matrices A and B are switching equivalent when M A = B M for some monomial matrix M. Here M is the permutation matrix of a bijection sigma between the vertex sets times the diagonal matrix of a vector d with no zero entry.",
                "SwitchingEquivalent", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("k2", "The complete graph on two vertices", K2Formula(),
                "The circulant Circ(0, 1) on Z/2Z, the adjacency matrix of K_2. Here Circ(a) is the circulant matrix with entries Circ(a)_(jk) = a_(k - j), the transpose of the circulant matrix of Mathlib.",
                "K2", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("triangle", "The oriented triangle", TriangleFormula(),
                "The circulant Circ(0, -i, i) on Z/3Z, the oriented triangle, which has universal perfect state transfer.",
                "orientedTriangle", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimFormula(),
                "The conjecture of the paper, read together with its introduction, which names K_2 and Circ(0, -i, i) as the only known examples and conjectures that this set is unique: every Hermitian circulant Circ(a) on Z/nZ with n at least 2, without loops (a_0 = 0), with property T and universal perfect state transfer is switching equivalent to K_2 or to Circ(0, -i, i).",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A counterexample on three vertices", Disp(new Formula.Not(F.Id("claim"))),
                "Let a = (-4 sqrt(3) + i)/7, so that |a| = 1, and let A = Circ(0, a, conj(a)) on Z/3Z. Then A is Hermitian, has no loops and has property T. The Fourier matrix V with entries omega^(km), where omega = exp(2 pi i/3), satisfies A V = V diag(mu) with eigenvalues mu = (sqrt(3)/7)(-8, 3, 5). At t_1 = 14 sqrt(3) pi/9 the numbers -i t_1 mu_m are 2 pi i/3 times 2, 0 and 1 modulo 2 pi i, so exp(-i t_1 A) = V diag(omega^2, 1, omega) V^(-1) = omega^2 P, where P is the cyclic permutation matrix with P_(jk) = 1 exactly when k = j + 1. Hence U(t_1) = omega^2 P, U(2 t_1) = U(t_1)^2 = omega^4 P^2 and U(0) = I, and every entry of these matrices on the relevant pair of vertices has modulus 1, which gives universal perfect state transfer. The vertex sets of A and K_2 have 3 and 2 elements, so there is no bijection between them. A monomial matrix M has nonzero determinant, so M A = B M gives det A = det B; but det A = a^3 + conj(a)^3 = -360 sqrt(3)/343, while det Circ(0, -i, i) = 0. So A is switching equivalent to neither.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("connelly-2017-property-t-universal-state-transfer"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("upst-" + id), DeclarationHandle.Create(Prefix + declaration),
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
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula AllOf(Formula variables, Formula body) =>
        Seq(Forall, Sp, variables, Comma, Sp, body);
    private static Formula SomeIn(Formula variable, Formula domain, Formula body) =>
        Seq(Exists, Sp, variable, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula SomeOf(Formula variable, Formula body) =>
        Seq(Exists, Sp, variable, Comma, Sp, body);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Entry(Formula matrix, Formula row, Formula column) =>
        new Formula.Apply(matrix, [row, column]);
    private static Formula Circulant(params Formula[] coefficients) =>
        Call(F.Id("Circ"), coefficients);

    private static Formula PropertyTFormula()
    {
        Formula a = F.Id("A"), j = F.Id("j"), k = F.Id("k");
        Formula entry = Entry(a, j, k);
        Formula body = AllOf(Seq(j, Sp, k),
            Implies(Rel(entry, FormulaRelationOperator.NotEqual, D(0)),
                Equal(new Formula.Norm(entry), D(1))));
        return Disp(Iff(Call(F.Id("PropertyT"), a), body));
    }

    private static Formula UpstFormula()
    {
        Formula a = F.Id("A"), u = F.Id("u"), v = F.Id("v"), t = F.Id("t");
        Formula entry = Call(F.Id("hamiltonianPropagator"), a, t, v, u);
        Formula body = AllOf(Seq(u, Sp, v),
            SomeIn(t, Reals(), Equal(new Formula.Norm(entry), D(1))));
        return Disp(Iff(Call(F.Id("UPST"), a), body));
    }

    private static Formula SwitchingFormula()
    {
        Formula a = F.Id("A"), b = F.Id("B"), d = F.Id("d"), i = F.Id("i");
        Formula monomial = Seq(Call(F.Id("perm"), SigmaLower), Sp, Call(F.Id("diag"), d));
        Formula nonzero = AllOf(i, Rel(new Formula.Apply(d, [i]),
            FormulaRelationOperator.NotEqual, D(0)));
        Formula intertwine = Equal(Seq(monomial, Sp, a), Seq(b, Sp, monomial));
        Formula body = SomeOf(SigmaLower, SomeOf(d, And(nonzero, intertwine)));
        return Disp(Iff(Call(F.Id("SwitchingEquivalent"), a, b), body));
    }

    private static Formula K2Formula() =>
        Disp(Equal(Named(F.Id("K2")), Circulant(D(0), D(1))));

    private static Formula TriangleFormula() =>
        Disp(Equal(Named(F.Id("orientedTriangle")),
            Circulant(D(0), new Formula.Negate(F.Id("i")), F.Id("i"))));

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), a = F.Id("a");
        Formula circ = Circulant(a);
        Formula coefficients = Seq(Call(F.Id("ZMod"), n), Sp, To, Sp, Complexes());
        Formula conclusion = Or(Call(F.Id("SwitchingEquivalent"), circ, Named(F.Id("K2"))),
            Call(F.Id("SwitchingEquivalent"), circ, Named(F.Id("orientedTriangle"))));
        Formula hypotheses =
            Implies(Equal(new Formula.Apply(a, [D(0)]), D(0)),
                Implies(Call(F.Id("IsHermitian"), circ),
                    Implies(Call(F.Id("PropertyT"), circ),
                        Implies(Call(F.Id("UPST"), circ), conclusion))));
        Formula body = AllOf(n,
            Implies(Rel(n, FormulaRelationOperator.GreaterThanOrEqual, D(2)),
                Seq(Forall, Sp, a, Sp, Colon, Sp, coefficients, Comma, Sp, hypotheses)));
        return Disp(Iff(F.Id("claim"), body));
    }
}
