using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class QunitRealWeakValueRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/QunitRealWeakValueRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/farinholt2015weak");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For the standard basis of C^3 and the real orthonormal basis given by the columns of (1/3)[[1, 2, 2], [2, 1, -2], [2, -2, 1]], every pair of basis vectors is distinct and nonorthogonal, and the traceless Hermitian matrix M = E_01 + E_10 has all nine weak values real, while M is not in the real span of the traceless projectors of the two bases. This refutes the conjecture of J. M. Farinholt, A. Ghazarians and J. E. Troupe (arXiv:1512.02113) that all weak values of a traceless observable are real exactly when it lies in that span.",
        H("Real weak values outside the projector span for qutrits"),
        Blocks(
            Node("weak", "Weak values", WeakFormula(),
                "For a pre-selected state phi and a post-selected state psi of C^n and an n x n matrix M, the weak value is <psi|M|phi> / <psi|phi>, with the bar denoting complex conjugation (star in Lean).",
                "weakValue", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("onb", "Orthonormal bases", OnbFormula(),
                "A family b_0, ..., b_(n-1) of vectors of C^n, written b_ik for the k-th coordinate of b_i, is an orthonormal basis when <b_i|b_j> is 1 for i = j and 0 otherwise.",
                "IsONB", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("proj", "Traceless projectors", ProjFormula(),
                "The traceless part of the projector onto v is |v><v| - I/n, whose (a, b) entry is v_a times the conjugate of v_b, minus 1/n on the diagonal.",
                "tracelessProj", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("span", "The real span of the two bases", SpanFormula(),
                "R(phi, psi) is the real linear span, inside the complex n x n matrices viewed as a real vector space, of the 2n traceless projectors of the two bases. All of them are traceless Hermitian, so this is the paper's span inside the space S of traceless Hermitian matrices.",
                "realSpan", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimFormula(),
                "For every n >= 2 and all orthonormal bases phi, psi of C^n such that every pair (phi_i, psi_j) is distinct and nonorthogonal, a traceless Hermitian matrix M has all weak values W(phi_i, psi_j, M) real exactly when M lies in R(phi, psi). The paper requires phi_0 and psi_0 to be distinct and nonorthogonal and defines weak values for distinct, nonorthogonal pairs; assuming this for every pair, so that every weak value in the statement is defined, only weakens the claim.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A qutrit counterexample", Disp(new Formula.Not(F.Id("claim"))),
                "Take n = 3, phi_i the standard basis vectors and psi_j the j-th column of O = (1/3)[[1, 2, 2], [2, 1, -2], [2, -2, 1]], an orthogonal matrix, so both families are orthonormal bases; the overlap <psi_j|phi_i> is the entry O_ij, never 0, and no phi_i equals a psi_j. For M = E_01 + E_10 the nine weak values are 2, 1/2, -1, 1/2, 2, -1, 0, 0, 0 (in the order (i, j) = (0, 0), (0, 1), ...), all real. If M were a real combination of the six traceless projectors, the off-diagonal entries (0, 1), (0, 2), (1, 2) would come only from the psi projectors and give (2 b_0 + 2 b_1 - 4 b_2)/9 = 1, (2 b_0 - 4 b_1 + 2 b_2)/9 = 0 and (4 b_0 - 2 b_1 - 2 b_2)/9 = 0; the last two force b_0 = b_1 = b_2, and then the first reads 0 = 1.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("farinholt-2015-qunit-real-weak-values"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("realweak-" + id), DeclarationHandle.Create(Prefix + declaration),
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
    private static Formula NotEqual(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Le(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Sub(Formula value, Formula index) => new Formula.Subscript(value, index);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Minus(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Conj(Formula value) => Seq(Overline, Grp(value));
    private static Formula SumOver(Formula index, Formula body) =>
        Seq(F.Sum, Underscore, Grp(index), Sp, body);
    private static Formula Ite(Formula condition, Formula then, Formula otherwise) =>
        Call(F.Id("ite"), condition, then, otherwise);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Fin(Formula n) => Call(F.Id("Fin"), n);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Vector(Formula n) => Arrow(Fin(n), Complex());
    private static Formula Basis(Formula n) => Arrow(Fin(n), Parenthesized(Vector(n)));
    private static Formula MatrixType(Formula n) => Call(F.Id("Matrix"), Fin(n), Fin(n), Complex());
    private static Formula Inner(Formula left, Formula right, Formula k) =>
        SumOver(k, Times(Conj(Sub(left, k)), Sub(right, k)));
    private static Formula Entry(Formula vector, Formula index) => Sub(vector, index);
    private static Formula Entry2(Formula vector, Formula i, Formula k) => Sub(vector, Seq(i, k));

    private static Formula WeakFormula()
    {
        Formula n = F.Id("n"), phi = F.Phi, psi = F.Psi, m = F.Id("M"), k = F.Id("k"), l = F.Id("l");
        Formula numerator = SumOver(k, SumOver(l,
            Times(Times(Conj(Entry(psi, k)), Sub(m, Seq(k, l))), Entry(phi, l))));
        Formula value = new Formula.Fraction(numerator, Inner(psi, phi, k));
        return Disp(All(n, Nat(), All(phi, Vector(n), All(psi, Vector(n), All(m, MatrixType(n),
            Equal(Call(F.Id("weakValue"), phi, psi, m), value))))));
    }

    private static Formula OnbFormula()
    {
        Formula n = F.Id("n"), b = F.Id("b"), i = F.Id("i"), j = F.Id("j"), k = F.Id("k");
        Formula inner = SumOver(k, Times(Conj(Entry2(b, i, k)), Entry2(b, j, k)));
        Formula body = All(i, Fin(n), All(j, Fin(n), Equal(inner, Ite(Equal(i, j), D(1), D(0)))));
        return Disp(All(n, Nat(), All(b, Basis(n), Iff(Call(F.Id("IsONB"), b), body))));
    }

    private static Formula ProjFormula()
    {
        Formula n = F.Id("n"), v = F.Id("v"), a = F.Id("a"), c = F.Id("c");
        Formula entry = Sub(Call(F.Id("tracelessProj"), v), Seq(a, c));
        Formula value = Minus(Times(Entry(v, a), Conj(Entry(v, c))),
            Ite(Equal(a, c), new Formula.Fraction(D(1), n), D(0)));
        return Disp(All(n, Nat(), All(v, Vector(n), All(a, Fin(n), All(c, Fin(n), Equal(entry, value))))));
    }

    private static Formula SpanFormula()
    {
        Formula n = F.Id("n"), phi = F.Phi, psi = F.Psi, i = F.Id("i"), j = F.Id("j");
        Formula generators = Seq(OpenBrace, Call(F.Id("tracelessProj"), Sub(phi, i)), Comma, Sp,
            Call(F.Id("tracelessProj"), Sub(psi, j)), Sp, Colon, Sp, i, Comma, Sp, j, Sp, InMacro, Sp,
            Fin(n), CloseBrace);
        Formula span = Seq(Sub(Named(F.Id("span")), Seq(Mathbb, Grp(F.Id("R")))), generators);
        return Disp(All(n, Nat(), All(phi, Basis(n), All(psi, Basis(n),
            Equal(Call(F.Id("realSpan"), phi, psi), span)))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), phi = F.Phi, psi = F.Psi, m = F.Id("M"), i = F.Id("i"), j = F.Id("j"), k = F.Id("k");
        Formula overlaps = All(i, Fin(n), All(j, Fin(n),
            NotEqual(SumOver(k, Times(Conj(Entry2(psi, j, k)), Entry2(phi, i, k))), D(0))));
        Formula distinct = All(i, Fin(n), All(j, Fin(n), NotEqual(Sub(phi, i), Sub(psi, j))));
        Formula hypotheses = And(Le(D(2), n), And(Call(F.Id("IsONB"), phi),
            And(Call(F.Id("IsONB"), psi), And(Parenthesized(overlaps), distinct))));
        Formula hermitian = Equal(new Formula.Power(m, Star), m);
        Formula traceless = Equal(Call(F.Id("tr"), m), D(0));
        Formula real = All(i, Fin(n), All(j, Fin(n),
            Equal(Call(F.Id("Im"), Call(F.Id("weakValue"), Sub(phi, i), Sub(psi, j), m)), D(0))));
        Formula member = Rel(m, FormulaRelationOperator.MemberOf, Call(F.Id("realSpan"), phi, psi));
        Formula body = All(n, Nat(), All(phi, Basis(n), All(psi, Basis(n), Implies(Parenthesized(hypotheses),
            All(m, MatrixType(n), Implies(Parenthesized(And(hermitian, traceless)),
                Iff(Parenthesized(real), member)))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
