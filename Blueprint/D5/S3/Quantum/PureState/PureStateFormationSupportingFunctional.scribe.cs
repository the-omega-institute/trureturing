using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class PureStateFormationSupportingFunctionalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/PureState/PureStateFormationSupportingFunctional.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/holevo2026logsobolevformation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In every finite-dimensional bipartite system, each pure state admits a Hermitian supporting functional for the entanglement of formation.",
        H("A supporting functional at every pure bipartite state"),
        Blocks(
            Paragraph(Text(
                "Let Alice and Bob have positive dimensions a and b. Fin(a) and Fin(b) label "
                    + "their bases by 0 through a - 1 and 0 through b - 1: a source index "
                    + "(i,j) in the ranges 1 through a and 1 through b corresponds to "
                    + "(i - 1,j - 1) here. Vectors are functions on Fin(a) times Fin(b), "
                    + "and matrices have rows and columns in that same product. Both even "
                    + "and odd positive dimensions are included, independently on each factor.")),
            Describe.Lean(
                DescribeId.Create("pure-state-formation-supporting-functional-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The supporting-functional assertion"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Holevo and Shirokov ask in the Introduction and Section 3.1 whether "
                            + "the entanglement of formation has a supporting affine functional "
                            + "at every pure state of a finite-dimensional composite system. "
                            + "The assertion below uses a Hermitian matrix W to represent that "
                            + "functional by the real part of Tr(W sigma). On the trace-one "
                            + "state space this representation also includes an affine constant, "
                            + "by adding a scalar multiple of the identity to W.")),
                    Paragraph(Text(
                        "The normalization is the squared vector norm, equivalently "
                            + "star(psi) dot psi = 1. rankOneDensity(psi) has entry "
                            + "psi(i,j) times the complex conjugate of psi(k,l). "
                            + "pureDensityState(psi) is the density state with that matrix; "
                            + "its unit-norm proof argument is supplied by the displayed "
                            + "normalization and suppressed in the formula. marginalRight "
                            + "traces out Bob and retains Alice. DensityState consists of "
                            + "positive semidefinite matrices of trace one, and "
                            + "CStarMatrix.ofMatrix.symm(val(sigma)) is the underlying matrix.")),
                    Paragraph(Text(
                        "The symbol E with subscript F denotes E_F, the infimum of the "
                            + "average marginal entropy over all finite pure ensembles with "
                            + "the prescribed average state. vonNeumannEntropy uses natural "
                            + "logarithms and assigns zero to a zero eigenvalue. E_F takes "
                            + "values in the extended nonnegative reals; ofReal(x) is max(x,0) "
                            + "in that space. The real equality with the marginal entropy is "
                            + "stated separately from the equality after ofReal, so the value "
                            + "at the pure state retains its sign information."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pure-state-formation-supporting-functional-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The assertion holds in all finite dimensions"),
                StatementSource.FromAuthor(Disp(Named("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The construction answers the question of Holevo and Shirokov. "
                            + "Put P = |psi><psi| and R = Tr_B(P), and write log-zero(R) "
                            + "for spectral application of the real logarithm, set to zero "
                            + "at a zero eigenvalue. If r(i) are the eigenvalues of R, take "
                            + "c to be the sum of their reciprocals, with reciprocal zero "
                            + "at zero. Thus c is nonnegative and c r(i) is at least one "
                            + "whenever r(i) is positive.")),
                    Paragraph(Text(
                        "For r >= 0, 0 <= t <= 1 and c >= 0 with c r >= 1 when r > 0, "
                            + "the scalar logarithmic inequality gives "
                            + "-t log-zero(r) - (t - r) - c(t - r)^2 <= -t log(t), "
                            + "where the right side is zero at t = 0. For positive r and t "
                            + "this follows from log(t/r) <= t/r - 1 and 1/r <= c. "
                            + "The cases r = 0 and t = 0 follow separately from "
                            + "nonnegativity and c r >= 1, respectively.")),
                    Paragraph(Text(
                        "For any density matrix T on Alice's space, average this scalar "
                            + "inequality over the two eigenbases with weights "
                            + "w(i,j) = |<e(i),u(j)>|^2. The overlap matrix is doubly "
                            + "stochastic: every row and column sums to one. The linear "
                            + "term cancels because both spectra sum to one, the logarithmic "
                            + "term becomes -Re Tr(log-zero(R) T), and the weighted squared "
                            + "differences become the squared Hilbert-Schmidt distance. "
                            + "Consequently S(T) >= -Re Tr(log-zero(R) T) - c ||T - R||_HS^2.")),
                    Paragraph(Text(
                        "Cauchy-Schwarz in Bob's index gives "
                            + "||Tr_B(X)||_HS^2 <= b ||X||_HS^2 for every joint matrix X. "
                            + "For a pure density Q, ||Q - P||_HS^2 = 2(1 - Re Tr(PQ)). "
                            + "Set K = 2bc and W = -log-zero(R) tensor I_B - K(I_AB - P). "
                            + "This W is Hermitian. The partial-trace bound and the entropy "
                            + "estimate give Re Tr(WQ) <= S(Tr_B(Q)), with equality "
                            + "Re Tr(WP) = S(R) at Q = P.")),
                    Paragraph(Text(
                        "For every finite pure ensemble with average sigma, linearity "
                            + "of the trace and the pure-state inequality bound Re Tr(W sigma) "
                            + "by its average marginal entropy. Applying ofReal and taking "
                            + "the infimum over all these ensembles proves the bound by "
                            + "E_F(sigma). At P, the one-element ensemble gives the reverse "
                            + "inequality, hence E_F(P) = ofReal(Re Tr(WP)). Together with "
                            + "the real equality at P, these are precisely the clauses of claim."))),
                DescribeRole.Theorem)
        )));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Typed(Formula variable, Formula type) =>
        Parenthesized(Seq(variable, Colon, Sp, type));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula JointIndex() =>
        Parenthesized(Seq(Call("Fin", F.Id("a")), Sp, F.Times, Sp, Call("Fin", F.Id("b"))));
    private static Formula Vectors() => Parenthesized(new Formula.TypeArrow(JointIndex(), Complexes()));
    private static Formula Matrices() => Call("Matrix", JointIndex(), JointIndex(), Complexes());
    private static Formula States() => Call("DensityState", JointIndex());
    private static Formula Formation(Formula state) => At(new Formula.Subscript(F.Id("E"), F.Id("F")), state);
    private static Formula RealTrace(Formula matrix) => Call("Re", Call("Tr", matrix));
    private static Formula StateMatrix(Formula state) => At(
        Seq(Operatorname, Grp(F.Id("CStarMatrix"), Dot, F.Id("ofMatrix"), Dot, F.Id("symm"))),
        Call("val", state));

    private static Formula ClaimFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), x = F.Id("x"), w = F.Id("W");
        Formula psi = new Formula.Psi(), sigma = SigmaLower;
        Formula norm = Seq(new Formula.Subscript(Sum, Typed(x, JointIndex())), Sp,
            Parenthesized(new Formula.Power(new Formula.Absolute(At(psi, x)), D(2))));
        Formula pure = Call("pureDensityState", psi);
        Formula value = RealTrace(Mul(w, Call("rankOneDensity", psi)));
        Formula entropy = Call("vonNeumannEntropy", Call("marginalRight", pure));
        Formula lowerBound = All(sigma, States(),
            LE(Call("ofReal", RealTrace(Mul(w, StateMatrix(sigma)))), Formation(sigma)));
        Formula conclusion = Some(w, Matrices(),
            And(Call("IsHermitian", w),
                And(Equal(value, entropy),
                    And(Equal(Formation(pure), Call("ofReal", value)), lowerBound))));
        Formula assertion = All(a, Naturals(), All(b, Naturals(),
            Imp(LE(D(1), a), Imp(LE(D(1), b),
                All(psi, Vectors(), Imp(Equal(norm, D(1)), conclusion))))));
        return new Formula.Logic(Named("claim"), FormulaLogicOperator.Iff, Parenthesized(assertion));
    }
}
