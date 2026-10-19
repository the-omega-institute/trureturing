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
                            + "the prescribed average state. In the entropy definition, "
                            + "CFC.log applies the natural real logarithm by functional "
                            + "calculus. Its spectral expression uses the eigenvalues of "
                            + "the Hermitian underlying density matrix, indexed by n; "
                            + "every zero eigenvalue contributes zero.")),
                    Display(EntropyFormula()),
                    Display(EntropySpectrumFormula()),
                    Display(LogConventionFormula()),
                    Paragraph(Text(
                        "The marginal traces out Bob. The coefficient matrix M represents "
                            + "a joint vector, mass is its squared norm, and Pure(a,b) "
                            + "consists of the coefficient matrices of mass one.")),
                    Display(MarginalFormula()),
                    Display(CoeffFormula()),
                    Display(MassFormula()),
                    Display(PureFormula()),
                    Paragraph(Text(
                        "An Ensemble(n,sigma) consists of probabilities p and normalized "
                            + "pure coefficient matrices q with the displayed average. "
                            + "Complex(p(i)) is the real-to-complex coercion; multiplying "
                            + "a matrix by this scalar denotes scalar multiplication. "
                            + "The lambda expression uncurries a coefficient matrix. "
                            + "For an ensemble e, p(e) and psi(e) are its probability "
                            + "and pure-vector projections. The normalization in Pure "
                            + "supplies the suppressed proof argument of pureDensityState.")),
                    Display(EnsembleFormula()),
                    Display(CostFormula()),
                    Paragraph(Text(
                        "E_F takes values in ENNReal, the extended nonnegative reals. "
                            + "Both infima are taken in ENNReal, and ENNReal.ofReal is "
                            + "applied to the whole real ensemble cost inside the infima. "
                            + "ENNReal.ofReal(x) is max(x,0) in that space. In the claim, "
                            + "it is applied to the whole real trace value in both the "
                            + "pure-state equality and the comparison for every sigma. "
                            + "The real equality with the marginal entropy is "
                            + "stated separately from the equality after ofReal, so the value "
                            + "at the pure state retains its sign information.")),
                    Display(FormationFormula())),
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
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("holevo-shirokov-2026-pure-state-formation-supporting-functional"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Display(Formula value) => new DocumentBlock.DisplayFormula(Disp(value));
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
    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(variable, type)), Sp, Parenthesized(body));
    private static Formula InfOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Named("inf"), Typed(variable, type)), Sp, Parenthesized(body));
    private static Formula Pair(Formula left, Formula right) =>
        Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Product(Formula left, Formula right) =>
        Parenthesized(Seq(left, Sp, F.Times, Sp, right));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        Parenthesized(new Formula.TypeArrow(domain, codomain));
    private static Formula LambdaOver(Formula variable, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body)));
    private static Formula SubsetOf(Formula variable, Formula type, Formula condition) =>
        Seq(OpenBrace, Typed(variable, type), Sp, Mid, Sp, Parenthesized(condition), CloseBrace);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula OfReal(Formula value) => At(Qualified("ENNReal", "ofReal"), value);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Dims(Formula body) =>
        All(F.Id("a"), Naturals(), All(F.Id("b"), Naturals(), body));
    private static Formula CoeffType() =>
        Call("Coeff", F.Id("a"), F.Id("b"));
    private static Formula PureType() =>
        Call("Pure", F.Id("a"), F.Id("b"));
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

    private static Formula AllDensityStates(Formula body)
    {
        Formula n = F.Id("n");
        return All(n, F.Id("Type"), Seq(
            OpenBracket, Call("Fintype", n), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", n), CloseBracket, Comma, Sp,
            Parenthesized(All(Rho, Call("DensityState", n), body))));
    }

    private static Formula EntropyFormula() => AllDensityStates(
        Equal(Call("vonNeumannEntropy", Rho),
            Seq(Minus, Parenthesized(RealTrace(Mul(Call("val", Rho),
                At(Qualified("CFC", "log"), Call("val", Rho))))))));

    private static Formula EntropySpectrumFormula()
    {
        Formula i = F.Id("i");
        Formula eigenvalue = At(Call("eigenvalues", StateMatrix(Rho)), i);
        return AllDensityStates(Equal(Call("vonNeumannEntropy", Rho),
            SumOver(i, F.Id("n"), At(Qualified("Real", "negMulLog"), eigenvalue))));
    }

    private static Formula LogConventionFormula()
    {
        Formula t = F.Id("t");
        Formula log(Formula value) => At(Qualified("Real", "log"), value);
        return And(All(t, Reals(), Equal(At(Qualified("Real", "negMulLog"), t),
                Mul(Parenthesized(Seq(Minus, t)), log(t)))),
            And(Equal(log(D(0)), D(0)), Equal(Mul(D(0), log(D(0))), D(0))));
    }

    private static Formula MarginalFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j"), k = F.Id("k");
        return Dims(All(SigmaLower, States(),
            All(i, Call("Fin", F.Id("a")), All(j, Call("Fin", F.Id("a")),
                Equal(At(StateMatrix(Call("marginalRight", SigmaLower)), i, j),
                    SumOver(k, Call("Fin", F.Id("b")),
                        At(StateMatrix(SigmaLower), Pair(i, k), Pair(j, k))))))));
    }

    private static Formula CoeffFormula() => Dims(Equal(CoeffType(),
        Call("Matrix", Call("Fin", F.Id("a")), Call("Fin", F.Id("b")), Complexes())));

    private static Formula MassFormula()
    {
        Formula m = F.Id("M"), i = F.Id("i"), j = F.Id("j");
        return Dims(All(m, CoeffType(), Equal(Call("mass", m),
            SumOver(i, Call("Fin", F.Id("a")), SumOver(j, Call("Fin", F.Id("b")),
                Call("normSq", At(m, i, j)))))));
    }

    private static Formula PureFormula()
    {
        Formula m = F.Id("M");
        return Dims(Equal(PureType(), SubsetOf(m, CoeffType(), Equal(Call("mass", m), D(1)))));
    }

    private static Formula CoefficientVector(Formula coefficients)
    {
        Formula x = F.Id("x");
        return LambdaOver(x, JointIndex(), At(coefficients, Call("fst", x), Call("snd", x)));
    }

    private static Formula EnsembleFormula()
    {
        Formula n = F.Id("n"), p = F.Id("p"), q = F.Id("q"), i = F.Id("i");
        Formula pairType = Product(Arrow(Call("Fin", n), Reals()), Arrow(Call("Fin", n), PureType()));
        Formula conditions = And(All(i, Call("Fin", n), LE(D(0), At(p, i))),
            And(Equal(SumOver(i, Call("Fin", n), At(p, i)), D(1)),
                Equal(SumOver(i, Call("Fin", n), Mul(Call("Complex", At(p, i)),
                    Call("rankOneDensity", CoefficientVector(Call("val", At(q, i)))))),
                    StateMatrix(SigmaLower))));
        return Dims(All(n, Naturals(), All(SigmaLower, States(),
            Equal(Call("Ensemble", n, SigmaLower), SubsetOf(Pair(p, q), pairType, conditions)))));
    }

    private static Formula CostFormula()
    {
        Formula n = F.Id("n"), e = F.Id("e"), i = F.Id("i");
        Formula vector = CoefficientVector(Call("val", At(At(new Formula.Psi(), e), i)));
        Formula entropy = Call("vonNeumannEntropy", Call("marginalRight", Call("pureDensityState", vector)));
        return Dims(All(n, Naturals(), All(SigmaLower, States(), All(e, Call("Ensemble", n, SigmaLower),
            Equal(Call("cost", e), SumOver(i, Call("Fin", n), Mul(At(Call("p", e), i), entropy)))))));
    }

    private static Formula FormationFormula()
    {
        Formula n = F.Id("n"), e = F.Id("e");
        return Dims(All(SigmaLower, States(), Equal(Formation(SigmaLower),
            InfOver(n, Naturals(), InfOver(e, Call("Ensemble", n, SigmaLower), OfReal(Call("cost", e)))))));
    }

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
            LE(OfReal(RealTrace(Mul(w, StateMatrix(sigma)))), Formation(sigma)));
        Formula conclusion = Some(w, Matrices(),
            And(Call("IsHermitian", w),
                And(Equal(value, entropy),
                    And(Equal(Formation(pure), OfReal(value)), lowerBound))));
        Formula assertion = All(a, Naturals(), All(b, Naturals(),
            Imp(LE(D(1), a), Imp(LE(D(1), b),
                All(psi, Vectors(), Imp(Equal(norm, D(1)), conclusion))))));
        return new Formula.Logic(Named("claim"), FormulaLogicOperator.Iff, Parenthesized(assertion));
    }
}
