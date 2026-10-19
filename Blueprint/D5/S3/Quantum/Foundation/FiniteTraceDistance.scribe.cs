using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class FiniteTraceDistanceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/FiniteTraceDistance.";

    public DocumentDefinition Create()
    {
        Formula m = F.Id("m"), n = F.Id("n"), r = F.Id("R");
        Formula a = F.Id("A"), b = F.Id("B"), c = F.Id("C");
        Formula rho = F.Id("rho"), sigma = F.Id("sigma"), tau = F.Id("tau");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", m, n, r), square = Call("Matrix", n, n, r);
        Formula csquare = Call("Matrix", n, n, complex), state = Call("DensityState", n);
        Formula unitary = Call("unitaryGroup", n, complex);
        Formula reTraceUA = Call("re", Call("trace", Mul(Call("val", F.Id("U")), a)));
        Formula TN(Formula x) => Call("traceNorm", x);
        Formula D(Formula x, Formula y) => Call("traceDistance", x, y);
        Formula Apply(Formula x) => Call("mapState", c, x);
        Formula NormForAll(Formula body) => All(
            [Bound("m", F.Id("FiniteType")), Bound("n", F.Id("FiniteType")),
                Bound("R", F.Id("RCLike")), Bound("A", matrix)], body);
        Formula States(Formula body, bool three = false) => All(three
            ? [Bound("n", F.Id("FiniteType")), Bound("rho", state), Bound("sigma", state),
                Bound("tau", state)]
            : [Bound("n", F.Id("FiniteType")), Bound("rho", state), Bound("sigma", state)], body);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Trace norm, actual density-state distance, and contraction for every canonical quantum channel.",
            H("Finite Trace Distance"),
            Blocks(
                Paragraph(Text(
                    "DensityState and QuantumChannel are the canonical FiniteStateChannel carriers. "
                    + "raw denotes CStarMatrix.ofMatrix.symm, applied to the value of a state when "
                    + "its argument is a density state; toCstar denotes the forward equivalence. "
                    + "All coordinate types are finite with decidable equality, including empty types. "
                    + "RCLike is the existing Mathlib scalar interface. Adjoint means conjugate "
                    + "transpose and the square root uses the positive-semidefinite matrix order.")),
                Item("exists_svd_sqrt_eigenvalues", "Singular value decomposition", All(
                    [Bound("n", F.Id("Type"))], Seq(
                        Seq(OpenBracket, Call("Fintype", n), CloseBracket),
                        Seq(OpenBracket, Call("DecidableEq", n), CloseBracket),
                        All([Bound("A", csquare)], Seq(
                            F.Text, Grp(F.Id("let"), Sp), Sp, F.Id("hH"), Colon, QCall("Matrix", "IsHermitian", Mul(QCall("Matrix", "conjTranspose", a), a)),
                            Comma, new Formula.BindMany(FormulaQuantifier.Exists,
                                [Bound("V", QCall("Matrix", "unitaryGroup", n, complex)),
                                    Bound("W", QCall("Matrix", "unitaryGroup", n, complex))],
                                Eqn(a, Mul(Mul(Call("val", F.Id("V")),
                                    QCall("Matrix", "diagonal", Seq(LambdaLower, Parenthesized(Seq(F.Id("i"), Colon, n)), Mapsto,
                                        QCall("Complex", "ofReal", QCall("Real", "sqrt",
                                            QCall("Matrix.IsHermitian", "eigenvalues", F.Id("hH"), F.Id("i"))))))),
                                    QCall("Matrix", "conjTranspose", Call("val", F.Id("W"))))))))))),
                Describe.Lean(
                    DescribeId.Create("re-trace-eq-trace"),
                    DeclarationHandle.Create(Owner + "re_trace_eq_trace"),
                    H("The trace of a Hermitian matrix is real"),
                    StatementSource.FromAuthor(Disp(All(
                        [Bound("n", F.Id("Type")), Bound("R", F.Id("Type"))], Seq(
                            Seq(OpenBracket, Call("Fintype", n), CloseBracket),
                            Seq(OpenBracket, Call("RCLike", r), CloseBracket),
                            All([Bound("A", square)], Implies(QCall("Matrix", "IsHermitian", a),
                                Eqn(Parenthesized(Seq(QCall("RCLike", "re", QCall("Matrix", "trace", a)),
                                        Colon, r)),
                                    QCall("Matrix", "trace", a)))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For every Hermitian square matrix over an RCLike scalar type, "
                            + "coercing the real part of its trace back to that scalar "
                            + "type gives the original trace. Only the index type is "
                            + "assumed finite; no decidable equality is required."))),
                    DescribeRole.Theorem),
                Item("traceNorm", "Actual trace norm", NormForAll(Eqn(TN(a),
                    Call("re", Call("trace", Call("sqrt", Mul(Adjoint(a), a)))))), true),
                Item("traceNorm_neg", "Negation invariance", NormForAll(Eqn(
                    TN(Sub(Num(0), a)), TN(a)))),
                Item("traceNorm_nonneg", "Nonnegative trace norm", NormForAll(Le(Num(0), TN(a)))),
                Item("traceNorm_eq_max_re_tr_U", "Unitary maximum formula", All(
                    [Bound("n", F.Id("FiniteType")), Bound("A", csquare)],
                    new Formula.Logic(
                        new Formula.BindMany(FormulaQuantifier.Exists, [Bound("U", unitary)],
                            Eqn(reTraceUA, TN(a))),
                        FormulaLogicOperator.And,
                        All([Bound("U", unitary)], Le(reTraceUA, TN(a)))))),
                Item("traceNorm_add_le", "Trace norm triangle inequality", All(
                    [Bound("n", F.Id("FiniteType")), Bound("A", csquare), Bound("B", csquare)],
                    Le(TN(Add(a, b)), Add(TN(a), TN(b))))),
                Item("traceNorm_of_posSemidef", "Positive trace norm", All(
                    [Bound("n", F.Id("FiniteType")), Bound("R", F.Id("RCLike")), Bound("A", square)],
                    Implies(Call("PosSemidef", a), Eqn(Call("embed", r, TN(a)), Call("trace", a))))),
                Item("act", "Canonical channel on matrix coordinates", All(
                    [Bound("n", F.Id("FiniteType")), Bound("C", Call("QuantumChannel", n, n)),
                        Bound("A", csquare)],
                    Eqn(Call("act", c, a), Call("raw", Call("applyCP", c, Call("toCstar", a))))), true),
                Item("traceDistance", "Actual density distance", States(Eqn(D(rho, sigma),
                    Div(TN(Sub(Call("raw", rho), Call("raw", sigma))), Num(2)))), true),
                Item("traceDistance_nonneg", "Nonnegative density distance", States(Le(Num(0), D(rho, sigma)))),
                Item("traceDistance_symm", "Symmetry", States(Eqn(D(rho, sigma), D(sigma, rho)))),
                Item("traceDistance_triangle", "Density distance triangle inequality", States(
                    Le(D(rho, tau), Add(D(rho, sigma), D(sigma, tau))), true)),
                Item("traceDistance_le_one", "All density distances are at most one", States(Le(D(rho, sigma), Num(1)))),
                Item("traceNorm_sub_orthogonal", "Orthogonal positive difference", All(
                    [Bound("n", F.Id("Type"))], Seq(
                        OpenBracket, Call("Fintype", n), CloseBracket, Sp,
                        OpenBracket, Call("DecidableEq", n), CloseBracket, Sp,
                        All([Bound("A", csquare), Bound("B", csquare)],
                            Implies(Call("PosSemidef", a), Implies(Call("PosSemidef", b),
                                Implies(Eqn(Mul(a, b), Num(0)),
                                    Eqn(TN(Sub(a, b)), Add(Call("re", Call("trace", a)),
                                        Call("re", Call("trace", b))))))))))),
                Item("trace_norm_jordan_mass", "Hermitian Jordan mass", All(
                    [Bound("n", F.Id("FiniteType")), Bound("A", csquare)],
                    Implies(QCall("Matrix", "IsHermitian", a), Eqn(TN(a),
                        Add(Call("re", Call("trace", Call("posPart", a))),
                            Call("re", Call("trace", Call("negPart", a)))))))),
                Item("traceDistance_contract", "Every CPTP channel contracts trace distance", All(
                    [Bound("n", F.Id("FiniteType")), Bound("C", Call("QuantumChannel", n, n)),
                        Bound("rho", state), Bound("sigma", state)],
                    Le(D(Apply(rho), Apply(sigma)), D(rho, sigma)))),
                Paragraph(Text(
                    "The trace-norm proofs and their necessary SVD, orthonormal extension, and "
                    + "unitary row-sum dependencies retain Alex Meiburg's Physlib source at revision "
                    + "6a09b2d1761a0d4430083045a247eb121d8da260. The Lean owner retains its copyright "
                    + "and full Apache 2.0 license. Retention ends when equivalent declarations are "
                    + "available in this repository's own pinned Mathlib.")),
                Paragraph(Text(
                    "Contraction follows from the actual Hermitian Jordan positive and negative "
                    + "parts, their trace-norm mass identity, complete positivity, and trace "
                    + "preservation. It assumes neither a contractivity field nor a Kraus "
                    + "representation of the recovery. The finite-record recovery-error theorem "
                    + "consumes these laws; no computational recovery algorithm is asserted.")),
                Paragraph(Text(
                    "For the signed-time prediction application in original Theorem 3.3, let d,e be "
                    + "at least two, H any Hermitian matrix on the joint space, and rho any positive "
                    + "semidefinite trace-one joint state. The partial trace is unnormalized and "
                    + "the trace norm here is unhalved. Set h0=Re Tr(H)/(de), HA=Tr_B(H)/e-h0 I, "
                    + "HB=Tr_A(H)/d, H0=HA tensor I+I tensor HB, and V=H-H0. The same-H residual "
                    + "is R_ab=(id-E_A)[H,W_ab tensor I], where E_A(X)=Tr_B(X) tensor I/e; "
                    + "delta(H) is the maximum of the Euclidean operator norms of these residuals.")),
                Paragraph(Text(
                    "A positive matrix R satisfies Re Tr(A R A*) <= ||A||^2 Re Tr(R). Indeed, "
                    + "with S=sqrt(R), the C-star conjugation bound gives S A* A S <= ||A||^2 R. "
                    + "Apply the positive trace map and trace cyclicity. For unitary U,W put "
                    + "D=U-W, M=(U+W)/2, and r=||D||. If r=0 the endpoints agree. Otherwise the "
                    + "positive matrices P_plus=(D+r M)R(D+r M)*/(2r) and "
                    + "P_minus=(D-r M)R(D-r M)*/(2r) have difference U R U*-W R W* and sum "
                    + "D R D*/r+r M R M*. Since ||M||<=1, their total trace is at most 2r Tr(R). "
                    + "Partial trace preserves positivity and the unnormalized trace. The positive "
                    + "trace-norm formula and triangle inequality therefore bound the reduced "
                    + "endpoint difference by 2||U-W|| Tr(R), including singular and correlated R.")),
                Paragraph(Text(
                    "Fix any real t and define Z(s)=exp(i t s H0) exp(-i t s H) for 0<=s<=1. "
                    + "The two exponential derivative formulas give "
                    + "Z'(s)=-i t exp(i t s H0) V exp(-i t s H). Both factors are actual "
                    + "unitaries, so ||Z'(s)||<=|t| ||V||. The vector-valued mean-value bound on "
                    + "[0,1], followed by multiplication by exp(-i t H0), yields "
                    + "||exp(-i t H)-exp(-i t H0)||<=|t| ||V||. The argument includes t<0 and "
                    + "t=0 and uses no commutation assumption on H and H0.")),
                Paragraph(Text(
                    "The two Kronecker algebra embeddings preserve the exponential and their "
                    + "images commute, hence exp(-i t H0)=exp(-i t HA) tensor exp(-i t HB). "
                    + "The existing local partial-trace covariance identity applies to every joint "
                    + "matrix, giving Tr_B(exp(-i t H0)rho exp(-i t H0)*)="
                    + "exp(-i t HA)Tr_B(rho)exp(-i t HA)*. The endpoint estimate and the same-H "
                    + "Weyl reconstruction inequality ||V||<=delta(H) give the bound "
                    + "2|t|delta(H). Both reduced endpoints are positive trace-one matrices, so "
                    + "their unhalved trace-norm difference is also at most two. Thus the actual "
                    + "reduced-state prediction error is <=min(2,2|t|delta(H)) for every real t "
                    + "and arbitrary joint rho, including noncommuting, singular and correlated states.")))));
    }

    private static DocumentBlock Item(string name, string title, Formula formula, bool definition = false) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), Provenance(name),
            Blocks(Paragraph(Text(Explanation(name)))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);
    private static AssessedProvenance Provenance(string name) => name switch
    {
        "exists_svd_sqrt_eigenvalues" => AssessedProvenance.FromLiterature(
            LibraryNoteRef.Create("D5/L/QuantumStates/meiburg2025svd")),
        "traceNorm" or "traceNorm_neg" or "traceNorm_nonneg" or "traceNorm_eq_max_re_tr_U" or "traceNorm_add_le"
            or "traceNorm_of_posSemidef" => AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Quantum/wilde2017quantum")),
        _ => AssessedProvenance.FromRepo()
    };
    private static string Explanation(string name) => name switch
    {
        "traceNorm_sub_orthogonal" => "For positive semidefinite complex matrices A and B with A B zero, A plus B is the positive square root of the Gram matrix of A minus B. The trace norm is therefore the sum of their real traces.",
        "exists_svd_sqrt_eigenvalues" => "For every finite complex square matrix, two unitary factors give a diagonal singular-value decomposition. The diagonal entries are the real square roots of the eigenvalues of its Gram matrix. The let-bound hH is the canonical Hermitian proof for that Gram matrix; ofReal denotes the real-to-complex embedding. The retained proof is Alex Meiburg's Physlib SVD.",
        "traceNorm" => "This is the real part of the trace of the positive square root of the Gram matrix.",
        "traceNorm_neg" => "Negation leaves the Gram matrix unchanged.",
        "traceNorm_nonneg" => "The positive square root is positive semidefinite and has nonnegative real trace.",
        "traceNorm_eq_max_re_tr_U" => "A unitary attains the trace norm as the real trace of its product with A, and every unitary gives a value at most the trace norm. Here val denotes the underlying matrix. The formula holds in every finite complex square dimension, including the empty type.",
        "traceNorm_add_le" => "The retained SVD proof identifies the norm as the maximum real trace over unitaries; trace additivity gives the bound.",
        "traceNorm_of_posSemidef" => "For a positive semidefinite matrix, the Gram matrix is its square and its positive square root is the original matrix.",
        "act" => "The matrix coordinate equivalence transports the actual completely positive map.",
        "traceDistance" => "The canonical density-state values are converted to matrices before taking half the trace norm of their difference.",
        "traceDistance_nonneg" => "Trace-norm nonnegativity gives the lower endpoint of the density-distance interval.",
        "traceDistance_symm" => "Reversing the state difference negates the matrix and preserves its trace norm.",
        "traceDistance_triangle" => "Split the state difference through the intermediate state and apply the trace-norm triangle inequality.",
        "traceDistance_le_one" => "Each density matrix has trace norm one; the triangle inequality bounds their difference by two.",
        "trace_norm_jordan_mass" => "For a Hermitian matrix A, its trace norm equals the sum of the real traces of its positive and negative Jordan parts.",
        "traceDistance_contract" => "Split the Hermitian state difference into positive and negative parts. Positivity and trace preservation preserve their trace-norm masses, whose sum is the original trace norm.",
        _ => throw new System.ArgumentOutOfRangeException(nameof(name))
    };
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        Seq(Operatorname, Grp(Seq((owner + "." + name).Split('.').SelectMany((part, index) =>
                index == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) }).ToArray())),
            Parenthesized(Seq(args.SelectMany((arg, index) =>
                index == 0 ? new[] { arg } : new[] { Comma, Sp, arg }).ToArray())));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Adjoint(Formula a) => Seq(a, Caret, Grp(Star));
}
