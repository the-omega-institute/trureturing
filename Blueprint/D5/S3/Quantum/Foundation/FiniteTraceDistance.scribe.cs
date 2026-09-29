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
                    + "consumes these laws; no computational recovery algorithm is asserted.")))));
    }

    private static DocumentBlock Item(string name, string title, Formula formula, bool definition = false) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), Provenance(name),
            Blocks(Paragraph(Text(Explanation(name)))),
            definition ? DescribeRole.Definition : DescribeRole.Theorem);
    private static AssessedProvenance Provenance(string name) => name switch
    {
        "traceNorm" or "traceNorm_neg" or "traceNorm_nonneg" or "traceNorm_eq_max_re_tr_U" or "traceNorm_add_le"
            or "traceNorm_of_posSemidef" => AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Quantum/wilde2017quantum")),
        _ => AssessedProvenance.FromRepo()
    };
    private static string Explanation(string name) => name switch
    {
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
        "traceDistance_contract" => "Split the Hermitian state difference into positive and negative parts. Positivity and trace preservation preserve their trace-norm masses, whose sum is the original trace norm.",
        _ => throw new System.ArgumentOutOfRangeException(nameof(name))
    };
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
