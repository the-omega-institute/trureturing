using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.NormCompression;

internal sealed class StrictSpectralPolyaRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/NormCompression/StrictSpectralPolyaRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Eigenstructure/zietak2017strictspectral");
    private static readonly Formula M = F.Id("M"), A = F.Id("A"), B = F.Id("B"), P = F.Id("p");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schatten-p approximants need not converge to the strict spectral approximant. A complex linear subspace of three-by-three matrices has a strict residual with singular values (1,1,0), whereas every minimizing residual for sufficiently large p has real last diagonal entry less than -1/4.",
        H("A counterexample to strict spectral convergence"),
        Blocks(
            Node("cp", "Schatten-p approximation", CpFormula(),
                "Page 308, verbatim: \"Thus for 1 < p < ∞ the cₚ-approximant B = Bₚ ∈ ℳ to A satisfying (1.1) is unique.\" Equation (1.1) minimizes the Schatten p-norm of A - X over X in the linear subspace. Here p is real, matrices have row and column carriers Fin m and Fin n, and schattenNorm is the finite singular-value norm in UpperBranchReduction. The limiting assertion below requires p > 1.",
                "IsCpApproximant", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("strict", "Lexicographic spectral approximation", StrictFormula(),
                StrictQuote,
                "IsStrictSpectralApproximant", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Ziętak's Conjecture 1.1", ClaimFormula(),
                ClaimQuote,
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The universal convergence claim is false", Seq(Neg, Sp, F.Id("claim")),
                "Set A = I₃, H = [[1,0,1],[0,-2,0],[1,0,0]], E = Matrix.diagonal (Pi.single 2 1), and M = Submodule.span ℂ {H,E}. The residuals are [[1+s,0,s],[0,1-2s,0],[s,0,t]]. The two leading diagonal constraints force s = 0 on the spectral-optimal face, whose lexicographic minimum is diag(1,1,0), so E is strict. Schatten-p minimizers exist for every p > 1. Their real last residual entry is eventually below -1/4, contradicting convergence to the strict residual. Hermitian projection reduces the complex minimization to a real comparison. No uniqueness or exact residual limit is needed.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zietak-2017-strict-spectral-polya-conjecture"),
                    ResolutionKind.Refuted)),
            Paragraph(Text("Grover–Gupta's Theorem 3.7 for min(m,n) ≤ 2 remains valid. The three-dimensional example uses a repeated leading singular-value cluster and a coupling that does not commute with E. Eventual superiority against each fixed competitor does not give a uniform comparison against moving minimizers.")),
            Paragraph(Text("Priyanka Grover and Krishna Kumar Gupta, Properties of best approximations with respect to the Ky Fan p-k norm, and the strict spectral approximant of a matrix, LAA 743 (2026), DOI 10.1016/j.laa.2026.04.016; arXiv:2603.07498v2."))),
        []));

    private const string StrictQuote = "Page 309, verbatim: \"A matrix B⁽ˢᵗ⁾ ∈ ℳ is a strict spectral approximant to a matrix A if the vector σ(R⁽ˢᵗ⁾) of the ordered singular values of the residual matrix R⁽ˢᵗ⁾ = A − B⁽ˢᵗ⁾ is minimal with respect to the lexicographic ordering in the set of vectors {σ ∈ ℝᵗ : σ = σ(A − X), X ∈ ℳ} (see [106]).\" Fin m and Fin n index the entries. LinearMap.singularValues supplies decreasing ordered singular values, padded by zeros; toLex uses the natural order of ℕ.";
    private const string ClaimQuote = "Page 309, Conjecture 1.1, verbatim: \"Let ℳ be a linear subspace of ℂᵐˣⁿ and let Bₚ ∈ ℳ be the cₚ-approximant to A ∈ ℂᵐˣⁿ. As p tends to ∞, the matrix Rₚ = A − Bₚ converges to A − B⁽ˢᵗ⁾, where B⁽ˢᵗ⁾ is the strict spectral approximant to A.\" The quantifiers range over all dimensions, complex linear subspaces, targets, strict approximants and functions B of the real exponent p. Minimization is required for every p > 1, and the residual converges in the matrix topology as p tends to infinity.";

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("zietak-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Q(string owner, string name)
    {
        var parts = owner.Split('.').Append(name).ToArray();
        Formula result = Seq(Operatorname, Grp(F.Id(parts[0])));
        foreach (var part in parts.Skip(1)) result = Seq(result, Dot, Operatorname, Grp(F.Id(part)));
        return result;
    }
    private static Formula QC(string owner, string name, params Formula[] args) => App(Q(owner, name), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula Lambda(string name, Formula type, Formula body) => Parenthesized(Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eqn(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Less(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) => Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Parenthesized(a), op, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Mat() => Call("Matrix", Call("Fin", F.Id("m")), Call("Fin", F.Id("n")), Complex());
    private static Formula OverMatrices(Formula body) => All("m", Nat(), All("n", Nat(),
        All("M", Call("Submodule", Complex(), Mat()), All("A", Mat(), All("B", Mat(), body)))));
    private static Formula Schatten(Formula residual) => QC("D5.S3.Quantum.NormCompression.UpperBranchReduction", "schattenNorm", P, residual);
    private static Formula Values(Formula residual) => Lambda("k", Nat(), QC("LinearMap", "singularValues", QC("Matrix", "toEuclideanLin", residual), F.Id("k")));
    private static Formula CpFormula() => All("p", Real(), OverMatrices(Eqn(Call("IsCpApproximant", P, M, A, B),
        And(Mem(B, M), All("X", Mat(), Imp(Mem(F.Id("X"), M), Le(Schatten(Sub(A, B)), Schatten(Sub(A, F.Id("X"))))))))));
    private static Formula StrictFormula() => OverMatrices(Eqn(Call("IsStrictSpectralApproximant", M, A, B),
        And(Mem(B, M), All("X", Mat(), Imp(Mem(F.Id("X"), M),
            Le(Call("toLex", Values(Sub(A, B))), Call("toLex", Values(Sub(A, F.Id("X"))))))))));
    private static Formula ClaimFormula()
    {
        Formula bst = F.Id("Bst");
        Formula body = QC("Filter", "Tendsto", Lambda("p", Real(), Sub(A, App(B, P))),
            Q("Filter", "atTop"), Call("nhds", Sub(A, bst)));
        body = Imp(All("p", Real(), Imp(Less(D(1), P), Call("IsCpApproximant", P, M, A, App(B, P)))), body);
        body = Imp(Call("IsStrictSpectralApproximant", M, A, bst), body);
        body = All("B", Arrow(Real(), Mat()), body);
        body = All("Bst", Mat(), body);
        body = All("A", Mat(), body);
        body = All("M", Call("Submodule", Complex(), Mat()), body);
        body = All("m", Nat(), All("n", Nat(), body));
        return Logic(F.Id("claim"), FormulaLogicOperator.Iff, body);
    }
}
