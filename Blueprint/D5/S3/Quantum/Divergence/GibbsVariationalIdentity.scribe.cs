using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class GibbsVariationalIdentityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Divergence/GibbsVariationalIdentity.";

    public DocumentDefinition Create()
    {
        Formula n = F.Id("n"), h = F.Id("H"), rho = F.Id("rho");
        Formula z = Call("partitionFunction", h), g = Call("gibbsState", h);
        Formula General(Formula body) => All(
            [Bound("n", F.Id("FiniteNonemptyType")),
                Bound("H", Call("HermitianMatrix", n)),
                Bound("rho", Call("DensityState", n))], body);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The normalized matrix exponential gives an exact entropy decomposition.",
            H("Gibbs Variational Identity"),
            Blocks(
                Paragraph(Text(
                    "Matrices are complex and indexed by an arbitrary finite nonempty type n. "
                    + "H is Hermitian. DensityState means a positive semidefinite matrix with "
                    + "complex trace one. ReTr is the real part of the matrix trace. "
                    + "partitionFunction(H) is ReTr(exp(H)) and is strictly positive; "
                    + "gibbsState(H) is its inverse scalar times exp(H), a positive definite "
                    + "density matrix. Every logarithm is natural and the matrix logarithm "
                    + "is Mathlib's spectral continuous functional calculus.")),
                Paragraph(Text(
                    "For any Hermitian Hamiltonians A and B and inverse temperature beta > 0, "
                    + "put V = A - B and c equal to the Euclidean induced operator norm of V. "
                    + "Here exp is the full complex matrix exponential. Write Z(A) = ReTr(exp(-beta A)), "
                    + "f(A) = -beta^(-1) log Z(A), and "
                    + "gamma(A) = Z(A)^(-1) exp(-beta A), and likewise for B. For every canonical "
                    + "positive semidefinite density rho "
                    + "with trace one, the three comparisons are |ReTr(rho V)| <= c, "
                    + "|f(A)-f(B)| <= c, and "
                    + "|beta^(-1) D(rho || gamma(A))-beta^(-1) D(rho || gamma(B))| <= 2c. "
                    + "These are applications of existing results, with no commutation or invertibility "
                    + "assumption on rho: it can be singular and can fail to commute with either Hamiltonian.")),
                Paragraph(Text(
                    "The signed Hermitian order envelope -c I <= V <= c I and positive trace "
                    + "pairing with rho give the expectation estimate. The existing "
                    + "abs_eigenvalue_sub_eigenvalue_le theorem, applied to the same Euclidean operators, "
                    + "bounds the paired eigenvalues by c. The re_trace_cfc spectral trace formula and the "
                    + "continuous-functional-calculus exponential then give "
                    + "exp(-beta c) Z(B) <= Z(A) <= exp(beta c) Z(B). "
                    + "Positive partition functions and logarithm monotonicity yield the free-energy "
                    + "estimate. Subtracting gibbs_variational_identity at the same rho gives exactly "
                    + "beta^(-1)(D(rho || gamma(A))-D(rho || gamma(B))) = "
                    + "ReTr(rho V) - (f(A)-f(B)); the triangle inequality gives 2c. "
                    + "The CFC exponential agrees with the full matrix exponential, so Z(A) and Z(B) "
                    + "are strictly positive and the normalized matrices are exactly the canonical "
                    + "Gibbs densities obtained through fromLegacyDensityState. Each is positive definite. "
                    + "Thus SupportContained rho gamma holds for both references, and the extended "
                    + "relative entropy equals the finiteTraceLogRelativeEntropy branch used for D. This justifies "
                    + "the finite trace-log entropy even for singular rho. "
                    + "The trace-exponential comparison is also discussed by Alhambra, "
                    + "PRX Quantum 4, 040201 (2023), Section III.D, equations (53)-(54), "
                    + "doi:10.1103/PRXQuantum.4.040201.")),
                Paragraph(Text(
                    "For a Hermitian H on Fin d x Fin e with d,e >= 2, define "
                    + "h0 = ReTr(H)/(de), HA = e^(-1) TrB(H) - h0 I_d, "
                    + "and HB = d^(-1) TrA(H), where TrB is partialTraceRight and TrA is "
                    + "partialTraceLeft of this same H. Only HA is centered. Partial traces preserve Hermiticity, so "
                    + "H0 = HA tensor I_e + I_d tensor HB and V = H - H0 are Hermitian. "
                    + "The comparisons apply with A = H, B = H0 and the same arbitrary joint "
                    + "density rho and every beta > 0, with c the Euclidean operator norm of H - H0. "
                    + "These finite-matrix estimates require no physical realization assumptions. "
                    + "A physical interpretation must supply its own Hamiltonian and state hypotheses. "
                    + "Replacing c by a Weyl residual delta(H) additionally requires "
                    + "the bound c <= delta(H). Tensor factorization of the "
                    + "Gibbs state, dynamical prediction, and recovery estimates require their "
                    + "own identities.")),
                Describe.Lean(
                    DescribeId.Create("spectral-logarithm-of-gibbs-state"),
                    DeclarationHandle.Create(Owner + "log_gibbs_state"),
                    H("Logarithm of the Gibbs state"),
                    StatementSource.FromAuthor(Disp(All(
                        [Bound("n", F.Id("FiniteNonemptyType")),
                            Bound("H", Call("HermitianMatrix", n))],
                        Eqn(Call("log", g), Sub(h, Mul(Call("log", z), F.Id("I"))))))),
                    AssessedProvenance.FromLiterature(
                        LibraryNoteRef.Create("D5/L/Quantum/watrous2018entropicidentities")),
                    Blocks(Paragraph(Text(
                        "The logarithm of a positive scalar multiple separates into a scalar "
                        + "logarithm and the matrix logarithm. The logarithm of the exponential "
                        + "of a Hermitian matrix is the original matrix."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("gibbs-variational-identity"),
                    DeclarationHandle.Create(Owner + "gibbs_variational_identity"),
                    H("Gibbs entropy decomposition"),
                    StatementSource.FromAuthor(Disp(General(Eqn(Call("log", z),
                        Add(Add(Call("ReTr", Mul(h, rho)), Call("vonNeumannEntropy", rho)),
                            Call("quantumRelativeEntropy", rho, g)))))),
                    AssessedProvenance.FromLiterature(
                        LibraryNoteRef.Create("D5/L/Quantum/goold2016thermodynamics")),
                    Blocks(Paragraph(Text(
                        "Expanding relative entropy cancels the self-logarithm term against "
                        + "von Neumann entropy. Substitution of the Gibbs logarithm, trace "
                        + "normalization, and cyclicity of the trace give the equality. "
                        + "The density matrix may fail to commute with H."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("entropy-relative-to-uniform-state"),
                    DeclarationHandle.Create(Owner + "entropy_uniform_identity"),
                    H("The maximally mixed reference state"),
                    StatementSource.FromAuthor(Disp(All(
                        [Bound("n", F.Id("FiniteNonemptyType")),
                            Bound("rho", Call("DensityState", n))],
                        Eqn(Add(Call("vonNeumannEntropy", rho),
                            Call("quantumRelativeEntropy", rho, Call("gibbsState", Num(0)))),
                            Call("log", Call("card", n)))))),
                    AssessedProvenance.FromLiterature(
                        LibraryNoteRef.Create("D5/L/Quantum/watrous2018entropicidentities")),
                    Blocks(Paragraph(Text(
                        "At H = 0 the partition function is card(n), and gibbs_state_zero "
                        + "identifies the Gibbs matrix with I/card(n). Substitution into the "
                        + "general identity gives entropy plus relative entropy to the "
                        + "maximally mixed state equal to log(card(n))."))),
                    DescribeRole.Theorem))));
    }

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Eqn(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
