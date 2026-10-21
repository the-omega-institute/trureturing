using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class TraceNormDiscordMutualCorrelationBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/TraceNormDiscordMutualCorrelationBound.";
    private const string Companion = "D5/S3/Quantum/Information/GeometricDiscordMutualCorrelationBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumContext/jakobczyk2016maximalmutual");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every two-qubit density matrix, one-sided trace-norm geometric discord is at most maximal mutual correlation.",
        H("Trace-norm discord and maximal mutual correlation"), Blocks(
            Paragraph(Text(
                "The qubits are ordered A, B, with matrix indices in Fin(2) × Fin(2). "
                    + "Fin(2) indexes 0, 1, and U(2) is the group of unitary complex 2 by 2 matrices. "
                    + "A dagger denotes conjugate transpose, I denotes the identity, and vector "
                    + "lengths are Euclidean. The trace norm ‖m‖₁ is "),
                Ref("D5/S3/Quantum/Foundation/FiniteTraceDistance.traceNorm"),
                Text(", namely Re tr(√(m†m)). Write 𝒫_U(ρ) = measuredState(U,ρ) for "),
                Ref(Companion + "measuredState"),
                Text(", the unread measurement Σ_k (P_k ⊗ I)ρ(P_k ⊗ I) on A, "
                    + "where P_k projects onto column k of U. Write C_M(ρ) for "),
                Ref(Companion + "maximalMutualCorrelation"),
                Text(", the supremum of the absolute local covariances over complex "
                    + "2 by 2 matrices of operator norm one, without a Hermitian restriction.")),
            Describe.Lean(
                DescribeId.Create("trace-norm-discord-mutual-correlation-tracenormdiscord"),
                DeclarationHandle.Create(Prefix + "traceNormDiscord"),
                H("One-sided trace-norm geometric discord"),
                StatementSource.FromAuthor(Disp(DiscordFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The infimum ranges over all orthonormal measurement bases on A. "
                        + "For a density matrix this is the source's D₁, with no factor of one half. "
                        + "The definition also applies to every complex two-qubit matrix, "
                        + "without positivity or normalization assumptions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("trace-norm-discord-mutual-correlation-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The two-qubit trace-norm bound"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The proposition states D₁(ρ) ≤ C_M(ρ) for every positive semidefinite "
                        + "two-qubit matrix of trace one, including pure and mixed states. "
                        + "The source proves the Bell-diagonal case and conjectures the "
                        + "inequality for general two-qubit states."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("trace-norm-discord-mutual-correlation-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Maximal mutual correlation bounds trace-norm discord"),
                StatementSource.FromAuthor(Disp(Named("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Let ρ be positive semidefinite with trace one, and let x be its "
                            + "Bloch vector on A. Choose a unit u parallel to x when x ≠ 0, "
                            + "and any unit u when x = 0. Measure A in the eigenbasis of u·σ. "
                            + "The existence of such a basis is expressed by "),
                        Ref(Companion + "marginal_basis"),
                        Text(". Work in that basis, using "),
                        Ref(Companion + "rotateState"),
                        Text(", so the first two coordinates of x vanish and u is the third "
                            + "coordinate vector. Unitary conjugation preserves the trace "
                            + "norm of the disturbance.")),
                    Paragraph(Text(
                        "Write R for the state in this basis, x and y for its Bloch vectors, "
                            + "T for its Pauli correlation tensor, and Q = T − xyᵀ for "),
                        Ref(Companion + "connectedCorrelation"),
                        Text(". Put P = I − uuᵀ. Since Px = 0, the disturbance "
                            + "δ = R − 𝒫_I(R) is Σ_ij (PQ)_ij σ_i ⊗ σ_j/4. "
                            + "Diagonalizing the 2 by 2 Gram matrix of Qᵀ restricted to the plane "
                            + "perpendicular to u gives a rotated orthonormal pair v′, w′ with "
                            + "a = Qᵀv′ perpendicular to b = Qᵀw′.")),
                    Paragraph(Text(
                        "The disturbance is δ = (A₁ + A₂)/4, where "
                            + "A₁ = (v′·σ) ⊗ (a·σ) and A₂ = (w′·σ) ⊗ (b·σ). "
                            + "These are Hermitian Pauli products. Anticommutation in each "
                            + "tensor factor makes A₁ and A₂ commute. With α = |a| and "
                            + "β = |b|, they satisfy A₁² = α²I, A₂² = β²I and tr(A₁A₂) = 0.")),
                    Paragraph(Text(
                        "Interchange the two terms if necessary so α ≥ β. If α = 0, "
                            + "both products vanish. Otherwise the positive square root is "
                            + "√(δ†δ) = (αI + α⁻¹A₁A₂)/4. Its positivity follows from "
                            + "the equal expression ((A₁ + A₂)†(A₁ + A₂) + (α² − β²)I)/(8α), "
                            + "and squaring gives δ†δ. Since tr(I) = 4 and tr(A₁A₂) = 0, "
                            + "taking the trace gives ‖δ‖₁ = α = max(|a|, |b|).")),
                    Paragraph(Text(
                        "For a ≠ 0, choose unit spin directions c = v′ and d = a/|a|. "
                            + "Their covariance in R is cᵀQd = |a|. Conjugate c·σ back "
                            + "to the original basis on A; its operator norm is still one. "
                            + "The bound "),
                        Ref(Companion + "rotated_spin_witness"),
                        Text(" therefore gives C_M(ρ) ≥ |a|. The zero case follows from "
                            + "nonnegativity, and the same argument with w′ and b gives "
                            + "C_M(ρ) ≥ |b|. The infimum defining discord is at most this "
                            + "measurement's disturbance, so D₁(ρ) ≤ ‖δ‖₁ "
                            + "= max(|a|, |b|) ≤ C_M(ρ)."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("jakobczyk-2016-trace-norm-discord-mutual-correlation-bound"),
                    ResolutionKind.Proved))
        )));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula ImpliesTo(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Index() => Call("Fin", D(2));
    private static Formula TwoQubit()
    {
        Formula indices = Parenthesized(Seq(Index(), Times, Sp, Index()));
        return Call("Matrix", indices, indices, Complexes());
    }

    private static Formula DiscordFormula()
    {
        Formula u = F.Id("U");
        Formula disturbance = Parenthesized(new Formula.Binary(Rho, FormulaBinaryOperator.Subtract,
            Call("measuredState", u, Rho)));
        Formula norm = new Formula.Subscript(new Formula.Norm(disturbance), D(1));
        Formula values = new Formula.SetBuilder(norm, u, Call("unitaryGroup", Index(), Complexes()));
        return All(Rho, TwoQubit(), Equal(Call("traceNormDiscord", Rho), Call("inf", values)));
    }

    private static Formula ClaimFormula()
    {
        Formula correlation = new Formula.Apply(new Formula.Subscript(F.Id("C"), F.Id("M")), [Rho]);
        Formula bound = new Formula.Relation(Call("traceNormDiscord", Rho),
            FormulaRelationOperator.LessThanOrEqual, correlation);
        Formula statement = All(Rho, TwoQubit(), ImpliesTo(Call("PosSemidef", Rho),
            ImpliesTo(Equal(Call("tr", Rho), D(1)), bound)));
        return new Formula.Logic(Named("claim"), FormulaLogicOperator.Iff, Parenthesized(statement));
    }
}
