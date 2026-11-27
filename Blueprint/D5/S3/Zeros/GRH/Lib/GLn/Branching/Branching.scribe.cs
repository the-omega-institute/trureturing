using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GLn.Branching;

internal sealed class BranchingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Branching", H("Branching"),
        Blocks(
            Paragraph(Text("Extremal vector is cyclic; Schur's lemma for U(n) on Weyl modules. Dual of a Weyl module by Jacobi complementary minors, as unimodular integral isometry. Multiplicity-one branching GL(n+1) to GL(n) as an integral map with explicit norm bound.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GLn/Branching/Branching.exists_branching_matrix"),
                H("exists_branching_matrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Branching from rank n+1 to n = |n_τ|: let κ = γ+κ', κ₀(h) = κ'(h)+γ(h+1) for 0<h<n, e₀ = e+κ'(n), κ'(i) = 0 for i<q. Some integer matrix br satisfies SpansBranchingMaps, br·ρ_{κ,e}(diag(g,s)) = ∏_τ s_τ^{e_τ+∑_{1≤h≤n}γ_τ(h)}·ρ_{κ₀,e₀}(g)·br over fields of characteristic 0, and ‖br‖ ≤ L^{3L} in Gram norms whenever L ≥ ∑_τ∑_{q≤h<n} hκ₀(h).")))))));
}
