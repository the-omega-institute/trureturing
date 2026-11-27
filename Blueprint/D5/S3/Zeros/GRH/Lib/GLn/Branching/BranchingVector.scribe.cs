using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GLn.Branching;

internal sealed class BranchingVectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Branching Vector", H("Branching Vector"),
        Blocks(
            Paragraph(Text("Norm on Weyl's lattice, Zariski density of U(n), hook number clears denominators. Cartan multiplication: integral, isometric, equivariant, split; submultiplicativity of norms. Denominator of the branching vector bounded by the columns of height at least q.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GLn/Branching/BranchingVector.exists_smul_weylKernel_mul_eq_toPoly"),
                H("exists_smul_weylKernel_mul_eq_toPoly"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let κ₀(h) = κ'(h)+γ(h) for 0<h<|n_τ|, κ'(i) = 0 for i<q, and f number the rows with rowPos ≤ f+1. Some integer c>0, at most L^{3L} whenever L ≥ ∑_τ∑_{q≤h<|n_τ|} hκ₀(h), and integer vector η satisfy c·K_γ·K_{κ'} = toPoly η, kernels weylKernel at the permutation arrays of f and rowPos.")))))));
}
