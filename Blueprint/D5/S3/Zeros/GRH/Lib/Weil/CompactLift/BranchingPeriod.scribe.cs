using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.CompactLift;

internal sealed class BranchingPeriodDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Branching Period", H("Branching Period"),
        Blocks(
            Paragraph(Text("Matrix of jets is an equivariant kernel for definite unitary theta lifts. Restriction period of algebraic forms as class sum through the unique branching map.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/CompactLift/BranchingPeriod.integral_algFormCoeff_blockEmb"),
                H("integral_algFormCoeff_blockEmb"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let V be standard and A satisfy SpansBranchingMaps. For t, c there is C such that, for smooth ψ, automorphic Φ(x,g) = L_g(x·c) and open K ≤ K₀, ∫ Φ(h) ψ_t(diag(h,u)) dh is C/[K₀:K] times the integral, for vol K = 1, of L_h(Aψ(diag(h,u))).")))))));
}
