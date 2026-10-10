using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class SharedPhaseBudgetGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict common-phase budget gap for the four-phase recovery matrix.",
        H("SharedPhaseBudgetGap"),
        Blocks(Describe.Lean(
            DescribeId.Create("first-hop-original"),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/SharedPhaseBudgetGap.first_hop_original"),
            H("Strict shared-phase budget gap"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let s be the positive square root of two, let nu = 3 - 2s, and let B have rows (-1/s, -1/s, 1, 0) and (-1/s, -i/s, 0, 1). Let M = B B star. For a finite family of phase vectors z_j in the four-dimensional complex torus and nonnegative real weights p_j, assume the residual M minus the weighted sum of the rank-one matrices (B z_j)(B z_j) star is positive semidefinite.")),
                Paragraph(Text("There is a positive real gamma, independent of the finite family, such that the total weight is at most 4/nu - gamma. The proof identifies every equality phase as one of two explicit one-parameter families, computes M as the matrix with diagonal entries 2 and off-diagonal entries (1-i)/2 and (1+i)/2, and uses compactness together with a shared non-diagonal perturbation to obtain a uniform strict separation.")),
                Paragraph(Text("The quantified family allows any positive finite index type; the underlying phase-cone estimate also applies to the empty family. The statement concerns the compressed shared budget and does not assert an operational realization theorem or a sharp small-noise asymptotic."))),
            DescribeRole.Theorem))));
}
