using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class FibonacciQutritSingularSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Singular qutrit comparisons reduce to a common qubit with an exact ambient loss.",
        H("Fibonacci singular qutrit support"), Blocks(
            Describe.Lean(DescribeId.Create("singular-support-reduction"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/FibonacciQutritSingularSupport.singular_support_reduction"),
                H("Exact support reduction and trace pairings"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Divergence/trureturing2026fibonaccisingularsupport"),
                    LibraryNoteRef.Create("D5/L/Divergence/audenaert2014skew")),
                Blocks(
                    Paragraph(Text(
                        "Let X be a finite family of qutrit density states, with reference weights q "
                        + "strictly positive and comparison weights p satisfying 4q/3 ≤ p ≤ 7q/3 "
                        + "pointwise. Write C and A for the weighted sums with q and p, respectively. "
                        + "For a null-class density state X₀ and e > 0, set B = C + e X₀ and "
                        + "Δ = Re Tr[A(log B − log C)]. If C fails positive definiteness or has rank "
                        + "at most two, there is a family Y of qubit density states with the same "
                        + "weights. Its weighted sums A₂ and C₂ satisfy D(A‖B) = D(A₂‖C₂) − Δ. "
                        + "Here Δ ≥ 0, with Δ = 0 exactly when C X₀ = 0. Every pair "
                        + "satisfies Re Tr(YᵢYⱼ) = Re Tr(XᵢXⱼ), including i = j.")),
                    Paragraph(Text(
                        "Diagonalize C by one unitary and reindex a zero eigenvalue onto the last "
                        + "coordinate. Each qᵢXᵢ is dominated by C, so its diagonal entry there "
                        + "vanishes. Positivity forces its column to vanish, and Hermiticity gives "
                        + "the row. Removing that coordinate preserves positivity and trace. "
                        + "Multiplying the resulting block matrices also preserves the trace "
                        + "pairings used in the qubit mixed-state comparison.")),
                    Paragraph(Text(
                        "Both weighted sums have a zero scalar block. The block logarithm and "
                        + "unitary trace invariance identify D(A‖C) with D(A₂‖C₂). "
                        + "The supported weighted log increment with bounds 4/3 and 7/3 supplies "
                        + "the ambient loss and its zero set, including when B is singular.")),
                    Paragraph(Text(
                        "For the Fibonacci triple use q = (a,b,c) and "
                        + "p = (4a/3,5b/3,7c/3). The construction handles one- and "
                        + "two-dimensional positive support with the same conclusion."))),
                DescribeRole.Theorem))));
}
