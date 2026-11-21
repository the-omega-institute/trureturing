using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzModularFrequencyQuantizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordinary Petz squared trace error is controlled by the number of retained frequency centres and the exact logistic cost of the assignment.",
        H("Retained modular frequency quantization for ordinary Petz recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ordinary-petz-exact-phase-discrepancy"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzModularFrequencyQuantization.exact_phase_discrepancy"),
                H("Exact logistic discrepancy on the retained spectral law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/yang2026quantumdataprocessing")),
                Blocks(
                    Paragraph(Text("Let T = Φ(ρ) and Q = Φ(σ) be the actual retained states of a finite CPTP channel. For positive eigenvalues pₖ and qₗ, the spectral pair has frequency log pₖ − log qₗ and mass pₖ times the squared overlap of the corresponding eigenvectors. The finite sum combines the masses of coincident frequencies and agrees with the spectral-projection formula for repeated eigenvalues.")),
                    Paragraph(Text("An assignment ψ changes only the retained phase of each spectral pair. The exact weighted squared Frobenius discrepancy between the original and assigned completed Stinespring amplitudes equals J, the mass-weighted sum of 2(1 − κ(ω − ψ(ω))). Here κ(0) = 1 and κ(x) = (x/2)/sinh(x/2) away from zero.")),
                    Paragraph(Text("The completed Stinespring columns form a coisometry. Trace pairing with the actual channel then weights the retained factor by Q. In the positive spectral columns, orthogonality removes cross terms and Q cancels the inverse square-root weights."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("ordinary-petz-quantized-phase-trace-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzModularFrequencyQuantization.ordinary_petz_traceNorm_sq_le_quantized_phase_cost"),
                H("Physical ordinary Petz recovery with finitely many centres"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/yang2026quantumdataprocessing")),
                Blocks(
                    Paragraph(Text("Take the supported relative modular model of the actual channel and density states with supp ρ contained in supp σ. Assign every positive-mass retained frequency to a finite set of m real centres. The squared trace norm of ρ minus its ordinary Petz recovery is at most 4(m + 1)(√Δ + √J)², where Δ is the channel's finite trace-log Umegaki loss.")),
                    Paragraph(Text("The inverse square root acts on the positive spectrum of Q and vanishes on its kernel. The bound applies to singular retained states and uses no positive spectral lower bound. Zero-mass pairs have zero amplitude coefficients and impose no restriction on the assignment.")),
                    Paragraph(Text("Every assigned phase equals one at zero, so the assigned amplitude has the same zero-phase Gram and ordinary Petz endpoint. The weighted L² triangle inequality combines the actual strip deficit with the exact discrepancy. Coordinatewise logistic evaluation counts the shifted centres and the constant term, and the physical Gram inequality contributes the factor four."))),
                DescribeRole.Theorem))));
}
