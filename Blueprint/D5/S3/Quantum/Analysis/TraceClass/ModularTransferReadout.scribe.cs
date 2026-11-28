using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;

internal sealed class ModularTransferReadoutDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/TraceClass/ModularTransferReadout.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/jia2026vacuumcorrelations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite sums of product probes characterize Hilbert–Schmidt modular transfer.",
        H("The norm of the reflected correlation on finite tensor readouts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-readout-characterization"),
                DeclarationHandle.Create(Module + "finite_readout_bound_iff"),
                H("Existence of a uniform finite-readout bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A reflected correlation is bounded on finite sums of elementary tensor probes "
                    + "exactly when its transfer is Hilbert–Schmidt."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sharp-finite-readout-bound"),
                DeclarationHandle.Create(Module + "least_finite_readout_bound"),
                H("The optimal readout bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The optimal bound squared is the trace of the positive transfer square. "
                    + "Finite families drawn from a Hilbert basis approach that bound. The "
                    + "quarter-weighted product-state embedding connects the norm to order-two "
                    + "sandwiched Rényi mutual information in split local algebras."))),
                DescribeRole.Theorem))));
}
