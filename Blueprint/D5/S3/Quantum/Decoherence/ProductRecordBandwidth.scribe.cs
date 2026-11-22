using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class ProductRecordBandwidthDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Decoherence/ProductRecordBandwidth.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp bandwidth for binary product records and separation from bounded cq conditional entropy.",
        H("Binary product records and Gibbs bath bandwidth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-product-required-width"),
                DeclarationHandle.Create(Module + "product_requiredWidth"),
                H("The required width is a sum over overlaps"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For overlaps 0 ≤ s_j < 1 the product memory has binary factors (1 ± s_j)/2 in its eigenbasis. The required width is β⁻¹ times the sum of log((1+s_j)/(1−s_j))."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-product-bath-bounds"),
                DeclarationHandle.Create(Module + "product_bandwidth_lower_bound"),
                H("Product lower bounds on bandwidth and dimension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/reeb2011hilbert")),
                Blocks(
                    Paragraph(Text("For any finite reduced preparation using an independent Gibbs bath, the spectral width is bounded below by the exact product formula, and the bath dimension is at least the product of (1+s_j)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-product-width-attainment"),
                DeclarationHandle.Create(Module + "product_bandwidth_attained"),
                H("A product-sized bath attains the product width"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/reeb2014improved")),
                Blocks(
                    Paragraph(Text("Indexing the bath by binary words gives the aligned Gibbs bath and an attaining tensor swap for the reduced preparation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-product-pure-record-memory"),
                DeclarationHandle.Create(Module + "productCQ_memory"),
                H("The product spectrum is an actual pure-record marginal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The uniform classical–quantum ensemble uses explicit normalized pure tensor records with the given local overlaps. Its average record is diagonal and has precisely the product spectrum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-product-cq-entropy"),
                DeclarationHandle.Create(Module + "productCQ_conditionalEntropy"),
                H("Conditional entropy of the explicit cq state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/delrio2011thermodynamic")),
                Blocks(
                    Paragraph(Text("The von Neumann entropy of the joint state minus that of its record marginal equals the sum of log 2 minus the binary entropy at (1+s_j)/2. Entropy is measured in nats."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-product-width-asymptotic"),
                DeclarationHandle.Create(Module + "product_width_asymptotic"),
                H("Asymptotic dimensionless width"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("If an envelope for the row overlaps tends to zero and the row sum of squares tends to λ > 0, the dimensionless width divided by twice the sum of overlaps tends to one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-product-cq-entropy-bandwidth"),
                DeclarationHandle.Create(Module + "productCQ_small_overlap"),
                H("Bounded cq conditional entropy with divergent bandwidth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/delrio2011thermodynamic")),
                Blocks(
                    Paragraph(Text("With the same triangular-array assumptions and fixed β > 0, the exact required bandwidth tends to infinity, while the actual cq conditional entropy eventually lies in [0, λ+1]. The exact optimization is stated for the preparation of the product memory from the maximally mixed state."))),
                DescribeRole.Theorem))));
}
