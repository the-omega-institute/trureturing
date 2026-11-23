using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMSlotCorrectionLoweringDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlotCorrectionLowering.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lowering and physical Wick corrections at the four punctures",
        H("Signed scales and correction endpoint partitions"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-four-m-slot-correction-lowering-same-slot-correction"),
                DeclarationHandle.Create(Prefix + "same_slot_correction"),
                H("Signed scales at one puncture"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any lattice, chart, real argument, puncture and word with prescribed colours "
                    + "and modes, the zero-mean physical correction Wick value is the product of the lifted signed "
                    + "scales at every occurrence times the zero-mean Wick value of the central pair evaluated at "
                    + "the negative lowering parameter of the puncture."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-four-m-slot-correction-lowering-slot-lowering-partition"),
                DeclarationHandle.Create(Prefix + "slot_lowering_partition"),
                H("Inverse lowering as a partition sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a lattice with unit Gram determinant and a finite label type, take a word "
                    + "with prescribed colours and modes at one chart puncture. With a cutoff strictly above the "
                    + "degree of its Wick polynomial, the sum of lowering powers on the occurrence monomial, "
                    + "weighted by powers of the negative lowering parameter divided by the corresponding "
                    + "factorials, equals the position partition sum of central contractions and surviving "
                    + "evaluated creators."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-four-m-slot-correction-lowering-physical-correction-by-slot"),
                DeclarationHandle.Create(Prefix + "physical_correction_by_slot"),
                H("Independent four-puncture correction factors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a lattice with unit Gram determinant and a finite label type, assign a "
                    + "puncture, colour and mode to each label. In any chart and at any real argument, the physical "
                    + "correction Wick value of a word with zero mean is the product of the signed scales over "
                    + "all occurrences times the product of four central contraction sums. Each uses the ordered "
                    + "subword at the corresponding puncture and its own negative lowering parameter."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-four-m-slot-correction-lowering-physical-marked-coefficient-by-slot"),
                DeclarationHandle.Create(Prefix + "physical_marked_coefficient_by_slot"),
                H("Within-puncture factors in the fixed-charge marked coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a lattice with unit Gram determinant, a fixed charge, a chart and chart "
                    + "flag, and a real argument strictly between zero and one, take the specified spatial degrees and first degree "
                    + "in each mark of a word of distinct labels from a finite type with decidable equality. "
                    + "The physical Taylor coefficient at zero equals the charge exponential times the ordered "
                    + "position partition sum. Correction endpoints contribute their signed scales and four "
                    + "within-puncture contraction sums. The complement contributes the native Taylor covariance "
                    + "and the extracted signed charge-linear means through the affine Wick value."))),
                DescribeRole.Theorem))));
}
