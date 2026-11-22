using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class BinaryRecordMemoryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/BinaryRecordMemory.";
    private static LibraryNoteRef EldarForney =>
        LibraryNoteRef.Create("D5/L/Entropy/eldarforney2001quantumdetection");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Walsh weights give an explicit compression penalty, and overlap-one pairs reduce the occupied span.",
        H("Finite memory for binary pure records"),
        Blocks(
            Describe.Lean(DescribeId.Create("binary-memory-product-bound"),
                DeclarationHandle.Create(Module + "coordinateProductRecord_success_le"),
                H("The phase penalty on the original heterogeneous product carrier"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(EldarForney),
                Blocks(
                    Paragraph(Text("For k independent fair bits, let sᵢ be each normalized pair's overlap modulus and assume every sᵢ is below one. Write N = 2ᵏ and g for the uncompressed joint optimum, the product of (1 + sqrt(1 − sᵢ²)) / 2. An arbitrary CPTP encoder from the original product carrier to dimension M, followed by an output POVM, has success at most min(M / N, g − (1 − M / N) c). Here c is the product of (1 − sᵢ + sqrt(1 − sᵢ²)) / 2.")),
                    Paragraph(Text("The product optimum uses the Walsh measurement, a case of the square-root measurement in Theorem 4 of Eldar and Forney. Isometric transport and the phase dual gap supply the CPTP memory bound."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("binary-memory-product-threshold"),
                DeclarationHandle.Create(Module + "coordinateProductRecord_optimum_attainable_iff"),
                H("Strict overlaps give an exact threshold of 2ᵏ"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("When all local overlap moduli are below one, the full joint optimum on the original product carrier is attainable through a CPTP memory exactly when its dimension is at least 2ᵏ. The local carriers may have different dimensions. The threshold specializes the known pure-state uniqueness and dimension argument to the occupied Walsh span."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("binary-memory-duplicate-labels"),
                DeclarationHandle.Create(Module + "repeatedLabel_success_set"),
                H("A uniform duplicate label scales the whole attainable success set"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For uniform labels (x, y) whose conditional states depend only on x, sum the labelled effects over y to obtain a POVM for x. The success values for guessing the pair are exactly the success values for guessing x divided by the size of the nonempty y-type. A fixed y-guess lifts any POVM for x."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("binary-memory-active-threshold"),
                DeclarationHandle.Create(Module + "activeProductRecord_optimum_and_memory"),
                H("Overlap-one coordinates affect the guessing value and reduce the required memory"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For arbitrary normalized binary pairs, let r count the overlap-one coordinates. The attained whole-word optimum is 2⁻ʳ times the product of the single-coordinate optima over the k − r active coordinates. A CPTP memory attains that value exactly when its dimension is at least 2 raised to k − r. After rephasing, each repeated pair gives the same conditional density for either bit. The active Walsh carrier transports isometrically and the repeated labels aggregate."))),
                DescribeRole.Theorem))));
}
