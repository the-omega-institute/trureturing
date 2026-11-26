using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.GeodesicCMI;

internal sealed class CapelCostaRicoForwardGeodesicCMIDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/GeodesicCMI/CapelCostaRicoForwardGeodesicCMI.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Divergence/capelcostarico2026geodesic");
    private static readonly LibraryNoteRef Masking =
        LibraryNoteRef.Create("D5/L/Divergence/ambainis2000private");
    private static readonly LibraryNoteRef ConditionalEntropy =
        LibraryNoteRef.Create("D5/L/Divergence/bluhm2023continuity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At each fixed positive geodesic parameter, both forward deficits have a log 2 gap for faithful pairs that share every two-body marginal and approach each other.",
        H("Forward geodesic CMI at one fixed parameter"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forward-geodesic-cmi-onesidedcmi"),
                DeclarationHandle.Create(Prefix + "oneSidedCMI"),
                H("One-sided forward deficit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "In equation (357) the fine divergence runs from the joint state to its AB marginal tensored with the chosen C reference. The reduced term runs from the actual BC marginal to the B marginal tensored with the same reference."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("forward-geodesic-cmi-twosidedcmi"),
                DeclarationHandle.Create(Prefix + "twoSidedCMI"),
                H("Two-sided forward deficit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Equation (357) uses the C marginal of the input state as the reference for the one-sided formula. On this witness family the C marginal is I/2, which agrees with the chosen one-sided reference."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("forward-geodesic-cmi-forwardgap"),
                DeclarationHandle.Create(Prefix + "ForwardGap"),
                H("Signed gap limits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For the given sequence of matched faithful pairs, both differences take the first state's deficit minus the second's. Both differences converge to the natural logarithm of two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("forward-geodesic-cmi-regularization-tendsto"),
                DeclarationHandle.Create(Prefix + "regularization_tendsto"),
                H("Regularization at fixed reference"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "At fixed u and fixed 0 < t ≤ 1, continuity on the positive semidefinite cone gives convergence to the unsmoothed value log 2 as η decreases to zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-geodesic-cmi-exists-pointwise"),
                DeclarationHandle.Create(Prefix + "exists_pointwise"),
                H("Faithful pairs for a fixed parameter"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source, Masking, ConditionalEntropy),
                Blocks(Paragraph(Text(
                    "For every fixed 0 < t ≤ 1, choose u_n = 1/(n+3) and select a positive regularization at each index using the fixed-reference limit. Both faithful states share their AB marginal within each pair. Their B is I/2 and their AC and BC are I/4 throughout the sequence. The trace distance tends to zero from above. The two coarse terms vanish and both fine comparisons use S_u, which gives zero on the reference arm. This theorem makes the sequence choice after fixing t."))),
                DescribeRole.Theorem)),
        []));
}
