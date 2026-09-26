using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class QubitChordFamilyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One joint-observation role retains the full quantum chord and spectral Fisher-information law.",
        H("QubitChordFamily"),
        Blocks(
            Node("signature", "signature", "Physical processor states",
                "Params and Role are Unit, anchors are Empty, and State is QuantumChannel (Fin 3 × Fin 2) (Fin 3). Output is a real-linear map from the three-dimensional Bloch space to the two probe-indexed complex 3 × 3 matrices. Neither processors nor outputs are finitely sampled."),
            Node("actual", "actual", "Joint observation",
                "The actual readout is jointObservation G. A single role uniformly replaces its three uses in the law: orthogonal-kernel membership of c, membership of v, and the projected Bloch-curve identity. Spectral QFI is retained in the conclusion, not introduced as a separately observed role."),
            Node("project-x", "projectX", "Bloch-coordinate intervention",
                "projectX is the real-linear projection retaining only the x coordinate. It is composed before the physical processor's joint observation; it does not change the original processor, program curve or exactness hypotheses."),
            Node("rejected", "rejected", "Projected observation family",
                "The rejected readout is jointObservation G composed with projectX. The Reg mirror supplies a physical processor and exact curve that refute its law, and distinct processors whose actual joint observations establish dependence. Merely defining this realization is not that proof."),
            Node("arena", "arena", "Complete chord and spectral QFI",
                "The law preserves all a with 0 < a < 1, processors G, program curves rho, density hypotheses and exactness for both probes on (2a-1,1). It retains probe density, nonzero chord direction, all bounds on b, the coupled c/v kernel and projection clauses, two-probe affine exactness for every real u, the norm and positivity equivalences with [b,1], trace one, strict interior norm, pure endpoints, and endpoint-overlap bounds. The second conjunct states that for every u in (2a-1,1), if rho is differentiable at u, the lower bound (1-a²)/((1-u)(1+u-2a²)) holds on spectralQFI of the same rho and its derivative."),
            Paragraph(Text("The preserved source is "),
                Ref("D5/S3/Quantum/Information/ActualQubitChordObstruction.actual_two_probe_chord_and_qfi"),
                Text(". Its Reg mirror supplies the full-statement bridge, variation, sole-role sensitivity and actual observational dependence. Source reconstruction ties all three occurrences to the same observation and preserves the original chord-plus-QFI conjunction; it does not claim an independent QFI sensitivity result or exactness for arbitrary signals.")),
            Paragraph(Text("This is repository-derived consumer-model content, with no new theorem wrapper, novelty, coverage or freeze claim. Raw open denotes unknown residual information, not an infinity, undecidability or completeness certificate.")))));

    private static DocumentBlock.Describe Node(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/QubitChordFamily." + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
