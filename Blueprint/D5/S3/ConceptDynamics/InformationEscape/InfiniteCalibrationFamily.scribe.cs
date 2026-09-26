using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class InfiniteCalibrationFamilyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The calibration consumer observes a real control witness over the full infinite calibration domain.",
        H("InfiniteCalibrationFamily"),
        Blocks(
            Node("signature", "signature", "Real parameters and controls",
                "Params is the dependent triple (a, δ, b) of real numbers. State and Output are both the entire real line, with one Unit role and Empty anchors. There is no finite truncation, sampling or replacement by a finite witness type."),
            Node("actual", "actual", "Identity control observation",
                "The actual readout returns the real control k itself at every parameter triple. Distinct real states can therefore supply the required actual observational dependence."),
            Node("rejected", "rejected", "Zero control intervention",
                "The rejected readout sends every real control to zero. InfiniteScalarControl requires strict positivity of the observed control, so the Reg proof can refute the intervened law at an admissible parameter triple. The name rejected is an operand definition; the law-breaking proof lives in Reg."),
            Node("arena", "arena", "Full calibration existence law",
                "The law retains all real a, δ, b and all seven premises: 0 < a < 1, 0 < δ, δ < (1-a)/4, δ < (1-a²)/16, 0 < b and b < 1-a/(1-δ). It asks for a real k whose observed value satisfies the original InfiniteScalarControl. That predicate retains strict physicality and analyticity on the whole interval (a,1), and the equivalence between simultaneous value/derivative calibration jets and the positive-natural nodes 1-b/n."),
            Paragraph(Text("The source declaration is "),
                Ref("D5/S3/Quantum/Information/InfiniteCalibrationControl.result"),
                Text(". Its Reg mirror retains the full source statement, uses the identity bridge, and supplies actual-law, variation, sole-role sensitivity and dependence proofs. Source binding selects the three real parameters and the existential control occurrence; it does not replace the infinite real domain with the counterexample's single parameter triple.")),
            Paragraph(Text("These are repository-derived consumer definitions, not new proven theorem wrappers. No novelty, coverage or freeze status is asserted. The raw open residual records unknown residual information and provides no infinity, undecidability or completeness certificate.")))));

    private static DocumentBlock.Describe Node(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/InfiniteCalibrationFamily." + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
