using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class FiniteHistoryFamilyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite-history consumer retains the full dependent probability law across all history lengths.",
        H("FiniteHistoryFamily"),
        Blocks(
            Node("signature", "signature", "All history fibers",
                "Parameters are triples (J, Z, N) with J : Type u, Z : Nat → Type v and N : Nat. States are J × History Z N, the sole Unit role outputs History Z N, and anchors are Empty. The family retains both universes and every N, including zero; finiteness of each history does not make the family domain finite."),
            Node("law", "Law", "Three conjuncts on the original measure",
                "The law retains the probability-measure assertion for historyLaw ν K N, the integral-to-finite-sum identity for every t ≤ N and test function, and the almost-everywhere conditional-expectation identity for every t < N. All nonnegativity and normalization premises for ν and K remain. The readout replaces the history projection in the integral, conditioning and posterior expression while the original measure remains fixed."),
            Node("sigma", "readoutSigma", "Readout-induced conditioning",
                "The conditioning sigma-algebra is the comap of the t-prefix of the observed history. At the identity readout it is the source history filtration; changing observations must also change this conditioning object, not just the integrand."),
            Node("full-law", "FullLaw", "Complete thirteen-binder statement",
                "FullLaw quantifies J and Z, the six Fintype/MeasurableSpace/MeasurableSingletonClass dictionaries (including their dependent families), and ν, hν, K, N, hK: thirteen binders in the source order, with universes u and v retained. No positive-length restriction is added. At N = 0 the t < N clause has no instances, while the other two conjuncts remain."),
            Node("actual", "actual", "Actual history observation",
                "The actual sole readout returns the history component of the state. The arena applies FullLaw to this complete readout family, not to a chosen distribution or a finite sample of histories."),
            Node("rejected", "rejected", "One-fiber intervention",
                "badFiber changes only (ULift Unit, the constant ULift Bool family, 1), returning the always-true history there and the original history elsewhere. targetNu is unit mass, targetK always emits false, and targetF detects true. These operands support the law-breaking witness without restricting FullLaw to that fiber."),
            Paragraph(Text("The preserved source is "),
                Ref("D5/S3/Estimation/DataProcessing/FiniteHistoryConditionalExpectation.history_law_conditional_expectation"),
                Text(". Its Reg mirror supplies the definitional bridge and uses Reg/Support/FiniteHistoryFamily for variation, sensitivity and actual observational dependence. Source coordinates retain J, Z and N, with the complete statement and dictionaries reconstructed by source binding.")),
            Paragraph(Text("This is repository-derived consumer-model content, not a new theorem wrapper or a coverage, novelty or freeze claim. The original theorem and Reg proofs remain the authority for their respective obligations. The registration's raw open residual means unknown residual information, not infinity, undecidability or completeness.")))));

    private static DocumentBlock.Describe Node(string id, string declaration, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/InformationEscape/FiniteHistoryFamily." + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
