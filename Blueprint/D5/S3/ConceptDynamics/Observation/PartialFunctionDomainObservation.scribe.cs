using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Observation;

internal sealed class PartialFunctionDomainObservationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two states agree in every jointly successful context, but a partial operation "
            + "succeeds at only one of them.",
        H("Partial Function Domain Observation"),
        Blocks(
            Paragraph(Text(
                "There are two states, a and b. The readout q takes values in the two-element "
                    + "type Fin 2 and is constantly zero. The single unary operation fixes a "
                    + "and is undefined at b. A context is any finite iteration of that "
                    + "operation, including the identity at depth zero. Failure propagates "
                    + "through every further operation.")),
            Paragraph(Text(
                "An observation has type Option (Fin 2). A successful zero is some zero, "
                    + "representing the tagged pair (1,0); failure is the distinct none tag. "
                    + "The success tag records definedness, not a numerical encoding of "
                    + "the resulting state.")),
            Describe.Lean(
                DescribeId.Create("context-observation-profile"),
                DeclarationHandle.Create(Prefix + "context_observation_profile"),
                H("Exact observations at every finite depth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At a, every context succeeds and reads zero. At b, only the depth-zero "
                        + "identity succeeds; every positive depth fails. Induction on the "
                        + "context length proves this for all natural depths."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partial-domain-not-q-saturated"),
                DeclarationHandle.Create(Prefix + "partial_domain_not_q_saturated"),
                H("The partial domain is not a union of readout fibers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The domain is the singleton containing a. The two states have equal q "
                        + "readings but different domain membership, so that singleton is "
                        + "not saturated under q."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-success-domain-refutation"),
                DeclarationHandle.Create(Prefix + "common_success_domain_refutation"),
                H("Common-success agreement fails to preserve definedness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "CommonSuccessPreservesDomains asserts that states agreeing in every "
                        + "jointly successful context have equal membership in the operation "
                        + "domain. The pair a,b refutes that assertion: every shared successful "
                        + "reading is zero, but the operation is defined only at a."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partial-function-domain-counterexample"),
                DeclarationHandle.Create(Prefix + "partial_function_domain_counterexample"),
                H("The complete two-state counterexample"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem combines the constant readout, its failure to reach one "
                            + "in Fin 2, the two operation values, the singleton domain, agreement "
                            + "in all jointly successful contexts, and both failures of domain "
                            + "preservation. At depth one the full observations are some zero "
                            + "and none, and these are unequal.")),
                    Paragraph(Text(
                        "Replacing none by the ordinary readout zero makes the observations "
                            + "of a and b equal again at every finite depth. Thus recording "
                            + "a failed observation and recording a successful zero are "
                            + "different requirements."))),
                DescribeRole.Theorem))));
}
