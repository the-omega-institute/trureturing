using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class ComplementFibersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Spacetime/ComplementFibers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced finite histories occupy opposite readout fibers, and scalar sections lose history.",
        H("Opposite Fibers and Scalar Sections"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("representative-complement-opposite-fiber"),
                DeclarationHandle.Create(Prefix + "representative_complement_mem_oppositeFiber"),
                H("Canonical complements lie in the opposite readout fiber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The actual canonical archive is balanced, so the B1 complement theorem places "
                        + "its context-preserving event complement in the numerical opposite fiber, for every d."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-full-opposite-fiber-members"),
                DeclarationHandle.Create(Prefix + "empty_full_fiber_members_distinct"),
                H("A nonempty balanced context has distinct empty and full fiber members"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Balance makes the empty and full selections both read zero, hence both belong to "
                        + "Opp(empty). Nonemptiness of the current region proves the two dependent selections "
                        + "are distinct."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("canonical-balanced-section"),
                DeclarationHandle.Create(Prefix + "balancedSection_rightInverse"),
                H("The exact integer representatives form a scalar right inverse"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The section is the balanced wrapper around the literal representative archive. Its "
                        + "readout is n by the canonical representative theorem, so it is a right inverse "
                        + "of scalar readout on BalancedRich d for every d, including the source d=3."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("section-lift-square-on-readout"),
                DeclarationHandle.Create(Prefix + "sectionLift_square_readout"),
                H("Every scalar right inverse has the frozen lift-square law"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any dimension d and any section s into BalancedRich d, applying the exact "
                        + "frozen sectionLift_square theorem to L(X)=s(-q(X)) gives "
                        + "L squared equal to s composed with q. The companion involutivity criterion is "
                        + "a direct application of frozen sectionLift_involutive_iff_leftInverse in every d."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("scalar-readout-loses-history"),
                DeclarationHandle.Create(Prefix + "scalar_recovery_refuted"),
                H("No scalar section recovers every balanced history"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty canonical zero history and the empty selection in the one-event-pair "
                        + "canonical context are distinct balanced rich histories with equal readout zero. "
                        + "The general witness compares archive cardinalities zero and two in every d. "
                        + "The closed scalar recovery claim concerns BalancedRich 3; its negation uses "
                        + "these actual histories at d=3. The general section is not a left inverse, and "
                        + "its complement lift is not involutive."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/ComplementCharge")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Negation/ComplementFiberLift")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/Spacetime/IntegerRepresentatives"))
        ]));
}
