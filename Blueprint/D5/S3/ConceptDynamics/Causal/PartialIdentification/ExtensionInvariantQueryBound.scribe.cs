using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class ExtensionInvariantQueryBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/ExtensionInvariantQueryBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equivariant relabelings of finite response-signature programs preserve feasibility, event values, and the complete identified set.",
        H("Extension-Invariant Causal Query Bounds"),
        Blocks(
            Paragraph(Text(
                "Two compatible total orders can use different response-signature carriers. Order invariance requires a carrier equivalence that preserves every observational constraint row, its right-hand side, and the Boolean counterfactual query evaluation.")),
            Paragraph(Text(
                "Mass is transported by composing with the inverse signature equivalence. Finite-sum reindexing proves preservation of event objectives and every constraint value.")),
            Paragraph(Text(
                "The resulting theorem identifies the exact proof payload needed to justify total-order invariance. Merely knowing that both orders extend the same partial order does not discharge row and query equivariance.")),
            Describe.Lean(
                DescribeId.Create("signature-event-mass-relabel"),
                DeclarationHandle.Create(Prefix + "signatureEventMass_relabel"),
                H("Query event mass is invariant under preserving signature relabeling"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An equivalence reindexes the finite signature sum, while preservation of the Boolean event makes each transported term equal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("feasible-relabel-iff"),
                DeclarationHandle.Create(Prefix + "feasible_relabel_iff"),
                H("Equivariant response-signature relabeling preserves feasibility"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every compiled constraint row has the same finite sum after relabeling, and the right-hand sides agree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("identified-set-invariant-under-signature-equivalence"),
                DeclarationHandle.Create(Prefix + "identified_set_invariant_under_signature_equivalence"),
                H("Preserving signature equivalences give identical identified sets"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Forward and inverse mass transports map every feasible witness at a target value to a feasible witness for the other order at the same value."))),
                DescribeRole.Theorem))));
}
