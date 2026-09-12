using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscape;

internal sealed class SharedArenaPeersDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscape/SharedArenaPeers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five frozen causal peers reuse the separation template on two existing canonical arenas.",
        H("Shared Canonical Arena Peers"),
        Blocks(
            Paragraph(Text("The intervention catalog contains four new peers and its gold shadow; the observation-intervention catalog contains one new peer and its gold shadow. Each occurrence uses exactly the two readouts of the canonical law. No anchors, carrier copies, or theorem-truth readouts enter the bundles.")),
            Node("intervention-catalog", "interventionCatalog", "Five intervention occurrences",
                "The catalog uses FourthFifthArenas.interventionArena and its complete registry vector.", DescribeRole.Definition),
            Node("observation-catalog", "observationCatalog", "Two observation-intervention occurrences",
                "The catalog uses ObservationIntervention.observationInterventionArena and its complete registry vector.", DescribeRole.Definition),
            Node("finer-bridge", "finer_bridge", "Counterfactual kernel strictness",
                "The collapse identity supplies inclusion; the remaining law is separation."),
            Node("fiber-bridge", "fiber_bridge", "Variation on a coupling fiber",
                "Introducing or eliminating the common marginal label preserves the separation law."),
            Node("identifiability-bridge", "not_identifiable_bridge", "Failure of identifiability",
                "The factorization criterion converts failure of identifiability into a separated pair."),
            Node("target-bridge", "target_bridge", "Target-relative sufficiency",
                "Universal sufficiency factorization identifies the failed counterfactual upgrade."),
            Node("profile-bridge", "profile_bridge", "Full intervention profile strictness",
                "The null-action coordinate supplies observational inclusion; strictness supplies separation."),
            Node("intervention-sensitive", "intervention_law_sensitive", "Intervention law sensitivity",
                "The actual realization satisfies the law and a constant realization of the same signature fails it."),
            Node("observation-sensitive", "observation_law_sensitive", "Observation law sensitivity",
                "The actual realization satisfies the law and a constant realization of the same signature fails it."),
            Node("intervention-before", "intervention_before_peers", "Intervention capture before peers",
                "Each occurrence alone captures 240 ordered state pairs; this measurement registers and seals no singleton."),
            Node("observation-before", "observation_before_peers", "Observation capture before peers",
                "Each occurrence alone captures 968 ordered state pairs; this measurement registers and seals no singleton."),
            Node("all-trivial", "all_peers_trivial", "All occurrences are trivial in their shared catalogs",
                "Every occurrence has zero unique capture because a real peer has the same agreement kernel."),
            Node("no-lowering", "no_peer_lowers_escape", "No occurrence lowers shared escape",
                "Nondegeneracy turns empty unique capture into failure of LowersEscape for all seven occurrences."),
            Paragraph(Text("The maximal seal succeeds on both complete catalogs with a redundant verdict: every occurrence is certified trivial in its catalog and carries one finite IE-C007 zero-unique-capture record (intervention full 0 and without 0; observation-intervention full 24 and without 24). Each catalog publishes a redundancy certificate, no occurrence receives positive admission, system irredundancy is refuted for this root, and the census query certifies triviality for all seven occurrences.")))));

    private static DocumentBlock.Describe Node(
        string id, string declaration, string title, string explanation,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);
}
