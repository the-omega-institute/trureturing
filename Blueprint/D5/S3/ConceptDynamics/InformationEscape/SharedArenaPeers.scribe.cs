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
            Paragraph(Text("The intervention catalog contains four new peers and its gold shadow; the observation-intervention catalog contains one new peer and its gold shadow. Each occurrence uses exactly the two finite readouts of its declared law. No anchors, carrier copies, or theorem-truth readouts enter the bundles.")),
            Node("finite-intervention-arena", "finiteInterventionArena", "Finite intervention object arena",
                "The intervention registrations enumerate the finite SCM object arena used by their declared readouts.", DescribeRole.Definition),
            Node("finite-intervention-law-arena", "finiteInterventionLawArena", "Finite intervention law arena",
                "The homogeneous finite signature turns intervention and counterfactual codes into the separation law.", DescribeRole.Definition),
            Node("finite-observation-arena", "finiteObservationInterventionArena", "Finite observation object arena",
                "The observation-intervention registrations enumerate the finite directional SCM object arena.", DescribeRole.Definition),
            Node("finite-observation-law-arena", "finiteObservationInterventionLawArena", "Finite observation law arena",
                "The same homogeneous signature records observation and intervention code separation.", DescribeRole.Definition),
            Node("intervention-codes", "icIntCode", "Intervention code readouts",
                "Marginal and counterfactual outcome tables are encoded as the two public finite readout functions.", DescribeRole.Definition),
            Node("counterfactual-code", "icCFCode", "Counterfactual code readout",
                "The joint outcome table supplies the second intervention readout.", DescribeRole.Definition),
            Node("observation-code", "oiObsCode", "Observation code readout",
                "The observation code branches on the direction field and projects the root and child fields.", DescribeRole.Definition),
            Node("oi-intervention-code", "oiIntCode", "Intervention code readout",
                "The intervention code branches on the direction field and projects the corresponding causal field.", DescribeRole.Definition),
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
            Paragraph(Text("The maximal seal succeeds on both complete catalogs with a redundant verdict: every occurrence is certified trivial in its catalog and carries one finite IE-C007 zero-unique-capture record (intervention full 0 and without 0; observation-intervention full 24 and without 24). Each catalog publishes a redundancy certificate, no occurrence receives positive admission, system irredundancy is refuted for this root, and the census query certifies triviality for all seven occurrences.")))));

    private static DocumentBlock.Describe Node(
        string id, string declaration, string title, string explanation,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);
}
