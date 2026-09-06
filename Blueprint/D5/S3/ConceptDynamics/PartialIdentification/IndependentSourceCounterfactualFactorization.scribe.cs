using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class IndependentSourceCounterfactualFactorizationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/PartialIdentification/IndependentSourceCounterfactualFactorization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Elementary independent disturbances supply the block laws needed by the existing intervention-locality compiler, yielding counterfactual factorization on the original full source carrier.",
        H("Counterfactual factorization from independent disturbances"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("independent-source-pair-readout-eq-partitioned"),
                DeclarationHandle.Create(Prefix + "independentSource_pair_readout_eq_partitioned"),
                H("Identify direct and partitioned readout laws"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pushforward of the original independent source law equals the existing partitioned readout representation with block laws derived from the same elementary disturbances."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("independent-source-separated-readouts-factorize"),
                DeclarationHandle.Create(Prefix + "independentSource_separated_readouts_factorize"),
                H("Factorize separated readouts under the full law"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Disjoint semantic dependency supports give product response laws. Mutual elementary independence supplies the required block factorization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("independent-source-separated-readouts-cell-eq-product"),
                DeclarationHandle.Create(Prefix + "independentSource_separated_readouts_cell_eq_product"),
                H("Evaluate joint cells by actual marginals"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every joint response cell is the product of the actual marginals of the full-source pushforward. Boolean simultaneous benefit is the true,true cell."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compiled-counterfactual-events-independent-sources"),
                DeclarationHandle.Create(Prefix + "compiled_counterfactual_events_independent_sources"),
                H("Join structural evaluation to elementary disturbance laws"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing counterfactual support compiler and source-separation proof are reused unchanged. The theorem takes elementary laws directly, without a separately supplied block-law premise."))),
                DescribeRole.Theorem))));
}
