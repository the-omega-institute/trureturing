using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class SeparatedCounterfactualSourceFactorizationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/PartialIdentification/SeparatedCounterfactualSourceFactorization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Intervention-specific dependency certificates discharge the coordinatewise-map premise of finite product pushforward. Independent source blocks retain arbitrary internal coupling.",
        H("Counterfactual source separation and product laws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("partitioned-readout-law"),
                DeclarationHandle.Create(Prefix + "partitionedReadoutLaw"),
                H("Partition the full source carrier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Mathlib piEquivPiSubtypeProd recoordinates every original source assignment into a supported block and its complement. The readouts themselves remain the original full-source functions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("separated-readouts-factorize"),
                DeclarationHandle.Create(Prefix + "separated_readouts_factorize"),
                H("Obtain product response laws from disjoint supports"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("DependsOn gives reduced maps through coordinate restriction. Disjoint support puts the right map in the complement block, allowing reuse of the existing product-pushforward theorem. Independence inside either block is unnecessary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("separated-readouts-cell-eq-product"),
                DeclarationHandle.Create(Prefix + "separated_readouts_cell_eq_product"),
                H("Evaluate joint cells from the actual marginals"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every joint response cell equals the product of its actual marginal masses. At the Boolean cell true,true this is the joint-benefit formula. It is a probability-evaluation corollary of the preceding factorization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compiled-counterfactual-events-factorize"),
                DeclarationHandle.Create(Prefix + "compiled_counterfactual_events_factorize"),
                H("Connect structural evaluation to cross-world factorization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proof combines parent-indexed structural semantics, local exogenous contracts, compiled support descent, support disjointness, and an explicit independent block law. A c-component label alone supplies none of the required event-locality evidence."))),
                DescribeRole.Theorem))));
}
