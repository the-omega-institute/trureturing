using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class FiniteConditionalResponseTableDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/PartialIdentification/FiniteConditionalResponseTable.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Existence quantifies over one pair of complete disturbances, rather than separate models for each stratum.",
        H("One common-source realization for all strata"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("table-evaluation-law"),
                DeclarationHandle.Create(Prefix + "tableEvaluationLaw"),
                H("A row distribution from a fixed table"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Push a complete response-table law through evaluation at one covariate value."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("table-evaluation-law-independent-source"),
                DeclarationHandle.Create(Prefix + "tableEvaluationLaw_independentSource"),
                H("All row marginals in one disturbance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product law on full tables reproduces every prescribed row law. Dependence among coordinates inside a response value is unrestricted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-conditional-table-realization"),
                DeclarationHandle.Create(Prefix + "finite_conditional_table_realization"),
                H("Simultaneous finite conditional representation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One normalized rational table law realizes the entire conditional response family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-noise-pair-model"),
                DeclarationHandle.Create(Prefix + "FixedNoisePairModel"),
                H("Two complete response mechanisms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each mechanism has one law on complete tables. The model class permits arbitrary dependence between different rows."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fixed-noise-source-law"),
                DeclarationHandle.Create(Prefix + "fixedNoiseSourceLaw"),
                H("Independent covariate and mechanism disturbances"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The common source law is the product of the covariate root law and the two full-table laws."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("selected-pair-law"),
                DeclarationHandle.Create(Prefix + "selectedPairLaw"),
                H("Read the same stratum from both tables"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A deterministic map selects each mechanism response at the common covariate value."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("selected-pair-law-mass"),
                DeclarationHandle.Create(Prefix + "selectedPairLaw_mass"),
                H("Exact selected response law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each joint cell equals the covariate mass times the two actual row marginal masses. This division-free statement includes zero-weight strata."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("canonical-fixed-noise-pair"),
                DeclarationHandle.Create(Prefix + "canonicalFixedNoisePair"),
                H("Canonical simultaneous witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Independent rows construct one attaining table per mechanism. Row independence is a choice of witness and is not imposed on the general model class."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("canonical-fixed-noise-pair-selected-mass"),
                DeclarationHandle.Create(Prefix + "canonicalFixedNoisePair_selected_mass"),
                H("Realize every specified conditional cell"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The canonical fixed-noise model reproduces both conditional response kernels at every covariate value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("simultaneous-conditional-product-realization"),
                DeclarationHandle.Create(Prefix + "simultaneous_conditional_product_realization"),
                H("One common-source realization for all strata"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Existence quantifies over one pair of complete disturbances, rather than separate models for each stratum."))),
                DescribeRole.Theorem))));
}
