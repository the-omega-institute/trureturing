using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.StrongSubadditivity;

internal sealed class MarkovConstructorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All states use the canonical finite density-state interface on A times (B times C). Conditional mutual information is the ordinary entropy expression evaluated on the four actual marginals. Product and orthogonal pointer constructions have zero conditional mutual information for all ranks, including zero mixture weights.",
        H("Physical quantum Markov constructors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("qcmi-eq-four-marginals"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.qcmi_eq_four_marginals"),
                H("The four actual marginal entropies"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Ordinary qcmi of the canonical state converted to MState equals the entropy of its actual AB marginal plus the entropy of its actual BC marginal minus the entropy of its actual B marginal and the entropy of the state itself."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("qcmi-product-left"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.qcmi_product_left"),
                H("A product across A and BC"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every density state a on A and every density state omega on B times C, the physical product a tensor omega has ordinary conditional mutual information zero. Product entropy additivity applies without a rank condition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("qcmi-product-right"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.qcmi_product_right"),
                H("A product across AB and C"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every density state P on A times B and every density state gamma on C, relabeling P tensor gamma onto A times (B times C) gives ordinary conditional mutual information zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("classicalmarkovstate"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.classicalMarkovState"),
                H("An orthogonal pointer state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A probability vector on B and normalized conditional states alpha(j) on A and gamma(j) on C define the mixture of alpha(j) tensor the computational pointer j tensor gamma(j). Zero weights do not require division."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("qcmi-classicalmarkovstate"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors.qcmi_classicalMarkovState"),
                H("Conditional independence in every pointer block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The orthogonal pointer mixture has ordinary conditional mutual information zero. Each of its four actual marginal entropies is evaluated using product additivity and the orthogonal record entropy formula; the classical entropy and both conditional entropy sums cancel."))),
                DescribeRole.Theorem))));
}
