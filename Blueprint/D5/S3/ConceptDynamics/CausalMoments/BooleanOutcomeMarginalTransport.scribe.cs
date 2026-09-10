using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.CausalMoments;

internal sealed class BooleanOutcomeMarginalTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/CausalMoments/BooleanOutcomeMarginalTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite rational nonfair outcome transport on the original complete-mediation model.",
        H("BooleanOutcomeMarginalTransport"),
        Blocks(
            Paragraph(Text("All theorem entries are bound to their Lean declarations without formula projection. The original mediator and outcome probability-law semantics are retained. No compilation or independent review status is asserted by this source document.")),
            Describe.Lean(DescribeId.Create("tablemean"),
                DeclarationHandle.Create(Prefix + "tableMean"), H("Actual outcome coordinate mean"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The readout is the original finite-law success expectation, with the complete response table retained."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tablemean-mem"),
                DeclarationHandle.Create(Prefix + "tableMean_mem"), H("Every coordinate mean is a probability"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nonnegative normalized original weights imply zero-to-one bounds, including deterministic coordinates."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bittransition"),
                DeclarationHandle.Create(Prefix + "bitTransition"), H("Monotone Bernoulli transition rates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The upward branch flips original zero bits; the downward branch thins original one bits. The unused branch remains defined at source mean zero or one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exists-exact-marginal-transport"),
                DeclarationHandle.Create(Prefix + "exists_exact_marginal_transport"), H("Preserve the original law and attain every minimum mismatch"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One joint old/new table law preserves every original-table expectation, realizes all target means, and has coordinate mismatch exactly the absolute mean difference. Original outcome coordinates need not be independent. The auxiliary table is independent of the whole original law."))), DescribeRole.Theorem))));
}
