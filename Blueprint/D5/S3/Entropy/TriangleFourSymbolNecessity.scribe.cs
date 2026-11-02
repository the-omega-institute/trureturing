using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class TriangleFourSymbolNecessityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Entropy/TriangleFourSymbolNecessity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common-record recovery from a finite original source law and incident stochastic kernels.",
        H("Original Triangle Law and Common-Record Recovery"),
        Blocks(
            Paragraph(Text(
                "The carrier retains arbitrary finite original source and output alphabets, "
                + "a nonnegative normalized real source law and three nonnegative normalized "
                + "incident kernels. It assumes neither independence nor full support. "
                + "The six-variable law is the source mass multiplied by the three response "
                + "probabilities. Agreement means that each off-diagonal cell has zero mass.")),
            Describe.Lean(
                DescribeId.Create("original-law-common-record-recoverability"),
                DeclarationHandle.Create(Module + "IncidentLaw.original_law_recoverability"),
                H("Agreement forces active response rows on the original alphabets"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At a positive source cell, positivity and agreement force the three "
                        + "response vectors to concentrate on one common symbol. A positive "
                        + "incident-pair marginal has a positive extension, so its fixed kernel "
                        + "row is this point mass. The selected incident maps agree on every "
                        + "positive source cell. The final identity includes every original "
                        + "record/source cell, including zero source cells.")),
                    Paragraph(Text(
                        "The maps select a positive coordinate of each original kernel row. "
                        + "Only rows with positive incident-pair marginal are forced to be "
                        + "point masses. Normalized inactive rows retain their original values."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The support-at-most-four necessity classification remains unproved here. "
                + "In particular, the KL equality has not yet been connected to pairwise "
                + "source independence and conditional three-source products, and no binary "
                + "block distributions or four-symbol output bijection have been constructed. "
                + "The converse and entropy formulas are also outside the proved statement.")))));
}
