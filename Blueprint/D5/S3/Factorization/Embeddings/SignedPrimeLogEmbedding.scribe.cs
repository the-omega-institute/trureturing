using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Embeddings;

internal sealed class SignedPrimeLogEmbeddingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical rational logarithmic length faithfully embeds signed prime ledgers.",
        H("Faithfulness of Signed Prime Logarithmic Length"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rational-logarithmic-length-is-injective"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Embeddings/SignedPrimeLogEmbedding.rational_log_length_injective"),
                H("Rational logarithmic length is injective"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("Injective")), Open,
                    F.Id("rationalLogLength"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The canonical logarithmic length distinguishes any two finite signed prime "
                        + "exponent ledgers. Thus the real-valued interface retains the complete ledger "
                        + "rather than only an additive summary.")),
                    Paragraph(Text(
                        "Both positive-rational representatives are strictly positive, so injectivity "
                        + "of the real logarithm identifies their real values. Injectivity of the "
                        + "rational and unit coercions then identifies the positive rationals, and the "
                        + "existing prime-exponent equivalence recovers the original ledgers.")),
                    Paragraph(Text(
                        "This repository-derived consequence uses the canonical positive-rational "
                        + "interface directly. It is adjacent to integer linear independence of prime "
                        + "logarithms but does not restate or reprove that separate theorem."))),
                DescribeRole.Theorem))));
}
