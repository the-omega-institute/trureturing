using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Embeddings;

internal sealed class SignedPrimeLogDensityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical rational logarithmic length is dense in the real line.",
        H("Density of Signed Prime Logarithmic Length"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rational-logarithmic-length-has-dense-range"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Embeddings/SignedPrimeLogDensity.rational_log_length_dense"),
                H("Rational logarithmic length has dense range"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("DenseRange")), Open,
                    F.Id("rationalLogLength"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The canonical logarithmic lengths of finite signed prime exponent "
                        + "ledgers form a dense subset of the real line. Equivalently, every "
                        + "nonempty real open interval contains the logarithmic length of a "
                        + "signed prime ledger.")),
                    Paragraph(Text(
                        "Exponentiation sends the endpoints of any such interval to two "
                        + "strictly ordered positive reals. A rational between those values "
                        + "is positive, hence defines a unit of the nonnegative rationals and "
                        + "therefore a signed prime ledger through the existing equivalence. "
                        + "The logarithm and exponential order equivalences return its length "
                        + "to the original interval.")),
                    Paragraph(Text(
                        "This repository-derived consequence reuses the canonical "
                        + "positive-rational interface. Pinned Mathlib supplies rational "
                        + "density through exists_rat_btwn, interval density through "
                        + "dense_of_exists_between, and the strict logarithm-exponential "
                        + "order equivalences used for both endpoint bounds."))),
                DescribeRole.Theorem))));
}
