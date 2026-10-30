using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class CoprimeNormalFormDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ExponentExchange/CoprimeNormalForm.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coprime residual admits an ordered prime-exponent representative with no smaller normalized divisor sum.",
        H("Coprime prime-exponent normal form"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coprime-allowed-ordered-definition"),
                DeclarationHandle.Create(Prefix + "AllowedOrdered"),
                H("Allowed ordered residuals"),
                StatementSource.FromAuthor(Disp(F.Id("AllowedOrdered"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "AllowedOrdered M m requires that, for every pair of distinct primes p<q "
                        + "coprime to M, the q-exponent of m is at most its p-exponent."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("coprime-allowed-ordered-form"),
                DeclarationHandle.Create(Prefix + "exists_coprime_allowed_ordered_form"),
                H("Ordered representative of a coprime integer"),
                StatementSource.FromAuthor(Disp(F.Id("existsCoprimeAllowedOrderedForm"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every positive n coprime to M has a positive m≤n that remains coprime to M, "
                        + "satisfies AllowedOrdered M m, and has normalized divisor sum at least "
                        + "that of n. The proof repeatedly swaps an inverted pair of prime exponents."))),
                DescribeRole.Theorem))));
}
