using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois.Chebotarev;

internal sealed class FrobeniusDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frobenius.",
        H("Frobenius"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unramified-in"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Galois/Chebotarev/Frobenius.UnramifiedIn"),
                H("Unramified In"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A prime of 𝓞 K is unramified in L if it is nonzero and every maximal prime above it " +
                    "is unramified over 𝓞 K."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("frobenius-class"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Galois/Chebotarev/Frobenius.frobeniusClass"),
                H("frobenius Class"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Frobenius conjugacy class of a prime, with the trivial class as a default value."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("exists-prime-dvd-nat-cast-mem"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Galois/Chebotarev/Frobenius.exists_prime_dvd_natCast_mem"),
                H("Frobenius"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A prime ideal containing (n : 𝓞 K) for 1 < n contains a prime factor of n."))),
                DescribeRole.Theorem)
        )));
}
