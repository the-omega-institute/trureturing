using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois.Chebotarev;

internal sealed class CyclotomicNormResidueDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Frobenii of coprime-norm primes generate the Galois group.",
        H("Frobenii of coprime-norm primes generate the Galois group"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("subgroup-eq-top-of-forall-frobenius-mem-of-coprime"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Galois/Chebotarev/CyclotomicNormResidue.subgroup_eq_top_of_forall_frobenius_mem_of_coprime"),
                H("Frobenii of coprime-norm primes generate the Galois group"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Frobenii of coprime-norm primes generate the Galois group (abelian case). A subgroup " +
                    "of Gal(L/K) containing the Frobenius representative of every nonzero prime of K that " +
                    "is unramified in L and has norm coprime to m is all of Gal(L/K). The κ-uniformity " +
                    "realization in ZetaProduct.lean uses this theorem for residues arising from coprime- " +
                    "norm ideal Frobenius values."))),
                DescribeRole.Theorem)
        )));
}
