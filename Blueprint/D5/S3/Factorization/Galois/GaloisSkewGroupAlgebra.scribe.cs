using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class GaloisSkewGroupAlgebraDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/conradgaloisdescent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The skew algebra of a finite Galois group is canonically the full linear endomorphism algebra of the field.",
        H("The Galois Skew-Group Algebra"),
        Blocks(Describe.Lean(
            DescribeId.Create("galois-skew-group-canonical-equivalence"),
            DeclarationHandle.Create(
                "D5/S3/Factorization/Galois/GaloisSkewGroupAlgebra.canonical_equivalence"),
            H("The canonical action is an algebra equivalence"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text(
                    "Let K and L be fields with a K-algebra structure on L. Let a finite group G "
                    + "act on L through a multiplicative semiring action, and assume IsGaloisGroup G K L. "
                    + "This states that the action is faithful and its fixed field is the image of K; "
                    + "commutation with the K-scalars follows from the same class.")),
                Paragraph(Text(
                    "A single term a[g] acts on x in L as a times g acting on x. The multiplication "
                    + "rule a[g] times b[h] equals a times g acting on b, in degree gh. "
                    + "The resulting map skewAction from SkewMonoidAlgebra L G to Module.End K L "
                    + "is a K-algebra homomorphism, where multiplication of endomorphisms is composition "
                    + "with the right factor applied first.")),
                Paragraph(Text(
                    "Distinct field automorphisms are linearly independent over L by Artin independence. "
                    + "Therefore equality of the induced endomorphisms recovers every coefficient of "
                    + "a skew-algebra element. Writing n for the degree of L over K, the Galois-group "
                    + "hypothesis gives finite dimensionality and cardinality G equal to n. "
                    + "The skew algebra and the endomorphism algebra both have K-dimension n squared. "
                    + "The injective canonical action is consequently surjective and defines equiv K L G.")),
                Paragraph(Text(
                    "The theorem supplies an algebra equivalence whose underlying homomorphism is "
                    + "skewAction and proves the single-term action formula for every g, a and x. "
                    + "This is the classical Galois skew-algebra bridge. Semilinear descent and "
                    + "matrix descriptions of larger orbit blocks require further hypotheses and arguments."))),
            DescribeRole.Theorem))));
}
