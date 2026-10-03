using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class GoldenCubicCompatibilityConjugacyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual compatibility automorphism has a two-element conjugacy class over the rationals.",
        H("Golden Cubic Compatibility Conjugacy"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-cubic-compatibility-conjugacy"),
            DeclarationHandle.Create(
                "D5/S3/Factorization/Galois/GoldenCubicCompatibilityConjugacy.actual_conjugacy_data"),
            H("Two rational conjugates and the Galois-group order"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For the actual radical and cyclotomic compositum, complex conjugation changes "
                    + "the selected automorphism on the real cube root of two. Automorphisms fixing "
                    + "the cubic cyclotomic base form an abelian subgroup of index two. Thus the "
                    + "rational conjugacy class consists of the selected automorphism and its "
                    + "distinct conjugate.")),
                Paragraph(Text(
                    "The class has size two. Linear disjointness of the actual radical and "
                    + "cyclotomic fields gives rational Galois-group order equal to the totient "
                    + "of the modulus times 3 to the power twice the earlier support size plus two."))),
            DescribeRole.Theorem))));
}
