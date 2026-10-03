using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta.NumberField;

internal sealed class ZetaProductFibreDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The L2 count as a sum of norm-residue counts.",
        H("The L2 count as a sum of norm-residue counts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("is-bad-part"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/ZetaProductFibre.IsBadPart"),
                H("Is Bad Part"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The \"bad-supported\" ideals of norm ≤ N: nonzero, with every prime factor unramified " +
                    "in L and of norm not coprime to m."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bad-finset"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/ZetaProductFibre.badFinset"),
                H("bad Finset"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Ideals supported on unramified primes whose norm is not coprime to m, bounded by N."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("card-l2-eq-sum-residue"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Zeta/NumberField/ZetaProductFibre.card_L2_eq_sum_residue"),
                H("The L2 count as a sum of norm-residue counts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The L2 count as a sum of norm-residue counts. Chaining the finite bad-part partition, " +
                    "the per-bad-part bijection (card_fibre_eq_card_good_fibre), and the good- " +
                    "fibre↔residue dictionary (card_good_fibre_eq_card_residue): the L2 fibre count at g " +
                    "is the sum over the finite bad-part set of the norm-residue counts of modulus m at " +
                    "residue autToPow (g · Frob(𝔟)⁻¹), each up to norm ⌊N / N𝔟⌋."))),
                DescribeRole.Theorem)
        )));
}
