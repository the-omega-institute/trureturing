using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimeIdeals.NormResidue;

internal sealed class IdealCongruenceCountDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourier decay from realized residues.",
        H("Fourier decay from realized residues"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tendsto-sum-char-mul-card-norm-le-residue-div-of-realized"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCount.tendsto_sum_char_mul_cardNormLeResidue_div_of_realized"),
                H("Fourier decay from realized residues"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Fourier decay from realized residues. Let S ≤ (ℤ/c)ˣ be a subgroup all of whose " +
                    "elements are realized as ideal-norm residues (hS). Then for every nontrivial " +
                    "character χ of S, the χ-twisted norm-residue count average over S tends to 0: (∑_{s ∈ " +
                    "S} χ(s)·#{N(I) ≤ N, N(I) ≡ s}) / N → 0."))),
                DescribeRole.Theorem)
        )));
}
