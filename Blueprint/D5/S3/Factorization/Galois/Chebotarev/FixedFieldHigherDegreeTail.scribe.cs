using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois.Chebotarev;

internal sealed class FixedFieldHigherDegreeTailDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "the degree-≥ 2 part of T vanishes in the density ratio.",
        H("the degree-≥ 2 part of T vanishes in the density ratio"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-ideal-zeta-sum-t2-div-univ-tendsto-zero"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Galois/Chebotarev/FixedFieldHigherDegreeTail.primeIdealZetaSum_T2_div_univ_tendsto_zero"),
                H("the degree-≥ 2 part of T vanishes in the density ratio"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For T₂ defined as the fixed-field Frobenius set after removing degree-one primes " +
                    "over K unramified in L, the partial prime sum over T₂ divided by the universal " +
                    "prime sum over E tends to zero as s decreases to one from above. The higher-degree " +
                    "part is bounded above by a convergent square-power prime sum; primes lying above " +
                    "the finitely many ramified base primes contribute a finite remainder."))),
                DescribeRole.Theorem)
        )));
}
