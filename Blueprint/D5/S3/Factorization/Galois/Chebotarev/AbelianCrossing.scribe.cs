using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois.Chebotarev;

internal sealed class AbelianCrossingDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/cbirkbeck2026chebotarev");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Abelian Crossing.",
        H("Abelian Crossing"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("liminf-density-s-sigma-ge-card-h-n-div-g-h"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Galois/Chebotarev/AbelianCrossing.liminf_density_S_sigma_ge_card_H_n_div_GH"),
                H("Abelian Crossing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Sharifi 7.2.2 Step 2 — partial lower bound on δ_inf(S_σ) coming from one cyclotomic " +
                    "crossing modulus m: |H_n(m)|/(|G|·|H(m)|) bounds the liminf of the density ratio for " +
                    "S_σ in K. Source quote (p. 144): \"δ_inf(S_σ) ≥ |H_n|/(|G|·|H|)\". The crossing is only " +
                    "valid at *admissible* m, so this per-m bound carries the same two hypotheses as " +
                    "exists_cyclotomicCrossing_fibres: hm4 : m % 4 ≠ 2 (feeding the cyclotomic case) and " +
                    "hcop : ((NumberField.discr L).natAbs).Coprime m (the linear-disjointness via the " +
                    "everywhere-unramified intersection / discr_dvd_discr)."))),
                DescribeRole.Theorem)
        )));
}
