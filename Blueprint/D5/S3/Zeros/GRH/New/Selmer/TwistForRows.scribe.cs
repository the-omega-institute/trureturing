using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class TwistForRowsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Twist For Rows", H("Twist For Rows"),
        Blocks(
            Paragraph(Text("One anticyclotomic twist makes all Selmer groups short. For finitely many irreducible blocks of Galois representations of lifts, one finite-order anticyclotomic twist ramified at new primes makes, for each of its first m powers, all Selmer groups modulo a given power of ℓ short and the ratios of twisted to untwisted Hecke values barely divisible by ℓ, which limits congruences. Twists of ℓ-power order at new primes that kill a Selmer group or keep L-values barely divisible are known. Related work: Mazur–Rubin, Diophantine stability, 2018; Kriz–Nordentoft, Horizontal p-adic L-functions, 2023; Hida, Non-vanishing modulo p of Hecke L-values, 2004.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/TwistForRows.exists_mFoldTwist_selmerLengthLe"),
                H("exists_mFoldTwist_selmerLengthLe"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For finitely many rows R_i and M, some m-fold twist has, for its first m powers ϑ, ψ the avatar of ϑ⁻¹: Q auxiliary, ψ anticyclotomic, Σ v(ψ(γ) − 1) ≤ cr_ℓ over tame generators γ at Q, Selmer length of ψR_i mod ℓ^M ≤ (10f·rank + 1)cr_ℓ, v(ιρ_p(ϑ^{±1})) ≤ 9cr_ℓ for ramified p. Here cr_ℓ = crudeUnit and ρ_p = Data.Pair.ratio p.")))))));
}
