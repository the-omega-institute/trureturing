using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.Crystalline;

internal sealed class PeriodLiftingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Period Lifting", H("Period Lifting"),
        Blocks(
            Paragraph(Text("Basis of the envelope; gamma-1 is onto with constant invariants (crystalline Poincare lemma). Almost comparison modulo p lifts to completed Witt coefficients after inverting tau.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/Crystalline/PeriodLifting.periodAlg_of_almostCoeff"),
                H("periodAlg_of_almostCoeff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let IsPeriodRingPair hold for S, K with K flat over S; N has flat base change, N' for K ⊗_S G(ψ'); ψ, ψ' take values b in IsPerfectTorsionFree. A comparison bijective for b ⊗ (O^♭ ⊗_{A_inf} S) ⊗ 𝔪 is bijective for K ⊗_S (S ⊗ W(b))^, p-adic completion.")))))));
}
