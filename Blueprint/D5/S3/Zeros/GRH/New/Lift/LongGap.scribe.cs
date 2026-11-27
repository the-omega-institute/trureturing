using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Lift;

internal sealed class LongGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Long Gap", H("Long Gap"),
        Blocks(
            Paragraph(Text("Points, strictness, safe pairs and the walk along Frobenius orbits killing cup products. Gap step: an explicit power kills cup products absent small negative weights. Long gap lemma: a deep point from one coefficient of the E-expansion.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Lift/LongGap.pointsOver_nonempty_of_long_gap"),
                H("pointsOver_nonempty_of_long_gap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Long gap, unramified chart, l > 0: if p^κ kills l letters before i, E^s kills at i, the jumps between are ≤ g, N = s + gΣ_{t<l} p^t < A ≤ p^l δ, 3 ≤ p^l, then a point over p^{κ+4δ}c has exponents min(A, −u−N), depth A at E, both standard elsewhere.")))))));
}
