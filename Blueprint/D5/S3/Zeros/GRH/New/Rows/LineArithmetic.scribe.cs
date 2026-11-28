using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class LineArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Line Arithmetic", H("Line Arithmetic"),
        Blocks(
            Paragraph(Text("Coefficient vectors are integral off the conductor and small when untwisted.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/LineArithmetic.lineMultiplier_integral_and_small"),
                H("lineMultiplier_integral_and_small"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("One c ≠ 0, depending on j, makes every y = conj(c·Data.lineMultiplier ϑ j i h) integral at h (weylGauge ≤ 1) for all ι: ℂ → ℂ_p, p prime to N(Q); if Q = ∅, all Aut(ℂ)-conjugates have squared norm ≤ exp(rB₀).")))))));
}
