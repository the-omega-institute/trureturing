using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class LinesStepDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lines Step", H("Lines Step"),
        Blocks(
            Paragraph(Text("Support of unfolded periods: lattice lines move at most one step per lift.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/LinesStep.step"),
                H("step"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("One step of Grading.HasNearLines: from Y, x, m, k to Y', x', m', k + 1, where s' + 1 = s and m = m' (s odd) or m' + 1 (s even). Assume (c) = (aā), b | conj(α/a)∏_Q w, ϱ_f(b·Ô-vectors) fixes f, Grading.constTermAtT of t ⊗ f is non-zero at (x, x'), and adapted bases at x' have ord_w β_i + ord_{w̄} β_{s'−1−i} ≥ 0. Here c is the constant of the grading Y and α = WeilData.α.")))))));
}
