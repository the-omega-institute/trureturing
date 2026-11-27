using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Algebra;

internal sealed class SuccessiveApproxDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Successive Approx", H("Successive Approx"),
        Blocks(
            Paragraph(Text("Successive approximation in adically complete modules; extracting the largest power of an element.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Algebra/SuccessiveApprox.mem_range_of_approx"),
                H("mem_range_of_approx"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Successive approximation: let shiftDiff be surjective for π on N and injective for π' on M, and f: N → M additive with f(πn) = π'f(n). If a set S ⊂ M lies in f(N) + π'S, then S lies in f(N).")))))));
}
