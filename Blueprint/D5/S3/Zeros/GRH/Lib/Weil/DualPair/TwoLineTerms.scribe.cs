using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.DualPair;

internal sealed class TwoLineTermsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two Line Terms", H("Two Line Terms"),
        Blocks(
            Paragraph(Text("Rules for theta kernels with data mod m: twists, level action, sums, conjugation. Two mixed models along isotropic lines: Levi action and Poisson equality of sums.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/DualPair/TwoLineTerms.tsum_lineTerm"),
                H("tsum_lineTerm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Poisson summation: the sums over ξ in E of θ of the terms lineTerm agree in both models. Each model is the mixed Schrödinger model of one splitting of Hom(W',V') over Hom(W,V) with explicit frames, adapted when A and X are.")))))));
}
