using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Fock;

internal sealed class MixedFockModelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mixed Fock Model", H("Mixed Fock Model"),
        Blocks(
            Paragraph(Text("Weighted moments on Fock data; polynomial vectors dense in all moment norms. Mixed Schrödinger–Fock model; rapid decay of mixed functions in weighted moment norms.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Fock/MixedFockModel.isRapidDatum_slice"),
                H("isRapidDatum_slice"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("In a mixed model, if all weighted norms mom_N(v) are finite, then so are those of v[a] for every point a.")))))));
}
