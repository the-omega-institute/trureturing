using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class DegreeBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Degree Bounds", H("Degree Bounds"),
        Blocks(
            Paragraph(Text("Last step: pairing on the top group is a multiple of the branching restriction. Bounds on the Bessel degree of the filling and on the number of Bessel coordinates.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/DegreeBounds.log_filling_besselDegree_mem_Icc"),
                H("log_filling_besselDegree_mem_Icc"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("With deg the degree Filling.besselDegree of Data.filling and w = Data.nominalWeight, the number log deg + f Σ_{k−1 ≤ l < r} log l! lies between m(k−1) Σ_v log w(v) and mr Σ_v (log w(v) + 1/x), v over the f infinite places.")))))));
}
