using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.LinearAlgebra;

internal sealed class PartialDerivCommDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial Deriv Comm", H("Partial Deriv Comm"),
        Blocks(
            Paragraph(Text("Characteristic polynomials over a subring pass from spanning elements to the whole algebra. Abstract Hecke operators, level eigenspaces, weighted class sums, indices of compact open subgroups. Jacobi's formula: derivative of the determinant at the identity is the trace.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/PartialDerivComm.hasDerivAt_det"),
                H("hasDerivAt_det"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Jacobi's formula at the identity: if a curve γ of complex n×n matrices has γ(s) = 1 and derivative Y at s, then t ↦ det γ(t) has derivative tr Y at s.")))))));
}
