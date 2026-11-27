using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GLn.SchurModule;

internal sealed class NablaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nabla", H("Nabla"),
        Blocks(
            Paragraph(Text("Basic API: Borel semi-invariant polynomials, substitution, Fischer product, base change.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GLn/SchurModule/Nabla.diagramWeight_add"),
                H("diagramWeight_add"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For fixed bounds N, the weight diagramWeight is additive in the column multiplicities: the weight of κ + κ' is the sum of the weights of κ and κ'.")))))));
}
