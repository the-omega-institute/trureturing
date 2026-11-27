using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GLn.SchurModule;

internal sealed class WeightRepBasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weight Rep Basic", H("Weight Rep Basic"),
        Blocks(
            Paragraph(Text("Unitary groups acting on Weyl modules, invariant metric, extremal vector, Harish-Chandra parameter. Algebraic modular forms on the standard definite unitary group; p-adic gauge. Weight representation: base change, integrality, unitary invariance of the contravariant form.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GLn/SchurModule/WeightRepBasic.gramForm_conjWeylRep"),
                H("gramForm_conjWeylRep"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The Gram pairing on coordinate vectors of weight κ is invariant under the product of the compact groups U(n), acting in weight (κ, e).")))))));
}
