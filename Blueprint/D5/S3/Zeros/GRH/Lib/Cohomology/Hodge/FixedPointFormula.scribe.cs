using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Hodge;

internal sealed class FixedPointFormulaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed Point Formula", H("Fixed Point Formula"),
        Blocks(
            Paragraph(Text("Pull-back of the diagonal class is a weighted sum of point classes.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Hodge/FixedPointFormula.pointClass_eq_of_functions_eq"),
                H("pointClass_eq_of_functions_eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If X has an atlas of dimension d and the k-points z, z' take the same value under every map from X to the affine line, then cl(z) = cl(z') in Hdg^d(X).")))))));
}
