using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.CuspForms;

internal sealed class WeightParameterDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weight Parameter", H("Weight Parameter"),
        Blocks(
            Paragraph(Text("Harish-Chandra parameter versus highest weight; highest coefficient, degree and dimension on compact unitary groups.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/CuspForms/WeightParameter.prod_formalDegree"),
                H("prod_formalDegree"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If l is twice the Harish-Chandra parameter of (κ, e), the product over w of the formal degrees formalDegree of l_w for the compact group U(n) equals the dimension of the representation of weight κ.")))))));
}
