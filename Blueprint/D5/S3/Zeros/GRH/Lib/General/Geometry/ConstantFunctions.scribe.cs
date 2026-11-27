using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Geometry;

internal sealed class ConstantFunctionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constant Functions", H("Constant Functions"),
        Blocks(
            Paragraph(Text("Locus where a point lies in a closed subscheme is an ideal. fpqc descent: a functional relation total on a cover is a morphism. Global functions on a base-changed abelian variety are constant on fibres.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Geometry/ConstantFunctions.hasConstFunctions_of_isPullback"),
                H("hasConstFunctions_of_isPullback"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let A be an abelian variety over a field k and X = A ×_k Spec C. A function regular on all of X takes equal values at any two ring-valued points with the same image in Spec C.")))))));
}
