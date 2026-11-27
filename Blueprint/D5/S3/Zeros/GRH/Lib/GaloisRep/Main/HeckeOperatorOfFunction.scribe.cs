using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GaloisRep.Main;

internal sealed class HeckeOperatorOfFunctionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hecke Operator Of Function", H("Hecke Operator Of Function"),
        Blocks(
            Paragraph(Text("Hecke polynomial coefficients, monic of degree n; jumps are distinct. Left translation; operators attached to test functions and their products with Hecke operators.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GaloisRep/Main/HeckeOperatorOfFunction.IsOperatorOf"),
                H("IsOperatorOf"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The function f is right K-invariant and nonzero on finitely many cosets gK, and T is the operator Σ_{g ∈ G/K} f(g)π(g) on the K-fixed vectors.")))))));
}
