using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hypermatrix;

internal sealed class PencilParameterFibersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hypermatrix/PencilParameterFibers.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/koprowski2026enumeration");
    private static readonly LibraryNoteRef Koszul =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/berkesch2013tensorcomplexes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit factors and scalar fibers", H("Explicit factors and scalar fibers"),
        Blocks(
            Describe.Lean(DescribeId.Create("pencil-parameter-fibers"),
                DeclarationHandle.Create(Prefix + "pencil_parameter_fibers"), H("Explicit factors and scalar fibers"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every field F, every natural k at least one, every ClosureFullRank face pair T has factors A,B with T0=A E0 B and T1=A E1 B. Every factor pair produces ClosureFullRank faces. Scalar shifts preserve factorMap; any two factor pairs with the same image differ by such a shift; for each fixed pair the shift is injective. The normalization uses the finite observability map over the algebraic closure, descends its injectivity to F, and constructs the standard chain basis. Intertwiners of the two standard faces are scalar. Thus the actual fibers are exactly the multiplicative units of F, including in characteristic two."))), DescribeRole.Theorem)
        ), []));
}
