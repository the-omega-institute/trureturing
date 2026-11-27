using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Rigidity;

internal sealed class AnalyticVectorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analytic Vectors", H("Analytic Vectors"),
        Blocks(
            Paragraph(Text("Lowest K-type and Casimir value determine a discrete series coefficient; analytic vectors (known result; see Lib.DiscreteSeries.Rigidity.CasimirGrowth).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Rigidity/AnalyticVectors.exists_innerProductSpace"),
                H("exists_innerProductSpace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a representation π on X with invariant positive definite hermitian form B as in IsUnitaryRep, there are a complex inner product space H and a linear isomorphism j : X → H with ⟨jx, jy⟩ = B(x,y).")))))));
}
