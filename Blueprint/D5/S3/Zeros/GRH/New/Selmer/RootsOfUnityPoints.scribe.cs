using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class RootsOfUnityPointsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Roots Of Unity Points", H("Roots Of Unity Points"),
        Blocks(
            Paragraph(Text("ℓ-power roots of unity keep valuations of polynomials of any degree low.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/RootsOfUnityPoints.exists_roots_of_unity_ellVal_le"),
                H("exists_roots_of_unity_ellVal_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Fix δ > 0, m, L, a, q and finitely many bounds B_k. For large N, then large O: given F_{k,d} (1 ≤ d ≤ m) in ≤ q variables with valuation ≤ B_k at points u_{k,d}, ℓ ∣ (u − 1)^a coordinatewise, and monic D_n of total degree ≤ L, some tuple ζ in O of ℓ^N-th roots of unity has v(F_{k,d}(ζ^d)) ≤ δ + B_k and all v(D_n(ζ_j)) ≤ δ.")))))));
}
