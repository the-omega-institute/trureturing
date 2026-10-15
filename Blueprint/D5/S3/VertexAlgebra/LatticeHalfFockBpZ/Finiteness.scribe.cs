using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockBpZ;

internal sealed class FinitenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native half-Fock energy grades are genuinely finite and have nondegenerate bilinear restrictions.",
        H("Finite Native Grades"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nativegradefinite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Finiteness.native_grade_finite"),
                H("Finite-Dimensional Actual Eigenspaces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original coefficient diagonalization has weight rank/16 plus occupationWeight/2, with variable weight 2n+1. An occupation of weight at most N has every multiplicity at most N and no occupied mode above N. Encoding its remaining coefficients by a function on Fin(rank) times Fin(N+1) into Fin(N+1) is injective. This proves that each exact occupation fiber is finite. The original ground is finite-dimensional, so its finite fiber coordinates give an injective map of the actual energy eigenspace into a finite-dimensional function space. An eigenvalue outside the original weight image has zero eigenspace. No finite-dimensional hypothesis is inserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gradepairingnondegenerate"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Finiteness.grade_pairing_nondegenerate"),
                H("Nondegeneracy on Each Actual Grade"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing finite native spectral reconstruction decomposes an arbitrary test vector into finitely many actual energy grades. Distinct-grade orthogonality removes every component except the matching grade. A restricted radical vector then annihilates the entire tensor and is zero. The exact integralSector equality transfers this result to the original integral theta-odd W grades; their genuine finite-dimensionality permits the bilinear map to identify each grade with its full algebraic dual."))),
                DescribeRole.Theorem))));
}
