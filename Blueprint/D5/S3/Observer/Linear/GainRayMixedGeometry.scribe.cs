using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class GainRayMixedGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Diagonal rigidity of bounded-degree evaluations", H("Diagonal rigidity of bounded-degree evaluations"), Blocks(
            Describe.Lean(DescribeId.Create("gain-ray-gainraymixedgeometry-diagonal-evaluation-rigid"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/GainRayMixedGeometry.diagonal_evaluation_rigid"),
                H("Every preserving diagonal is scalar"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural d,n with d+2 at most n, injective nodes t:Fin n to the reals, and arbitrary a:Fin n to the reals, suppose that for every polynomial p of natural degree at most d there is a polynomial q of natural degree at most d satisfying q(t(i))=a(i)*p(t(i)) for every i. Then a(i)=a(j) for every i,j. Zero entries of a are allowed. Choose d nodes outside i,j and take their monic root product p. The polynomial q-a(i)*p vanishes on those d nodes and on node i, so it is zero. Since p(t(j)) is nonzero, evaluation at j gives a(j)=a(i). The hypothesis includes n=2(d+1) for d at least one."))), DescribeRole.Theorem))));
}
