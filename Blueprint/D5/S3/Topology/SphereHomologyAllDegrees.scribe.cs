using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class SphereHomologyAllDegreesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Topology/SphereHomologyAllDegrees.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The TauCeti sphere computation and dimension induction cover every positive degree.",
        H("Actual sphere homology in every degree"),
        Blocks(
            Node("off-dimension", "isZero_reducedHomology_sphere", "Reduced sphere homology vanishes off the dimension",
                "For every natural sphere dimension d, real inner-product space E with a supplied orthonormal basis indexed by Fin(d+1), coefficient object R in an abelian category with the required coproducts, and natural q distinct from d, the actual reduced singular homology of the unit sphere in E is zero. Dimension zero uses the actual discrete sphere. In positive dimension, degree zero uses path connectedness; positive degrees use the existing reducedSingularHomologySphereSuccIso and orthogonalLast basis. Thus the induction includes degrees below and above the dimension. This is the classical homology computation of spheres, using the existing TauCeti port at its original general telescope.", DescribeRole.Theorem),
            Node("torsion-free", "isTorsionFree_singularHomology_sphere", "Every positive-degree sphere homology module is torsion-free",
                "For a ring k and any coefficient module M satisfying Module.IsTorsionFree k M, the actual singular homology of each such sphere satisfies Module.IsTorsionFree in every q>0. On the diagonal, TauCeti.reducedSingularHomologySphereIso identifies the group with M. Off the diagonal, the preceding vanishing theorem makes it a zero module. Over a general ring, this means injectivity of multiplication by regular scalars as specified by Mathlib; injectivity for every nonzero scalar is only asserted at the integral-domain endpoint. No IsDomain assumption is imposed on this generic theorem.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Geometry/hatcher2002algebraic")),
            Blocks(Paragraph(Text(prose))), role);
}
