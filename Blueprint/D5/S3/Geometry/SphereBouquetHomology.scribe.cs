using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class SphereBouquetHomologyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/SphereBouquetHomology.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact arbitrary sphere-wedge sources have torsion-free positive integral singular homology.",
        H("Singular homology of compact sphere-wedge sources"),
        Blocks(
            Node("bouquet", "finite_bouquet_torsionFree", "Actual finite positive bouquets in all positive degrees",
                "For every finite list b of PositiveDimension, ring k and torsion-free coefficient module M, actual singular H_q(Bouquet b;M) is torsion-free for every q>=1, with no relation required between q and the entries of b. A private induction on the native bouquet uses the existing singleton sphere homeomorphism, the all-degrees sphere theorem, the actual based contractions of finite vertex stars, PointedWedgeHomology.homologyIso and bouquetAppendHomeomorph. CompactSphereNormalForm.nativeBouquetHomeomorph then transports to the literal FamilyWedge of standard spheres. The empty inner list is a one-point space, whose positive homology vanishes.", DescribeRole.Theorem),
            Node("model", "finite_model_torsionFree", "Finite outer coproducts, including the empty space",
                "For every natural m and family b:Fin m to lists of positive dimensions, actual positive-degree singular homology of CompactSphereNormalForm.Model b is torsion-free over those same coefficient modules. A dependent sigma-sum homeomorphism and OpenCoverHomology.sumIso perform the induction. At m=0 the source is empty, not a point; an empty inner bouquet remains a point component.", DescribeRole.Theorem),
            Node("compact-wedge", "compact_wedge_torsionFree", "Compact sources with arbitrary original sphere families",
                "Let X be compact and homotopy equivalent to CompactWedgeFiniteFactor.FamilyWedge p, where J is an arbitrary type, d:J to natural numbers is unrestricted and p is any choice of original sphere basepoints. For every positive degree and torsion-free coefficient module, actual singular homology of X is torsion-free. CompactSphereNormalForm.compactWedgeModel supplies the existing finite positive-bouquet model and its actual equivalence. The theorem imposes no finiteness on J, no positivity on d and no special original basepoint choice. In particular S0 factors and the empty family remain included.", DescribeRole.Theorem),
            Node("source", "compact_sourceSP_torsionFree", "The original compact sourceSP telescope",
                "For every compact topological space X in Type and every HereditaryLexicographicProduct.sourceSP.{0,v} X, actual integral singular homology is Module.IsTorsionFree in every degree q>=1. sourceSP retains its contractible alternative and its arbitrary J:Type v sphere-wedge alternative. The coefficient object is ModuleCat.of Int Int in Mathlib singularHomologyFunctor; no synthetic carrier or assumed homology comparison is used. The contractible branch uses actual singular-homology vanishing, and the wedge branch uses compact_wedge_torsionFree.", DescribeRole.Theorem),
            Node("integer-obstruction", "compact_sourceSP_smul_eq_zero", "Every nonzero integer acts injectively",
                "For every such compact X and sourceSP witness, every q>=1, nonzero integer n and actual integral singular homology class z in degree q, n times z equal to zero implies z equal to zero. In particular the intended obstruction can use n=2. This is an application of the preceding torsion-freeness theorem and the integral-domain scalar law. The classical sphere and open Mayer–Vietoris ingredients are attributed to Hatcher and the existing TauCeti port; the exact finite-coordinate and compact-normalization suppliers are reused. This batch gives no original-problem resolution credit for Carnero Bravo arXiv:2505.06457v2 Question 32. The seed-to-singular comparison, suspension and graph construction steps, induced-coordinate embedding and final refutation remain separate proof obligations. The source-readout audit remains unfinished under https://github.com/the-omega-institute/trureturing/issues/25194; no declared_validated registration is claimed.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
