using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class PairedIdealIntersectionDeterminantsDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionDeterminants.";
    private static readonly LibraryNoteRef Source=LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "Actual ideal-intersection graphs and uniform higher-prime Laplacian obstructions.",
        H("PairedIdealIntersectionDeterminants"),Blocks(
            Paragraph(Text("The public mathematical input is unit-exponent.tex at immutable revision b93becea662a746badeadba42fdc3d3eb3db9382. General endpoint arguments follow the completed mathematical note supplied 2026-11-02. The formal proofs and this exposition are independently authored; no priority claim follows.")),
            Node("det_tensorK_sub_scalar","Full symbolic determinant","The scalar-shift determinant is expanded symbolically over an arbitrary commutative ring. This is a binding normalization identity, with no fixed positive certificate.",DescribeRole.Theorem),
            Node("det_two_sub_two","Exact H4 endpoint reduction","At a=2 and shift two, the determinant is exactly P2(b,c).",DescribeRole.Theorem),
            Node("det_three_sub_two","Exact H5 endpoint reduction","At a=3 and shift two, the determinant is exactly P3(b,c).",DescribeRole.Theorem),
            Node("det_three_sub_three","H5 upper endpoint","With p=bc and s=b+c, det(K3-3I)=-35p squared+8ps-20s squared+149p+11s+4.",DescribeRole.Theorem),
            Node("det_two_add_one","Shifted H4 determinant","With p=bc and s=b+c, det(K2+I)=4(10p squared+39ps+102p+24s squared+104s+96).",DescribeRole.Theorem),
            Node("det_three_sub_three_neg","Strict upper-endpoint sign for every tail","For b,c at least two, p at least four, s at least four and s at most p. Thus the determinant is at most -27p squared+149p-272=-(27(p-4) squared+67(p-4)+108), strictly negative.",DescribeRole.Theorem),
            Node("three_symmetric_low_eigenpair","H5 paired eigenvalue in (1,3)","A negative determinant prevents S3-3I from being positive semidefinite, so its Hermitian spectral expansion has a negative eigenvalue. Combining with the shared strict lower bound gives a paired eigenvalue in (1,3) throughout b,c at least two.",DescribeRole.Theorem))));
    private static DocumentBlock Node(string name,string title,string prose,DescribeRole role)=>
        Describe.Lean(DescribeId.Create("nik-"+name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name),H(title),StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),Blocks(Paragraph(Text(prose))),role);
}
