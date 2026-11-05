using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class PairedIdealIntersectionCongruenceDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionCongruence.";
    private static readonly LibraryNoteRef Source=LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "Actual ideal-intersection graphs and uniform higher-prime Laplacian obstructions.",
        H("PairedIdealIntersectionCongruence"),Blocks(
            Paragraph(Text("The public mathematical input is unit-exponent.tex at immutable revision b93becea662a746badeadba42fdc3d3eb3db9382. General endpoint arguments follow the completed mathematical note supplied 2026-11-02. The formal proofs and this exposition are independently authored; no priority claim follows.")),
            Node("shifted_tensor_charpoly_mod_three","Nilpotent characteristic transport","Over any commutative ring R of characteristic three, suppose b+1 and c+1 are nilpotent, with arbitrary nilpotency orders. Put X=(F_b+I) tensor I and Y=I tensor(F_c+I). Their squares are (b+1)I and (c+1)I, so X and Y are nilpotent. They commute and K2+I=X+Y-XY; the existing commuting nilpotent sum, product and subtraction laws give nilpotence of K2+I. Its characteristic polynomial differs from the fourth power of the polynomial variable by a nilpotent polynomial. The infinite mod-nine consumer specializes this general law to the reduced field F3, where that difference is zero. Nonreduced rings and unbounded nilpotent thickenings are included in the provider statement.",DescribeRole.Theorem),
            Node("shifted_tensor_det_not_dvd","The whole infinite family excludes divisibility by 27","For b=9s+5,c=9t+8, the symbolic determinant is 27W+18 for an integer polynomial W. Equivalently, with b=3u-1,c=3v-1, r=u+v,z=uv, it is 36(90z squared+57zr-5r squared+44z+r+2); the bracket is two modulo three. Hence 27 never divides the determinant in this entire family.",DescribeRole.Theorem),
            Node("two_mod_nine_noninteger","Infinite-family noninteger real spectrum","For positive b=9s+5 and c=9t+8, suppose all real symmetric eigenvalues were integers. The nilpotent characteristic reduction makes every shifted integer root divisible by three. Their product would then be divisible by 3 to the fourth power, contradicting the preceding determinant formula. Positive diagonal transport supplies a noninteger real eigenvalue of the original weighted tensor. The pair (5,8) is the specialization s=t=0; exchanging the tail coordinates covers (8,5). No fixed mod-17 success certificate is used.",DescribeRole.Theorem))));
    private static DocumentBlock Node(string name,string title,string prose,DescribeRole role)=>
        Describe.Lean(DescribeId.Create("nik-"+name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name),H(title),StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),Blocks(Paragraph(Text(prose))),role);
}
