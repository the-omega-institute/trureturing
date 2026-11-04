using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class PairedIdealIntersectionObstructionsDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionObstructions.";
    private static readonly LibraryNoteRef Source=LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "Actual ideal-intersection graphs and uniform higher-prime Laplacian obstructions.",
        H("PairedIdealIntersectionObstructions"),Blocks(
            Paragraph(Text("The public mathematical input is unit-exponent.tex at immutable revision b93becea662a746badeadba42fdc3d3eb3db9382. General endpoint arguments follow the completed mathematical note supplied 2026-11-02. The formal proofs and this exposition are independently authored; no priority claim follows.")),
            Node("tensorK","Weighted paired tensor","E_k is diagonal(k+1,1), F_k has rows (1,k) and (1,0), and K_a=(a+1)E_b tensor E_c+a F_b tensor F_c. The coordinate order is empty tail, c tail, b tail, full tail.",DescribeRole.Definition),
            Node("symmetricK","Symmetric representative","Replacing F_k by H_k with rows (1,sqrt(k)) and (sqrt(k),0) gives the symmetric representative. The positive diagonal has entries 1,sqrt(c),sqrt(b),sqrt(b)sqrt(c).",DescribeRole.Definition),
            Node("symmetricK_sub_one_posDef","General strict tensor lower bound","For every real a>0 and b,c at least zero, the symmetric representative minus the identity is positive definite. E+H is positive definite because its quadratic form is (sqrt(k)x0+x1) squared+2 x0 squared; E-H is positive semidefinite with form (sqrt(k)x0-x1) squared. The sum EE+HH equals half the sum of their respective two-factor tensor products, so is positive definite. Also EE-I=(E_b-I) tensor E_c+I tensor(E_c-I) is positive semidefinite. Thus K-I=a(EE+HH)+(EE-I) is positive definite. This proves the supporting (a,a,b,c) bound uniformly, with no integer instance enumeration.",DescribeRole.Theorem),
            Node("tensor_eigenpair_of_symmetric","Nonzero weighted eigenvector transport","The positive diagonal D satisfies D K=S D. Dividing a symmetric eigenvector coordinatewise by its positive diagonal entries preserves nonzero vectors and gives an eigenvector of the original weighted operator with the same eigenvalue.",DescribeRole.Theorem),
            Node("two_symmetric_low_eigenpair","H4 paired eigenvalue in (1,3)","The general lower bound gives every paired eigenvalue greater than one. At a=2 the empty/full principal block of S-3I has determinant -4bc. An explicit negative direction, with empty coordinate 2 sqrt(b)sqrt(c) and full coordinate -(3(b+1)(c+1)-1), gives a strict negative quadratic form. The Hermitian spectral expansion yields an eigenvalue below three.",DescribeRole.Theorem),
            Node("tensor_symmetric_charpoly","Characteristic transport under diagonal geometry","The proved diagonal intertwining has nonzero determinant. The existing Mathlib characteristic-polynomial supplier transports every scalar shift to the symmetric representative. This identity is a binding helper for the general modular spectral argument.",DescribeRole.Theorem),
            Node("tensor_symmetric_det_shift","Exact scalar-shift determinant transport","Taking determinants in the proved diagonal intertwining and cancelling the nonzero positive diagonal determinant gives equality of scalar-shift determinants.",DescribeRole.Theorem))));
    private static DocumentBlock Node(string name,string title,string prose,DescribeRole role)=>
        Describe.Lean(DescribeId.Create("nik-"+name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name),H(title),StatementSource.WithoutFormula(),
            role == DescribeRole.Definition ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),Blocks(Paragraph(Text(prose))),role);
}
