using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class FourPrimeIdealIntersectionObstructionsDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/Combinatorics/SpectralGraph/FourPrimeIdealIntersectionObstructions.";
    private static readonly LibraryNoteRef Source=LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "Actual ideal-intersection graphs and uniform higher-prime Laplacian obstructions.",
        H("FourPrimeIdealIntersectionObstructions"),Blocks(
            Paragraph(Text("The public mathematical input is unit-exponent.tex at immutable revision b93becea662a746badeadba42fdc3d3eb3db9382. General endpoint arguments follow the completed mathematical note supplied 2026-11-02. The formal proofs and this exposition are independently authored; no priority claim follows.")),
            Node("two_equal_obstruction","All actual four-prime (2,2,b,c) obstructions","For four arbitrary distinct primes, every positive b,c and every permutation of the four exponent positions, the actual ideal-intersection graph is not Laplacian integral. If either tail is one, H1 applies. Otherwise the paired spectrum contains a real kappa in (1,3). The exact P2 endpoint classification excludes kappa=2 except at the unordered pair {5,8}. Away from that pair, kappa is noninteger; at the pair, the entire mod-nine family supplies a noninteger real eigenvalue. The proved paired lift gives an actual graph eigenvalue V+1-kappa. Its integrality would imply that of kappa, a contradiction.",DescribeRole.Theorem),
            Node("three_equal_obstruction","All actual four-prime (3,3,b,c) obstructions","For every four distinct primes, positive b,c and exponent-position permutation, the actual graph is nonintegral. If both tails are at least two, the paired eigenvalue kappa lies in (1,3), and the exact P3 exclusion gives kappa different from two. Its actual lift lies strictly in (V-2,V) and differs from V-1, with V=16(b+1)(c+1)-2. Thus the exact requested interval and middle-point exclusion hold. When a tail is one, H1 supplies nonintegrality at that unit boundary.",DescribeRole.Theorem))));
    private static DocumentBlock Node(string name,string title,string prose,DescribeRole role)=>
        Describe.Lean(DescribeId.Create("nik-"+name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name),H(title),StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),Blocks(Paragraph(Text(prose))),role);
}
