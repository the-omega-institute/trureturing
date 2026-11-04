using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class PairedIdealIntersectionLiftDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/Combinatorics/SpectralGraph/PairedIdealIntersectionLift.";
    private static readonly LibraryNoteRef Source=LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "Actual ideal-intersection graphs and uniform higher-prime Laplacian obstructions.",
        H("PairedIdealIntersectionLift"),Blocks(
            Paragraph(Text("The public mathematical input is unit-exponent.tex at immutable revision b93becea662a746badeadba42fdc3d3eb3db9382. General endpoint arguments follow the completed mathematical note supplied 2026-11-02. The formal proofs and this exposition are independently authored; no priority claim follows.")),
            Node("pairExponents","The full paired exponent family","The exponent vector is (a,a,b,c). Neither tail exponent is bounded above. The final actual graph theorems permit every prime permutation.",DescribeRole.Definition),
            Node("paired_lift_nonzero","Injective paired support construction","For each tail support T, assign h(T) to {0} union T and -h(T) to {1} union T; all other supports get zero. The positive member of each pair is a genuine nonempty proper support cell with positive weight, so any nonzero coordinate vector lifts to a nonzero graph vector.",DescribeRole.Theorem),
            Node("paired_lift_sum","Exact zero sum of actual paired vectors","Each paired cell has the same positive multiplicity a times the product of the tail exponents in T. The two values cancel exactly, including the extension by zero across all universal vertices.",DescribeRole.Theorem),
            Node("paired_support_action","Exact actual paired action","The support-complement Laplacian on this subspace is K_a-I. The proof evaluates the full four-coordinate support algebra with symbolic exponents, including all zero cells and both removed endpoints. It enumerates the fixed support carrier, not a finite set of exponents.",DescribeRole.Theorem),
            Node("actual_paired_eigenvalue","Actual paired spectral lift","A nonzero eigenvector of K_a with eigenvalue kappa lifts to the actual ideal graph eigenvalue V+1-kappa, V=(a+1) squared (b+1)(c+1)-2. The paired vector has explicit zero sum, so the reflection is valid even if kappa-1 is zero.",DescribeRole.Theorem))));
    private static DocumentBlock Node(string name,string title,string prose,DescribeRole role)=>
        Describe.Lean(DescribeId.Create("nik-"+name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix+name),H(title),StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),Blocks(Paragraph(Text(prose))),role);
}
