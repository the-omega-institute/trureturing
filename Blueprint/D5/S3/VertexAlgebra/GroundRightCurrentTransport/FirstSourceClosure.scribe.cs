using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.GroundRightCurrentTransport;

internal sealed class FirstSourceClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/GroundRightCurrentTransport/FirstSourceClosure.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First-source original-mu closure",
        H("FirstSourceClosure"),
        Blocks(
            Paragraph(Text("The source mu, correctedField, ActualTensor and all unreduced signed lifts are unchanged. Source Borcherds at (p,q,r)=(0,r,d) is applied to current,a,b and mapped by the actual linear source-to-slice map. A common K majorizes both a genuine target A/B locality order and an independently obtained original source-vector tail. Target locality alone is never used to assert source-vector vanishing.")),
            Paragraph(Text("Smaller compatibility identifies Q(A,B) with the slice of the actual source mu. This identification supplies H2 from actual current/source locality, without an assumed general Dong theorem. The same-numerator nested iterate and native_current_inverse then identify both finite source Borcherds sums. Every native defect vanishes, and defect_compatible restores all signed coefficient laws and their three finite supports.")),
            Describe.Lean(
                DescribeId.Create("first-current-step"), DeclarationHandle.Create(Prefix + "first_current_step"),
                H("Closure under an actual first-source current"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("For every D, unit determinant hu, current i, original a and signed gamma, the sole induction hypothesis is OriginalCompatible(a,b,gamma,delta) for every original b and signed delta. For every signed current mode d the conclusion is OriginalCompatible(neutralMode(i,d,a),b,gamma+1,delta). In particular d=-m gives negative-current closure; the lift changes once independently of m."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("first-eigen-arbitrary-second"), DeclarationHandle.Create(Prefix + "first_eigen_arbitrary_second"),
                H("Matching first eigensource and arbitrary second source"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("For every D, unit determinant hu, original a and signed gamma satisfying theta(a)=(-1)^gamma a, every arbitrary original b and signed delta satisfies OriginalCompatible(a,b,gamma,delta). The matching first eigenvalue is an explicit premise. There is no second eigenvalue, positivity or finite charge-space premise.")),
                    Paragraph(Text("The charged_sector_ground_pair supplier and projectedGround_arbitrary_second start the induction on actual finite current words. The tail has lift gamma-1 and the opposite ground parity. Theta-sector source expansion and left linear closure then sum independent finite charge and oscillator supports; the three coefficient supports close by finite unions. Rank zero, zero projections, repeated sources, negative indices and indefinite forms are retained.")),
                    Paragraph(Text("The result is an original twisted coefficient-law bridge on this actual tensor carrier. The entire requested Monster moonshine, VOA, CFT, symmetry anomaly, fusion, string theory, AdS/CFT and local-information-to-global-dynamics formalization remains the overarching objective. No completed physical model or literature novelty is claimed."))), DescribeRole.Theorem))));
}
