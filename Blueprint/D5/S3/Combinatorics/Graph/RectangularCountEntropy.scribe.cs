using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class RectangularCountEntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric rectangular subadditivity implies a full square-area limit.",
        H("Rectangular subadditivity and square entropy"),
        Blocks(Describe.Lean(
            DescribeId.Create("square-log-limit"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/RectangularCountEntropy.square_log_limit"),
            H("A square limit from fixed-width Fekete limits"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Let f map pairs of natural numbers to real numbers, let L be nonnegative, assume f(r,c)=f(c,r), assume subadditivity in r for each c, and assume 0<=f(r,c)<=r*c*L for every rectangle. Then there exists a nonnegative real s such that f(n,n)/n squared converges to s through all natural n. Pinned Mathlib Subadditive.tendsto_lim supplies each fixed-width limit g(c). The square limit is the infimum of g(k)/k over positive k. A cut into width-k strips and a remainder bounds the diagonal above by (f(n,k)/n)/k+k*L/n; Fekete's infimum bound supplies the lower bound. No diagonal convergence, periodic-boundary relation or two-dimensional entropy conclusion is assumed."))),
            DescribeRole.Theorem))));
}
