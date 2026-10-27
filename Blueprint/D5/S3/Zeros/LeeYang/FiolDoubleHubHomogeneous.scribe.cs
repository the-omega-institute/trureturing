using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.LeeYang;

internal sealed class FiolDoubleHubHomogeneousDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The physical double-hub family: homogeneous.",
        H("Double-hub homogeneous"), Blocks(
            Paragraph(Text("The coefficient of the original independent two-coupling source equals 200 times 12^(2m) times the sum of [X^j]R_m times a^(4m+6-j)b^j, for 0<=j<=4m+6. This identity holds for every pair of complex couplings.")),
            Paragraph(Text("For a nonzero first coupling, the source ratio identity and the coefficient identity give the formula directly. Both sides are continuous in the first coupling, and equality on its dense nonzero locus extends to zero. The ratio formula itself retains its nonzero hypothesis.")),
            Paragraph(Text("These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.")),
            Describe.Lean(DescribeId.Create("fioldoublehubhomogeneous-actual-closed-ratio"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubHomogeneous.actual_closed_ratio"), H("actual closed ratio"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Organizes instantiation, projections, finite-sum/degree/phase rewrites or normalization on a live proof path; no independent new-content claim. Exact source statement: theorem actual_closed_ratio (m cutoff : \u2115) (hm : 1\u2264m) (hc : 3\u2264cutoff)     (a b : \u2102) (ha : a\u22600) :     homogeneousCoefficient m cutoff a b = (200*(12:\u2102)^(2*m))*a^(4*m+6)*       ((R m).map Complex.ofRealHom).eval (b/a)."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fioldoublehubhomogeneous-actual-homogeneous-identity"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubHomogeneous.actual_homogeneous_identity"), H("actual homogeneous identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Proves all-complex homogeneous equality from independent finite sums, a degree bound and continuous extension through a=0. Exact source statement: theorem actual_homogeneous_identity (m cutoff : \u2115) (hm : 1\u2264m) (hc : 3\u2264cutoff)     (a b : \u2102) : homogeneousCoefficient m cutoff a b=expectedHomogeneousCoefficient m a b."))), DescribeRole.Theorem))));
}
