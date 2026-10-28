using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class BinaryRunSourceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Circle/BinaryRunSource.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical cyclic binary carries retain every labelled position and force a separated-run lower bound.",
        H("Physical cyclic binary runs"),
        Blocks(
            Paragraph(Text(
                "This repository result is a source-level bridge for Circle C3.1. The carrier is the physical Fin(k) cycle: "
                + "equal numerical source values and proper numerical periods remain present. It does not assume numerical "
                + "injectivity or least period k, and it does not settle arbitrary signed A.")),
            Node("edge", "Labelled false-to-true edges", "falseTrueEdge", DescribeRole.Definition,
                "falseTrueEdge c i means c(i)=false and c(finRotate k i)=true. physicalRunCount is the cardinality of this labelled edge set, so repeated values are counted by their physical labels."),
            Node("tops", "Ordinary binary run tops", "binaryRunTops", DescribeRole.Definition,
                "binaryRunTops e is the finite set of bit positions j with e.testBit j=true and e.testBit (j+1)=false. binaryRunCount is its cardinality."),
            Node("separated", "Separated-run estimate", "separated_run_bound", DescribeRole.Theorem,
                "Every two selected run tops differ by at least two. Ordering them gives the j-th top at least 2j, hence e is at least the sum of 4^j over all selected tops. The geometric identity gives 4^(binaryRunCount e) <= 3e+1. This is the new escape content."),
            Node("profile", "Physical cyclic binary profile", "cyclic_binary_run_bound", DescribeRole.Theorem,
                "For k>=2, u:Fin(k)->Nat with recurrence u(rho i)=2u(i)-(2^k-1)c(i) in integers, an anchor u(a)=4e+1 below 2^(k-1) has physicalRunCount c=binaryRunCount e+1 and 4^(physicalRunCount c-1)<=3e+1. The proof consumes ZeroSumSubsets.carry_weight for reconstruction, Mathlib binary uniqueness for digit identification, and the physical cycle permutation. No upper bound on the other values of u is needed for this telescope."),
            Node("negative-large", "Actual negative LARGE labels", "actualSource_falseTrueEdge_iff", DescribeRole.Theorem,
                "For k>=3 and every physical i, falseTrueEdge (nativeCarry k t) i holds exactly when actualSource k t i<=-quarter k. Here nativeCarry is decide(actualSource>0). The centered range is [-(2Q-1),2Q-1], the modulus is 4Q-1, and centered doubling sends a nonpositive source to a positive source exactly on [-2Q+1,-Q]. The proof includes the physical wrap at k-1 through phase_step and centered_full_period."),
            Node("negative-count", "Count all physical negative LARGE labels", "actualNegativeLargeCount", DescribeRole.Definition,
                "actualNegativeLargeCount k t is the cardinality of Finset.univ.filter (fun i:Fin(k) => actualSource k t i<=-quarter k). actualSource_runCount_eq identifies it with physicalRunCount (nativeCarry k t), using the pointwise equivalence at every label. Numerical repetitions are counted separately."),
            Node("native", "Actual centered source consumer", "actualSource_binary_run_bound", DescribeRole.Theorem,
                "For the actual centered source, the oriented unsigned code is -actualSource plus the modulus when negative, and the carry is decide(actualSource>0). Existing SourceWidth and ExpandingSourcePath lemmas prove its nonnegative normalization and physical recurrence. At an anchor equal to -(4e+1), the native strict inequality 3e+1<quarter k puts the anchor code below 2^(k-1). The conclusion directly states actualNegativeLargeCount k t=binaryRunCount e+1 and 4^(actualNegativeLargeCount k t-1)<=3e+1; it consumes the pointwise sign-transition bridge via actualSource_runCount_eq. For use in the original 12-condition minimum setting, the consumer must establish k>=3, this anchor form and strict inequality, and four distinct negative LARGE physical labels. The count hypothesis remains separate from the doubling proof: once supplied, Rneg>=4 forces e>=21, and the strict quarter bound forces k>=2*Rneg+1. Neither the full original 12-condition configuration nor its four-label consequence is proved here. At k=6,t=42, all six labels remain, the numerical period is two and Rneg=3; the strict native hypothesis fails at equality 3e+1=quarter k=16. Full arbitrary signed-A C3.1 is open."))), []));

    private static DocumentBlock Node(string id, string title, string declaration, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("circle-binary-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
