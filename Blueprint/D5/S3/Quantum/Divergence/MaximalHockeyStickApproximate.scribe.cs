using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickApproximateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform bounds for actual finite-test gaps",
        H("Uniform bounds for actual finite-test gaps"), Blocks(
            Paragraph(Text("The same fixed pair A,B supplies every test in a sequence. Constants depend only on its actual traces, not the number of labels. This source feeds the full-support measure transfer and the general-convex finite-cost approximation argument.")),
            Node("PositiveThreshold", "PositiveThreshold is the real subtype t>0. This is exactly the curvature domain used in the integrated classification.", false, false),
            Node("gap", "gap R t=hockey R t-maximalHockey A B t for positive t. This is the actual gap of the prepared classical test against the PSD value, whose operational meaning is proved in Operational.", false, false),
            Node("left_mass", "For every actual finite test, Re Tr(A)=sum p_i, because each prepared state has trace one. Both orientation conversion and cost decomposition consume the original mass identity.", true, false),
            Node("right_mass", "For every actual finite test, Re Tr(B)=sum q_i. The original arbitrary mass is retained in Lipschitz constants and affine cost decomposition.", true, false),
            Node("maximal_hockey_nonneg", "For PSD A,B and t>=0, maximalHockey A B t>=0. Every feasible overlap is bounded by A in trace. The compact maximal profile and general convex kernel use this bound.", true, false),
            Node("hockey_le_trace", "For every test and t>=0, hockey R t<=Re Tr(A). Nonnegativity of p,q bounds each positive part by p_i. The actual gap bound uses this uniform mass ceiling.", true, false),
            Node("hockey_lipschitz", "For every test and all real s,t, |hockey R t-hockey R s|<=|t-s| Re Tr(B). Summing the scalar positive-part Lipschitz estimates removes dependence on label count. actual_gap_profile_data consumes it.", true, false),
            Node("actual_gap_profile_data", "For PSD A,B, on positive thresholds gap R lies in [0,Tr(A)] and is Lipschitz with constant 2 Tr(B), expressed by Real.toNNReal. Combining overlap and classical Lipschitz bounds gives constants uniform over every finite test. Both quadratic and general convex transfer consume these facts.", true, false),
            Node("actual_tests_full_support_transfer", "For PSD A,B, any sequence of actual finite tests, and g_j exactly equal to their gaps, assume integrable gaps whose integrals against locally finite full-support mu tend to zero. Then g_j(t) tends to zero at every positive threshold and its integral tends to zero against every finite measure nu. No minimizing test or compactness of the test class is assumed. QuadraticEquality.vanishing_curvature_gaps_imply_commute consumes this transfer.", true, false))));

    private static DocumentBlock Node(string name, string prose, bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-stick-approximate-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
