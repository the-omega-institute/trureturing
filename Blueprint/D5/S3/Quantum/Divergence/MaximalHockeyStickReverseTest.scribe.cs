using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickReverseTestDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite density-matrix preparations and their profiles",
        H("Actual finite density-matrix preparations and their profiles"), Blocks(
            Paragraph(Text("The source class is all k in the natural numbers and all ReverseTest A B k. Its weights need not have unit mass. Density states, rather than arbitrary positive components, ensure an actual CPTP preparation on the entire source matrix algebra. Empty matrix dimension does not assume a density state exists.")),
            Node("ReverseTest", "A ReverseTest A B k gives nonnegative p,q on Fin k, one actual DensityState n for each label, and exact preparation sums for A and B. The operational infima, quadratic minimum and general-convex finiteCost all quantify over this unchanged structure.", false, false),
            Node("stateMatrix", "stateMatrix R i is the ordinary complex matrix underlying the density state at label i. It is PSD with trace one and is used by preparedOverlap and the mass calculations.", false, false),
            Node("cptp_realization", "Every ReverseTest is realized by a quantum channel from matrices on Fin k to matrices on n. The same CPTP map sends diag(p) to A and diag(q) to B. This is a realization theorem for actual states, not an assumption about an arbitrary L1 source.", true, false),
            Node("preparedOverlap", "preparedOverlap R t is the sum of min(p_i,t q_i) times the prepared state matrices. It is the actual common overlap induced by this test.", false, false),
            Node("hockey", "hockey R t is the actual classical sum of max(p_i-t q_i,0). Operational.operationalHockey takes its infimum over every finite alphabet; no SDP formula is built into this definition.", false, false),
            Node("overlap_feasible", "For t>=0, preparedOverlap R t is PSD and below A and tB. Positive component sums prove each of the three Loewner inequalities. maximal_hockey_le consumes this feasible point.", true, false),
            Node("maximal_hockey_le", "For every actual finite test and t>=0, maximalHockey A B t <= hockey R t. The trace-one states identify the classical overlap mass and the feasible overlap bounds its SDP value. Operational combines this bound with the three-component witness to prove equality of the true infimum.", true, false),
            Node("starCost", "starCost R sums the standard closed quadratic perspectives over exactly the same labels. QuadraticBound and QuadraticIntegral compute and bound this actual cost.", false, false),
            Node("maximalQuadratic", "maximalQuadratic A B is the EReal infimum of starCost over all k and actual ReverseTest A B k. There is no alphabet bound or minimizing-test premise.", false, false),
            Node("maximal_quadratic_le_test", "Every actual finite test gives an upper bound for maximalQuadratic by membership in its defining infimum. QuadraticCanonical consumes this bound with the attained spectral test.", true, false))));

    private static DocumentBlock Node(string name, string prose, bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-stick-reverse-test-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
