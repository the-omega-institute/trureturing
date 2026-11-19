using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickOperationalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite operational hockey infima equal the PSD overlap formulas",
        H("The finite operational hockey infima equal the PSD overlap formulas"), Blocks(
            Paragraph(Text("The two formulas are the finite-matrix content of HMT Proposition V.1 (V.124)-(V.125), following Matsumoto. They are known antecedents, not new conjecture solutions. Only actual finite ReverseTest alphabets are quantified here; identifying an arbitrary L1 source infimum requires a separate theorem. All pairs retain arbitrary traces, zero and singular matrices and empty dimension.")),
            Node("negativeHockey", "negativeHockey R t is the actual sum max(t q_i-p_i,0). Convex.testKernel uses this negative orientation at 0<t<=1.", false, false),
            Node("operationalHockey", "operationalHockey A B t is the real infimum of hockey R t over all natural k and all ReverseTest A B k. Nonemptiness and attainment for PSD pairs and t>0 are proved by an actual witness.", false, false),
            Node("operationalNegativeHockey", "operationalNegativeHockey uses exactly the same entire finite source class and the actual negative profile. The threshold-dependent three-component witness attains both orientations simultaneously.", false, false),
            Node("negative_hockey_eq", "For every finite test and every real t, negativeHockey R t=hockey R t-Tr(A)+t Tr(B). The original mass identities and the scalar positive-part relation prove this. The negative infimum theorem consumes the conversion.", true, false),
            Node("reverse_test_attains_hockey", "For PSD A,B and t>0, one actual finite test has hockey=maximalHockey and negativeHockey=t Tr(B)-overlapValue A (tB). Take an attained common PSD lower bound X and components X,A-X,tB-X. Independent Fin 3 labels use coefficients a=(1,1,0), b=(1/t,0,1/t); normalization gives the stated masses. Zero components have a coordinate state with zero weight. If dimension is empty, the witness has zero labels, so no density state or Nonempty n assumption is required. Both operational infimum equalities consume this witness.", true, true),
            Node("operational_hockey_eq", "For every finite PSD pair and t>0, the infimum of the actual positive classical profiles over all k and ReverseTest equals Tr(A)-overlapValue A (tB). The existing feasible-overlap lower bound and the attained three-component test give both inequalities. Convex.maximal_kernel_eq_operational consumes this formula.", true, true),
            Node("operational_negative_hockey_eq", "For every finite PSD pair and t>0, the infimum of the actual negative classical profiles over all k and ReverseTest equals t Tr(B)-overlapValue A (tB). The same test attains it; no separate source-class assumption is introduced. Convex uses this formula for the whole negative curvature branch, including the atom at one.", true, true))));

    private static DocumentBlock Node(string name, string prose, bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-stick-operational-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
