using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickQuadraticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The bounded quadratic generator and positive-operator Jensen supplier",
        H("The bounded quadratic generator and positive-operator Jensen supplier"), Blocks(
            Paragraph(Text("The quadratic generator and its canonical optimality are known antecedents of the Hiai maximal-divergence theory. The source proves the finite matrix Jensen supplier from positive components; it does not count that antecedent as a newly solved conjecture.")),
            Node("starGenerator", "starGenerator u=(u-1)^2/(u+1) is the fixed reference generator. The compact coordinate turns its perspective into a polynomial on [0,1].", false, false),
            Node("starPerspective", "starPerspective p q=(p-q)^2/(p+q), with Lean real division giving zero at p=q=0. For nonnegative p,q this is the closed quadratic perspective including both axes.", false, false),
            Node("star_perspective_compact", "For 0<x<1, (1-x) starGenerator(x/(1-x))=(2x-1)^2. Quadratic preparation and trace estimates use the same compact-coordinate polynomial.", true, false),
            Node("square_jensen", "For a finite family of PSD matrices E_i with sum 1 and arbitrary real r_i, (sum r_i E_i)^2 <= sum r_i^2 E_i in Loewner order. A sum of positive variance terms proves the inequality. compact_quadratic_jensen consumes it.", true, false),
            Node("square_jensen_subunital", "The same square inequality holds when sum E_i<=1. Adding the positive remainder with coefficient zero reduces to the unital case. QuadraticBound uses the actual normalized preparation components.", true, false),
            Node("compact_quadratic_jensen", "For PSD E_i summing to 1 and arbitrary real x_i, (2 sum x_i E_i-1)^2 <= sum (2x_i-1)^2 E_i. The trace bound consumes this compact-coordinate Jensen inequality.", true, false),
            Node("compact_quadratic_trace_bound", "For PSD S and PSD E_i summing to 1, the trace of S times the square in compact_quadratic_jensen is at most sum (2x_i-1)^2 Re Tr(S E_i). No bounds on the real x_i or normalization of S are assumed. This supplies the canonical quadratic cost comparison.", true, false))));

    private static DocumentBlock Node(string name, string prose, bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-stick-quadratic-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
