using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MinimalForts;

internal sealed class SimplexApproximationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MinimalForts/SimplexApproximation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/becker2024minimalforts");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Feasible integer multiplicities and vanishing error.", H("Feasible integer multiplicities and vanishing error"),
        Blocks(
            Node("eventual-simplex-approximation", "Approximation on the entire integer tail", "eventual_simplex_approximation", "For real p,b,g,c with p positive, b negative, zero less than g less than p, and b divided by p irrational, every positive real epsilon admits a natural threshold K such that every natural k at least K has nonnegative natural x,y,z with x plus y plus z equal to k and absolute value of x b plus z p minus k g minus c less than epsilon. A finite rotation window is fixed for each tolerance; the interior target slope ensures nonnegative feasible coordinates on the entire tail.", DescribeRole.Theorem),
            Node("simplex-approximation-sequence", "Actual feasible sequences for every index", "simplex_approximation_sequence", "Under the same hypotheses, there are three natural-valued sequences x,y,z whose sum is k at every natural index k, and whose signed real errors x(k)b plus z(k)p minus k g minus c tend to zero as k tends to infinity. At every index a least absolute-error pair is chosen from the finite feasible simplex. The preceding tail theorem bounds these least errors for each positive tolerance. These feasible sequences supply the multiplicities in the every-order graph construction.", DescribeRole.Theorem)), []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
