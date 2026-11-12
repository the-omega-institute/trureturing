using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickOriginalPairDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickOriginalPair.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/hiaimosonyitomamichel2026hockeystick");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The all-threshold classifier for the original singular pair",
        H("The all-threshold classifier for the original singular pair"), Blocks(
            Paragraph(Text("Let S=A+B, C=normalize(S,A), P=interiorProjection(C). Every statement retains arbitrary traces, zero matrices and empty finite dimension. This geometry is a repository derivation used in quadratic and general-convex equality, not a theorem attributed to GGJ.")),
            Node("original_optimal_iff_normalized", "For PSD A,B and t>=0, original trace optimality of the reconstructed canonical overlap is equivalent to weighted optimality of canonicalOverlap C t among PSD overlaps of C and t(1-C), with weight S. The support bijection handles the complementary endpoint piece.", true, false),
            Node("original_canonical_feasible", "For PSD A,B and t>=0, reconstruct S (canonicalOverlap C t) is an actual element of positiveOverlaps A (tB). This candidate supplies the lower bound needed to turn optimality into equality of the value.", true, false),
            Node("original_all_thresholds_iff_commute", "For PSD A,B, maximalHockey A B t = Tr(A)-Re Tr(S canonicalOverlap(C,t)) for every t>0 exactly when (PSP)(PCP)=(PCP)(PSP). No optimizer, commutation, nonzero pair or faithfulness is assumed. The integrated quadratic criterion consumes this geometric iff; general convex necessity is then obtained from approximate tests.", true, false))));

    private static DocumentBlock Node(string name, string prose, bool theorem, bool literature) =>
        Describe.Lean(DescribeId.Create("maximal-hockey-stick-original-pair-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name.Replace("_", " ")),
            StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
