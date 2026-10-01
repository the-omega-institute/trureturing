using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.FundamentalBijection;

internal sealed class ThetaFixedDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/FundamentalBijection/ThetaFixedDefs.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/archer2024fundamental");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Standard cycle notation defines the fundamental bijection and its fixed-pattern generating functions.",
        H("The Fundamental Bijection and Fixed Avoiders"),
        Blocks(
            Node("fundamental-bijection-thetafixeddefs-cyclefrom", "A cycle read from a letter", "cycleFrom",
                "Read the cycle of m in the permutation p by starting with m and following the permutation until the first return to m, using at most the length of p further steps.", DescribeRole.Definition),
            Node("fundamental-bijection-thetafixeddefs-isleader", "The largest letter of a cycle", "IsLeader",
                "A letter is a cycle leader when every letter in the cycle read from it is at most that letter.", DescribeRole.Definition),
            Node("fundamental-bijection-thetafixeddefs-instdecidableisleader", "Decidability of cycle maxima", "instDecidableIsLeader",
                "For every finite word and letter, whether that letter is the largest in its cycle is decidable.", DescribeRole.Definition),
            Node("fundamental-bijection-thetafixeddefs-theta", "The fundamental bijection", "theta",
                "Write each cycle beginning with its largest letter, order the cycles by increasing largest letter, and concatenate their letters.", DescribeRole.Definition),
            Node("fundamental-bijection-thetafixeddefs-fixedavoiders", "Avoiders fixed by an iterate", "fixedAvoiders",
                "For a size n, an iteration number k, and a pattern sigma, the fixed avoiders are the permutations of one through n that avoid sigma and are fixed by the k-th iterate of the fundamental bijection.", DescribeRole.Definition),
            Node("fundamental-bijection-thetafixeddefs-gf", "The fixed-avoider generating function", "gf",
                "The ordinary generating function has integer coefficient at degree n equal to the number of sigma-avoiding permutations of size n fixed by the k-th iterate.", DescribeRole.Definition),
            Node("fundamental-bijection-thetafixeddefs-cubeclaim", "The proposed third-iterate identity", "cubeClaim",
                "For each of the patterns 231 and 312, the generating function for third-iterate fixed avoiders multiplied by 1 - x - x squared - 2x cubed equals one.", DescribeRole.Definition),
            Node("fundamental-bijection-thetafixeddefs-fourthclaim", "The proposed fourth-iterate identity", "fourthClaim",
                "For each of the patterns 231 and 312, the generating function for fourth-iterate fixed avoiders multiplied by 1 - x - x squared - 2x to the fourth - x to the fifth - x to the sixth equals one.", DescribeRole.Definition),
            Node("fundamental-bijection-thetafixeddefs-fifthclaim", "The proposed fifth-iterate identity", "fifthClaim",
                "For each of the patterns 231 and 312, the generating function for fifth-iterate fixed avoiders multiplied by 1 - x - x squared equals one.", DescribeRole.Definition)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
