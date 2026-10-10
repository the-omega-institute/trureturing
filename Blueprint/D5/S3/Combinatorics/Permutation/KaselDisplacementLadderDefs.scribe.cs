using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class KaselDisplacementLadderDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/KaselDisplacementLadderDefs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dyadic horizons, normalized stage schemes and distinguished displacement values.",
        H("Kasel displacement-ladder definitions"),
        Blocks(
            Node("block", "Dyadic block index",
                "block(v) is Nat.clog 2 v. For v at least two it is the unique k with "
                + "2^(k-1)<v<=2^k. The definition is total on the natural numbers.", DescribeRole.Definition),
            Node("SA", "The finite dyadic horizon",
                "SA(m) filters the inclusive interval [1,4^m] by block(v)>=2 and Even(block(v)). "
                + "It is S_A intersected with this finite horizon.", DescribeRole.Definition),
            Node("lexLess", "Stage concatenation order",
                "lexLess(s,r,a,b) means s(a)<s(b), or s(a)=s(b) and r(a)<r(b). "
                + "It compares stage first and fibre position second.", DescribeRole.Definition),
            Node("Valid", "A valid finite scheme",
                "Valid(X,s,r) requires that for a,b in X, equality of both stage and fibre "
                + "position implies a=b. For every x<y<z in X with x+z=2*y, it excludes "
                + "both lexLess(x,y) and lexLess(y,z) together, and both lexLess(z,y) "
                + "and lexLess(y,x) together. Thus neither monotone AP occurs in the concatenation.",
                DescribeRole.Definition),
            Node("Normalized", "Nonnegative displacement",
                "Normalized(X,s) requires floor(block(v)/2)<=s(v) for every v in X. "
                + "Stages are natural numbers and division is natural-number division.", DescribeRole.Definition),
            Node("distinguished", "The distinguished values",
                "distinguished is the finset {3,4,9,10,11,12,13,14,15,16}, namely "
                + "S_A intersected with [1,16].", DescribeRole.Definition),
            Node("block_eq_of_pow_pred_lt_le_pow", "Identifying a dyadic block",
                "If k>=1 and 2^(k-1)<v<=2^k, then block(v)=k.", DescribeRole.Theorem),
            Node("distinguished_subset", "Distinguished values lie in every relevant horizon",
                "For m>=2, distinguished is a subset of SA(m).", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("kasel-defs-" + name.ToLowerInvariant().Replace("_", "-")), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
