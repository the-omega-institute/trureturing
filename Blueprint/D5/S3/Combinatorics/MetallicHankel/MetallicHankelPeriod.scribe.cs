using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MetallicHankel;

internal sealed class MetallicHankelPeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MetallicHankel/MetallicHankelPeriod.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/han2025hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Periodic monic moment relations propagate a signed period and a five-value bound to every determinant size.",
        H("Propagation of Hankel Periodicity Across Zero Intervals"),
        Blocks(
            Node("metallic-hankel-period-propagate", "A signed period for the next Hankel shift", "propagate",
                "Let Phi(q) = sum_{r >= 0} f_r q^r be an integral formal power series, and let ell,n,L,P be nonnegative integers with P even. Suppose s_0 = 0 and s_{p+1} = s_p+k_p+1. Assume s_{p+L} = s_p+P, k_{p+L} = k_p, h_{p+L} = h_p and c_{p+L,0} = c_{p,0} for every p, with h_p in {-1,1}, c_{p,0} in {-1,0,1,2} and c_{p,s_p} = 1. The moment sum sum_{r=0}^{s_p} c_{p,r} f_{ell+r+t} must vanish for t < s_{p+1}-1 and equal h_p at t = s_{p+1}-1. Suppose also that, for every p, the product of (-1)^{k_{p+i}(k_{p+i}+1)/2} h_{p+i}^{k_{p+i}+1} over 0 at most i and i less than L is (-1)^n. Then for every nonnegative j, Delta_{j+P}^{(ell+1)} = (-1)^n Delta_j^{(ell+1)}, and Delta_j^{(ell+1)} belongs to {-2,-1,0,1,2}. The conclusion includes determinant sizes between successive s_p, where the preceding-shift Hankel determinants vanish.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
