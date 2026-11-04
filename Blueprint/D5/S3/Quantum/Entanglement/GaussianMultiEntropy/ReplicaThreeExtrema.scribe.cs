using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.GaussianMultiEntropy;

internal sealed class ReplicaThreeExtremaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaThreeExtrema.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every total integer N >= 3, the actual order-three Gaussian genuine multi-entropy is minimized precisely by the balanced positive integer triples and maximized precisely by permutations of (N-2,1,1), with all ties retained. The two extremal classes coincide at N=3 and N=4.",
        H("All-total integer extrema at replica three"),
        Blocks(
            Paragraph(Text("Scientific source: Haobo Ma then Wenlin Zhang, An exact balancing law for order-three Gaussian multi-entropy, 4 November 2026, CC BY 4.0. Camargo and Nishida supply the physical family; Marshall, Olkin and Arnold supply the classical majorization criterion. The proof reuses the actual integral/Fourier bridge and the strict scalar comparison, retaining their canonical and transplant credits. Higher replicas, physical replica-one continuation, other branches and the separate Page/large-N issue 22644 remain outside this result.")),
            Node("balanced", "The balanced representative", "balanced", "b",
                "Write N=3q+r with q=N/3 and r=N%3 in {0,1,2}. The descending representative has exactly r entries q+1 and the remaining entries q: (q+[r>0],q+[r>1],q). All permutations represent the same balanced class.", DescribeRole.Definition),
            Node("extreme", "The extreme representative", "extreme", "e",
                "The extreme positive integer representative is (N-2,1,1). Its full permutation class is retained, including the duplicate entries and the fully tied N=3 case.", DescribeRole.Definition),
            Node("is-balanced", "Balanced integer triples", "IsBalanced", "B",
                "A triple is balanced exactly when x_i <= x_j+1 for every ordered pair i,j, equivalently every pair of integer sizes differs by at most one. This definition does not impose an ordering on party labels.", DescribeRole.Definition),
            Node("integer", "Scalar extrema and both iff equality classes", "integer_extrema", "V",
                "For every k>0, integer N>=3 and positive integer triple x of total N, V(k,balanced N) <= V(k,x) <= V(k,N-2,1,1). Equality at the minimum holds if and only if x is balanced; equality at the maximum holds if and only if x is a permutation of (N-2,1,1). The values are the exact logarithmic expression of ReplicaThreeScalar, evaluated at the displayed representatives, for all three residues of N. Sorting supplies the two prefix bounds; the strict Schur theorem supplies both permutation equality directions. This is universal in N, not a finite enumeration.", DescribeRole.Theorem),
            Node("physical", "Actual integral-defined physical extrema", "GM3_three_extrema", "GM",
                "For every integer N>=3, a>1 and positive integer labelled triple x with sum N, the actual integral-defined GaussianMultiEntropyAsymptotic.GM3 3 x_0 x_1 x_2 a lies between V(kappa,balanced N) and V(kappa,N-2,1,1), where kappa=3(a^2-1)/(4(N-1)). It equals the lower endpoint if and only if every pair of sizes differs by at most one; it equals the upper endpoint if and only if x is a permutation of (N-2,1,1). Both endpoint representatives are positive triples of the required total, so these bounds are attained. Each endpoint is the exact formula log((1+kappa s)^2/(D_x D_y D_z))/12 evaluated at its representative, with all three labelled cut factors. Physical mode counts are integers; positive reals occur only in the scalar comparison used by the proof. At a=1 the separate physical behavior theorem gives zero and all triples tie.", DescribeRole.Theorem),
            Node("degeneracy", "Coincident extrema at totals three and four", "extremal_degeneracy", "V",
                "For every k>0 and N>=3, the extreme representative is balanced if and only if N=3 or N=4; equivalently the minimum and maximum values coincide if and only if N=3 or N=4. Thus every admissible triple at these totals belongs to the common extremal class, with no false strict separation. For every N>=5 the two extremal values are distinct and the minimum is strictly smaller.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        string symbol, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("gaussian-three-extrema-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(F.Id(symbol))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, null);
}
