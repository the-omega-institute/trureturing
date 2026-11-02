using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class FiedlerResistanceK2mSharpSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/FiedlerResistanceK2mSharpSpectrum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp product equality on labelled K2m determines the entire native spectrum.",
        H("The sharp product and its two positive spectral rays"),
        Blocks(
            Paragraph(Text("Every natural m at least three is allowed. The vertices are Fin (2+m), with two labelled hubs and m labelled leaves. Every one of the 2m hub-to-leaf conductances varies independently over strictly positive reals. The matrix is the original ordinary unnormalized wLap, lambda2 is the original mean-zero Rayleigh infimum, and totalRes is the original harmonic-current resistance summed over every unordered distinct vertex pair, including nonadjacent pairs. No total-conductance or symmetry assumption is imposed on competitors. Nonedge values are arbitrary.")),
            Node("spectrum", "The complete native eigenvalue multiplicities", "FullSpectrum",
                "The eigenvalues are those returned by Matrix.IsHermitian.eigenvalues for the actual matrix wLap (K2m m) w. FullSpectrum requires exactly one zero eigenvalue, exactly m entries equal to t, exactly one entry equal to m*t, and every entry equal to one of those three values. It imposes no ascending-index convention and introduces no surrogate matrix or assumed spectral list. When m is at least three and t is positive, the three values are distinct. The generic Hermitian spectral theorem makes this indexed enumeration the full spectrum with multiplicity.", DescribeRole.Definition),
            Node("ray", "One common sign across every leaf", "Ray",
                "For a real scale t and sign epsilon, Ray fixes each first-hub conductance to t/2*(1+epsilon*sqrt((m-2)/(m+2))) and each second-hub conductance to t/2*(1-epsilon*sqrt((m-2)/(m+2))). The same epsilon is used for all leaves. The theorem restricts t to positive values and epsilon to +1 or -1. The definition compares only labelled edges.", DescribeRole.Definition),
            Node("claim", "The whole sharp-product endpoint", "SharpProductClaim",
                "The conjunction contains the universal product bound C_m=(m+2)(m+1/m); equality if and only if a positive scale and one common sign give the edge restriction; existence and positivity of both rays at every positive scale; lambda2=t, totalRes=C_m/t and the full native spectrum on every such restriction; disjointness of the two labelled rays even when their positive scales differ; interchange of the rays under hub exchange; and invariance of lambda2 and totalRes under arbitrary changes on nonedges. Applying the equality characterization and the universal ray conclusion gives the complete spectrum at every equality case.", DescribeRole.Definition),
            Node("result", "The sharp bound, all equality restrictions and their full spectra", "result",
                "The product bound, trace equality, positive spectral lower bound, harmonic reciprocal-eigenvalue formula, zero multiplicity, equality parameters, quadratic parameter roots and extremal lambda2/resistance values are direct applications of the original frozen optimizer suppliers. The additional argument proves reciprocal equality rigidity: for the m+1 positive native eigenvalues r_i, put q_i=r_i/t-1. Trace equality gives sum q_i=m-1. Each difference q_i/(1+q_i)-q_i/m is nonnegative, and product equality makes their sum zero. Hence each q_i is either zero or m-1; a positive total forces exactly one nonzero term. Consequently exactly one native eigenvalue is m*t and exactly m are t. This relation is used for every positive point on either equality ray. The construction remains on the original native matrix and harmonic resistance carriers throughout. These are repository-derived consequences of the selected K2m theory; no literature novelty or external open-problem resolution is asserted.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string name, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("fks-" + id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
}
