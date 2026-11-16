using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.PermutationCriteria;

internal sealed class BellWitnessesDocument : IScribeDocumentDefinition
{
    private static DocumentBlock.Describe Item(string name, string title, string body,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("permutation-bell-witnesses-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/PermutationCriteria/BellWitnesses." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(body))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Which correlated basis bits survive in each row or column string of a tensor-index permutation.",
        H("Bell witness coordinate kernels"), Blocks(
            Item("sidePos", "A row or column position", "For a Boolean side and a party k, sidePos is the ket position when side is true and the bra position otherwise.", DescribeRole.Definition),
            Item("sideSelected", "Selection of one matrix side", "A flat position is selected when it is even for side true, or odd for side false.", DescribeRole.Definition),
            Item("sideImage", "A reshaped correlated string", "Choose a set S of parties, one row bit and one column bit. Form the corresponding two basis strings, interleave them, pull them back by the inverse permutation, and project onto the selected output side.", DescribeRole.Definition),
            Item("sideImage_kernel", "Exact bit kernel on either side", "For every local dimension at least two, support set S, position permutation and selected side, two reshaped strings agree exactly when their first bits agree whenever any ket position from S lands on that side, and their second bits agree whenever any bra position from S lands on that side. Empty S and zero parties are allowed."),
            Item("permute_bellWitness", "The four permuted Bell entries", "For all parties i,j, local dimension at least two and position permutation, the permuted Bell witness is the sum of the four matrix units indexed by its reshaped row and column strings, each with coefficient one half."),
            Item("bellWitness_traceNorm", "The Bell separation values", "For every local dimension at least two, parties i,j and permutation sigma, the permuted Bell witness has trace norm one, twice the square root of one half, or two according as the paired row-side labels of i,j have Hamming distance zero, one, or two. The statement also includes i equal to j, when the distance is zero."),
            Item("dependent_pairDistance", "Dependence preserves paired-label distance", "If two permutations have equal trace norms on every positive trace-one state in local dimension at least two, then the Hamming distance between the paired row-side labels of any two parties agrees for the two permutations. The three Bell norm values are distinct, so the Bell witness detects each of the three distances."))));
}
