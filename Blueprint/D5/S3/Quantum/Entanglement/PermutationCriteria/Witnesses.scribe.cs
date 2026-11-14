using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.PermutationCriteria;

internal sealed class WitnessesDocument : IScribeDocumentDefinition
{
    private static DocumentBlock.Describe Item(string name, string title, string body,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("permutation-witnesses-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/PermutationCriteria/Witnesses." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(body))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Density operators used to distinguish tensor-index permutation trace norms.",
        H("Single-party and Bell witnesses"), Blocks(
            Item("bitPattern", "Correlated basis strings", "For local dimension d at least two, a subset S of the parties and a bit t, bitPattern is the computational basis string equal to t on S and zero off S.", DescribeRole.Definition),
            Item("witnessEmbedding", "The two-string inclusion", "For nonempty S, witnessEmbedding includes the all-zero string and the string with ones on S as two orthonormal computational basis vectors; all remaining coordinates are zero.", DescribeRole.Definition),
            Item("singleWitness", "The single-party mixed state", "For party i, singleWitness is the equal mixture of the all-zero string and the string with one at i and zero at all other parties. It is the maximally mixed qubit state at i tensor the zero pure state at every other party.", DescribeRole.Definition),
            Item("singleWitness_isDensity", "The mixed witness is a density operator", "For every number of parties, local dimension at least two and chosen party i, singleWitness is positive semidefinite and has trace one. The two-string inclusion is isometric and preserves the trace of its half-identity block."),
            Item("bellWitness", "The embedded Bell state", "For parties i and j, bellWitness is the pure equal superposition of the all-zero string and the string with ones on the set containing i and j. When i and j are distinct, this is the two-party Bell state tensor zero pure states on the other parties.", DescribeRole.Definition),
            Item("bellWitness_isDensity", "The Bell witness is a density operator", "For every number of parties, local dimension at least two and parties i,j, bellWitness is positive semidefinite and has trace one. Distinctness of i and j is not needed for this density assertion."),
            Item("singleWitness_eq", "Two diagonal half entries", "singleWitness equals the sum of the two matrix units at its correlated zero and one basis strings, each with coefficient one half."),
            Item("bellWitness_eq", "Four Bell half entries", "bellWitness equals the sum of all four matrix units between its correlated zero and one basis strings, each with coefficient one half."),
            Item("singleWitness_traceNorm", "The mixed-state separation", "For every local dimension at least two, party i and position permutation sigma, the trace norm of the permuted singleWitness is the square root of one half when the ket and bra positions of i are sent to the same output side, and one otherwise. The two nonzero entries are a column, a row, or a pair in distinct rows and columns."),
            Item("dependent_sameSide", "Dependence preserves local side status", "If two permutations have equal trace norms on every positive trace-one state in local dimension at least two, then at each party their ket and bra positions lie on the same output side for one permutation if and only if they do so for the other. The positive square root of one half differs from one, so a single-party mixed witness separates the two cases."))));
}
