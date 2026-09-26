using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Thermal;

internal sealed class CountableDiagonalGibbsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct the maximal diagonal Hamiltonian on actual l2, characterize its adjoint graph, and construct its Gibbs operator by an absolutely summable rank-one series. These source candidates have no kernel-verification claim.",
        H("Countable Diagonal Hamiltonians and Gibbs Operators"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("energydomain-dense"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/CountableDiagonalGibbs.energyDomain_dense"),
                H("energyDomain dense"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every canonical finite-support vector belongs to the constructed maximal domain; the actual l2 finite-support expansion proves density."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adjoint-graph-iff"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/CountableDiagonalGibbs.adjoint_graph_iff"),
                H("adjoint graph iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The adjoint graph is defined by testing inner products against every domain vector. Basis tests recover the full maximal domain and operator value, rather than only formal symmetry."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("diagonalnuclear-apply"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/CountableDiagonalGibbs.diagonalNuclear_apply"),
                H("diagonalNuclear apply"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The bounded operator is defined by an absolutely convergent rank-one operator series. Continuity of evaluation then proves its diagonal coordinate action."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("diagonal-nuclear-expansion"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/CountableDiagonalGibbs.diagonal_nuclear_expansion"),
                H("diagonal nuclear expansion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both the operator-valued HasSum statement and the summability of the norms of the normalized rank-one terms are proved."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("oscillator-hassum"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/CountableDiagonalGibbs.oscillator_hasSum"),
                H("oscillator hasSum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact positive oscillator energy, including the zero-point term, yields the infinite geometric Gibbs sum at every positive inverse temperature."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gibbs-nuclear-expansion"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/CountableDiagonalGibbs.gibbs_nuclear_expansion"),
                H("gibbs nuclear expansion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Gibbs operator acts on infinite l2. Its explicit nuclear decomposition is constructed; no finite truncation is substituted for this series."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gibbs-canonical-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/CountableDiagonalGibbs.gibbs_canonical_trace"),
                H("gibbs canonical trace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Evaluate the trace in the fixed complete canonical basis. General basis independence and the unitary identification with an original differential Hamiltonian are separate obligations."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("oscillator-unbounded"),
                DeclarationHandle.Create("D5/S3/Quantum/Thermal/CountableDiagonalGibbs.oscillator_unbounded"),
                H("oscillator unbounded"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every proposed real norm bound, an explicitly constructed domain vector of norm one has Hamiltonian output norm strictly larger."))), DescribeRole.Theorem))));
}
