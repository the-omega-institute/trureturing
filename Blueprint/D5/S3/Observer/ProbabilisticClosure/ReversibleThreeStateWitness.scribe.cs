using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class ReversibleThreeStateWitnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A continuous two-parameter reversible stochastic family has a fixed equilibrium but a sharp nonzero projected memory term.",
        H("Equal Equilibria Do Not Determine Path Kinetics"),
        Blocks(
            Paragraph(Text("The three-state nearest-neighbor matrix has off-diagonal parameters a and b, with nonnegative entries when a,b are nonnegative and a+b is at most one. The observation merges states zero and one. Its matrix is the actual conditional expectation for the uniform equilibrium measure.")),
            Describe.Lean(
                DescribeId.Create("stochastic-and-stationary"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/ReversibleThreeStateWitness.stochastic_and_stationary"),
                H("One stationary distribution for the entire valid family"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The source proves entrywise nonnegativity, unit row sums, invariance of the complete uniform stationary vector, and symmetry. For strictly positive a and b and sum less than one, these are ordinary communicating stochastic examples rather than invalid transition matrices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exact-memory-entry"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/ReversibleThreeStateWitness.exact_memory_entry"),
                H("A visible two-step discrepancy equals b squared over two"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The (2,2) entry of the compression defect is exactly b^2/2, computed from the concrete matrices. All equilibrium weights can be equal while this kinetic discrepancy varies. The formula also quantifies this single entry for small coupling; no long-horizon approximation bound is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("closed-iff-cross-edge-zero"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/ReversibleThreeStateWitness.closed_iff_cross_edge_zero"),
                H("Small cross-coupling is not exact closure"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Using the general reversible Gram criterion, the observation space is invariant exactly when b is zero. An arbitrarily small but nonzero cross-fiber coupling still leaves memory under projection. This does not deny useful approximate slow models; it identifies their missing approximation obligation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("no-equilibrium-only-transition-decoder"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/ReversibleThreeStateWitness.no_equilibrium_only_transition_decoder"),
                H("Equilibrium data cannot recover even one transition entry"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two interior parameter choices have identical full stationary vectors but different K(1,2). Hence no function of that stationary vector alone returns the entry on this family. This concerns equilibrium-only information. A force field together with masses, friction, noise, integrator and physical clock carries additional dynamical information that is not excluded by the theorem."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/ProbabilisticClosure/ReversibleProjectionMemory")),
        ]));
}
