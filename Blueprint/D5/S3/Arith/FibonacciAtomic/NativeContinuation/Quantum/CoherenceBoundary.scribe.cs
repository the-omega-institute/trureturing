using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.NativeContinuation.Quantum;

internal sealed class CoherenceBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/NativeContinuation/Quantum/CoherenceBoundary.";

    private static DocumentBlock Theorem(string id, string declaration, string title, params string[] prose) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(prose.Select(p => (DocumentBlock)Paragraph(Text(p))).ToArray()), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The diagonal hidden-joint readout bounds, but does not determine, the corresponding coherence.",
        H("FIB hidden-joint coherence boundary"),
        Blocks(
            Paragraph(Text(
                "The existing finite FIB instrument has a branch whose diagonal input trace is the "
                + "source coordinate 25. This document extends that boundary to arbitrary matrix inputs "
                + "and records the positivity constraint on the 2-4 off-diagonal entry. The source "
                + "coordinate rho(4,4) is the hidden joint mass kappa; the off-diagonal entry rho(2,4) "
                + "is a separate coherence coordinate.")),
            Theorem("coherence-radius-bound", "coherence_radius_bound", "Positivity bounds the coherence radius",
                "For every positive semidefinite five-state matrix, the squared magnitude of the 2-4 "
                + "coherence is at most the product of the two corresponding diagonal masses. This is "
                + "a principal-minor consequence of positivity and supplies only a radius bound; it does "
                + "not determine a phase or a nonzero coherence."),
            Theorem("arbitrary-branch-trace-reads-diagonal", "arbitrary_branch_trace_reads_diagonal", "The odd-rejection branch is diagonal-blind",
                "For an arbitrary five-state matrix input, the concrete odd-rejection Kraus branch has "
                + "trace equal to its source diagonal entry 4. Its off-diagonal entries, including the "
                + "2-4 coherence, do not enter this trace."),
            Theorem("hidden-joint-bounds-coherence", "hidden_joint_bounds_coherence", "The hidden joint mass leaves a coherence fibre",
                "Combining the two exact statements gives the current quantum boundary: the branch "
                + "reads rho(4,4), while positivity restricts rho(2,4) to a disk of squared radius at "
                + "most rho(2,2) times rho(4,4). The branch record alone therefore cannot recover the "
                + "phase or select a point in that coherence fibre."),
            Paragraph(Text(
                "This is a finite matrix statement for the stipulated instrument. It does not assert "
                + "physical state preparation, a Fock-space realization, Hamiltonian dynamics, phase "
                + "tomography, or gravitational sourcing. A phase-sensitive reference and a separate "
                + "non-diagonal readout remain open.")))));
}
