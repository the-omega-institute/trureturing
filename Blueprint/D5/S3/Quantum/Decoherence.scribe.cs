using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class DecoherenceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Zurek =
        LibraryNoteRef.Create("D5/L/zurek2003decoherence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Quantum/Decoherence",
            "Composition and fixed points delimit the stipulated qubit phase-damping channel."),
        H("Phase-Damping Structure"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("phase-damping-composition-multiplies-retention"),
                DescribeKind.Theorem,
                H("Phase-damping composition multiplies retention"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Quantum/Decoherence.phase_damping_composition")),
                DescribeProvenance.LiteratureAttested(Zurek),
                Blocks(Paragraph(Text(
                    "DampingCoefficient is the inhabited real interval [0,1], with zero as an explicit witness. For an arbitrary complex two-by-two matrix, no positivity, trace-one, or Hermiticity premise is assumed. Composing two stipulated phase-damping maps multiplies their real coherence-retention coefficients. The theorem does not derive a channel from a system-environment Hamiltonian, identify the repository ledger with an environment, identify bookkeeping with decoherence, or make a record rule select a pointer basis. Original certificate disposition: the source atoms' symbolic (1/2) * c0^N coherence law and fixed one-half populations are already formalized exactly by QubitWitnesses; the source atoms supply no fixed numeric c0 or N."))),
                LatexStatement.Create(@"$\forall c,d \in [0,1],\ \forall \rho \in \operatorname{QubitMatrix},\ \operatorname{phaseDamping}(c,\operatorname{phaseDamping}(d,\rho))=\operatorname{phaseDamping}(\operatorname{dampingProduct}(c,d),\rho)$")),
            new DocumentBlock.Describe(
                DescribeId.Create("nontrivial-phase-damping-fixes-exactly-diagonal-matrices"),
                DescribeKind.Theorem,
                H("Nontrivial phase damping fixes exactly diagonal matrices"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Quantum/Decoherence.phase_damping_fixed_iff_diagonal")),
                DescribeProvenance.LiteratureAttested(Zurek),
                Blocks(Paragraph(Text(
                    "For a retention coefficient in [0,1] whose real value is explicitly not one, an arbitrary complex two-by-two matrix is fixed exactly when every off-diagonal entry vanishes. No positivity, normalization, Hermiticity, density-state, environment, or record-generation premise is hidden. This identifies the fixed points of the stipulated map only; it does not prove that address records physically select this basis or that Fourier records select another basis. Original certificate disposition: the source atoms' symbolic (1/2) * c0^N law remains covered by the frozen QubitWitnesses theorem, with no fixed numeric c0 or N supplied by the atoms."))),
                LatexStatement.Create(@"$$\forall c \in [0,1],\ \forall \rho \in \operatorname{QubitMatrix},\ c\neq 1 \Rightarrow (\operatorname{phaseDamping}(c,\rho)=\rho \Leftrightarrow \forall i,j,\ i\neq j \Rightarrow \rho_{ij}=0)$$")))));
}
