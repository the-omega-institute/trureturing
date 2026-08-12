using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class DecoherenceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Zurek =
        LibraryNoteRef.Create("D5/L/zurek2003decoherence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Composition and fixed points delimit the stipulated qubit phase-damping channel.",
        H("Phase-Damping Structure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("phase-damping-composition-multiplies-retention"),
                DeclarationHandle.Create("D5/S3/Quantum/Decoherence.phase_damping_composition"),
                H("Phase-damping composition multiplies retention"),
                StatementSource.FromAuthor(In(Seq(Forall, Sp, F.Id("c"), Comma, F.Id("d"), Sp, InMacro, Sp, OpenBracket, D(0), Comma, D(1), CloseBracket, Comma, Esc, Forall, Sp, Rho, Sp, InMacro, Sp, Operatorname, Grp(F.Id("QubitMatrix")), Comma, Esc, Operatorname, Grp(F.Id("phaseDamping")), Open, F.Id("c"), Comma, Operatorname, Grp(F.Id("phaseDamping")), Open, F.Id("d"), Comma, Rho, Close, Close, Eq, Operatorname, Grp(F.Id("phaseDamping")), Open, Operatorname, Grp(F.Id("dampingProduct")), Open, F.Id("c"), Comma, F.Id("d"), Close, Comma, Rho, Close))),
                AssessedProvenance.FromLiterature(Zurek),
                Blocks(Paragraph(Text(
                    "DampingCoefficient is the inhabited real interval [0,1], with zero as an explicit witness. For an arbitrary complex two-by-two matrix, no positivity, trace-one, or Hermiticity premise is assumed. Composing two stipulated phase-damping maps multiplies their real coherence-retention coefficients. The theorem does not derive a channel from a system-environment Hamiltonian, identify the repository ledger with an environment, identify bookkeeping with decoherence, or make a record rule select a pointer basis. Original certificate disposition: the source atoms' symbolic (1/2) * c0^N coherence law and fixed one-half populations are already formalized exactly by QubitWitnesses; the source atoms supply no fixed numeric c0 or N."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nontrivial-phase-damping-fixes-exactly-diagonal-matrices"),
                DeclarationHandle.Create("D5/S3/Quantum/Decoherence.phase_damping_fixed_iff_diagonal"),
                H("Nontrivial phase damping fixes exactly diagonal matrices"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("c"), Sp, InMacro, Sp, OpenBracket, D(0), Comma, D(1), CloseBracket, Comma, Esc, Forall, Sp, Rho, Sp, InMacro, Sp, Operatorname, Grp(F.Id("QubitMatrix")), Comma, Esc, F.Id("c"), Neq, Sp, D(1), Sp, Rightarrow, Sp, Open, Operatorname, Grp(F.Id("phaseDamping")), Open, F.Id("c"), Comma, Rho, Close, Eq, Rho, Sp, Leftrightarrow, Sp, Forall, Sp, F.Id("i"), Comma, F.Id("j"), Comma, Esc, F.Id("i"), Neq, Sp, F.Id("j"), Sp, Rightarrow, Sp, Rho, Underscore, Grp(F.Id("ij")), Eq, D(0), Close))),
                AssessedProvenance.FromLiterature(Zurek),
                Blocks(Paragraph(Text(
                    "For a retention coefficient in [0,1] whose real value is explicitly not one, an arbitrary complex two-by-two matrix is fixed exactly when every off-diagonal entry vanishes. No positivity, normalization, Hermiticity, density-state, environment, or record-generation premise is hidden. This identifies the fixed points of the stipulated map only; it does not prove that address records physically select this basis or that Fourier records select another basis. Original certificate disposition: the source atoms' symbolic (1/2) * c0^N law remains covered by the frozen QubitWitnesses theorem, with no fixed numeric c0 or N supplied by the atoms."))),
                DescribeRole.Theorem))));
}
