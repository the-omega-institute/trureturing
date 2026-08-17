using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class CoherenceDecayDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Zurek =
        LibraryNoteRef.Create("D5/L/zurek2003decoherence");

    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Strict phase damping drives equal-superposition coherence to zero.",
            H("Equal-Superposition Coherence Decay"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("equal-superposition-coherence-tends-to-zero"),
                    DeclarationHandle.Create(
                        "D5/S3/Quantum/Decoherence/CoherenceDecay."
                        + "equal_superposition_coherence_tendsto_zero"),
                    H("Equal-superposition coherence tends to zero"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Lim, Underscore, Grp(F.Id("N"), To, Infty), Sp,
                        Operatorname, Grp(F.Id("phaseDampingIterate")),
                        Open, F.Id("c"), Comma, F.Id("N"), Comma,
                        Operatorname, Grp(F.Id("equalSuperpositionDensity")),
                        Close, Underscore, Grp(D(0, 1)), Sp, Eq, Sp, D(0)))),
                    AssessedProvenance.FromLiterature(Zurek),
                    Blocks(Paragraph(Text(
                        "For a real phase-damping retention coefficient c in [0,1), the exact "
                        + "finite-step certificate identifies the equal-superposition off-diagonal "
                        + "entry with (1/2)c^N. Pinned Mathlib's geometric-power limit then sends "
                        + "that entry to zero. This closes only the source atom's exact coherence-"
                        + "decay clause; it does not derive the channel from a Hamiltonian or "
                        + "formalize the atom's center, pointer-basis, or redundancy claims."))),
                    DescribeRole.Theorem))));
}
