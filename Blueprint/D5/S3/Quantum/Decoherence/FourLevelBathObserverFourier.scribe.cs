using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class FourLevelBathObserverFourierDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Decoherence/FourLevelBathObserverFourier.";
    private static readonly LibraryNoteRef Wheeler =
        LibraryNoteRef.Create("D5/L/Observer/wheeler1999informationphysics");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Fourier measurement on the reference and an outcome-dependent bath measurement recover the label.",
        H("One-way Fourier readout of the purified bath"),
        Blocks(
            Paragraph(Text(
                "Use the coherent preparation of the fixed-bath observer and keep access to both systems. "
                + "Measure the reference in the four-point Fourier basis, send its outcome k to the bath "
                + "observer, and use the corresponding phase-adjusted projectors on the bath. The "
                + "measurement model grants phase-sensitive control on each side.")),
            Theorem("reference-effect-projection", "referenceEffect_projection", "Reference projectors",
                "Each Fourier column defines a self-adjoint projection in the reference space."),
            Theorem("reference-effect-complete", "referenceEffect_complete", "Four reference outcomes",
                "The four Fourier basis projectors sum to the reference identity."),
            Theorem("fourier-analysis-effect", "fourierAnalysis_effect", "Effect of the partial inner product",
                "The branch operator I_B ⊗ ⟨fₖ| has adjoint product I_B ⊗ |fₖ⟩⟨fₖ|."),
            Theorem("fourier-columns-isometry", "fourierColumns_isometry", "Orthogonal bath columns in each branch",
                "The conjugated Fourier character is a diagonal unitary on B and preserves the "
                + "weighted column Gram matrix."),
            Theorem("fourier-branch", "fourierBranch_eq", "The actual subnormalized bath branch",
                "On basis input i, reference outcome k leaves 1/4 times the rank-one operator of "
                + "the phase-adjusted bath column for i."),
            Theorem("fourier-outcome-uniform", "fourier_outcome_uniform", "Uniform outcome on the reference",
                "Each k has probability 1/4 for every input label under the weighted Gram identity."),
            Theorem("fourier-decoder-born", "fourier_decoder_born", "Exact label readout after one message",
                "The joint probability of (k,o) is 1/4 when o reports the input label and zero "
                + "otherwise, including the complementary outcome. Thus every k yields the correct "
                + "decoded label. For a prescribed j, testing whether the bath result is j gives "
                + "the corresponding yes-or-no answer.", Wheeler))));

    private static DocumentBlock.Describe Theorem(
        string id, string name, string title, string statement, params LibraryNoteRef[] sources) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(sources),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
