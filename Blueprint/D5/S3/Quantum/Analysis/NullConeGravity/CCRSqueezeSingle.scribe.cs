using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.NullConeGravity;

internal sealed class CCRSqueezeSingleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/satishchandransorce2026nulllocal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A one-mode squeezed vacuum in the occupation representation and its Weyl expectation.",
        H("The one-mode squeezed vacuum"),
        Blocks(
            Paragraph(Text("This construction supplies the one-mode vectors used in the Gaussian "
                + "excitability problem of Satishchandran and Sorce. On the real line the coherent "
                + "vectors become Gaussian packets with the same Gram matrix. Their span is dense "
                + "because testing at imaginary labels detects the Fourier transform of the "
                + "Gaussian-weighted orthogonal vector.")),
            Entry("single-basis", "singleModeBasis", "Canonical one-mode basis",
                "The basis of the complex one-particle line is indexed by Unit and consists of one.",
                DescribeRole.Definition),
            Entry("single-basis-value", "singleModeBasis_apply", "Value of the basis vector",
                "The single basis vector has value one."),
            Entry("single-basis-coordinate", "singleModeBasis_repr", "One-particle coordinate",
                "The unique basis coordinate of a complex input is the input itself."),
            Entry("squeezed-vacuum", "squeezeVacuum", "One-mode squeezed vacuum",
                "For each real r, pull back the normalized Gaussian of width exp(2r) under the "
                + "coherent isometry. Its position wavefunction is the vacuum Gaussian dilated "
                + "by exp(r), with amplitude multiplied by exp(r/2).", DescribeRole.Definition),
            Entry("squeezed-vacuum-zero", "squeezeVacuum_zero", "Zero squeeze",
                "At r = 0 the Gaussian is the image of the Fock vacuum."),
            Entry("squeezed-vacuum-norm", "squeezeVacuum_norm", "Unit norm",
                "The Gaussian integral of the squared wavefunction equals one for every real r."),
            Entry("squeezed-vacuum-overlap", "squeezeVacuum_vacuum_inner", "Overlap with the vacuum",
                "The vacuum overlap is 1/√cosh(r). The average of the two Gaussian widths is "
                + "exp(r) cosh(r), and the amplitude factor cancels its exp(r) contribution."),
            Entry("squeezed-vacuum-weyl", "squeezeVacuum_weyl_inner", "One-mode Weyl expectation",
                "For z = x + iy the expectation is exp(−(exp(2r) x² + exp(−2r) y²)/2). "
                + "Coherent pairings identify the displaced Gaussian, and the quadratic Gaussian "
                + "integral cancels the mixed phase."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(statement))), role);
}
