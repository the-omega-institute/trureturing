using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockAllStatePhysicalLocalityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original arbitrary-state native two-sheet physical locality",
        H("Original arbitrary-state native two-sheet physical locality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticehalffockallstatephysical-locality"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockAllStatePhysicalLocality.Ytw_physical_locality"),
                H("Every original pair of source states admits a uniform physical clearing order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every lattice D with unit Gram determinant and every original source pair a and b, there exists a natural order N such that the actual bosonic commutator of Ytw coefficients is annihilated by the binomial sum with cover shifts E minus two times N minus i and F minus two times i, for all signed E and F and all actual tensor target vectors. There is no target cutoff or positive-signature hypothesis."))),
                DescribeRole.Theorem),
            Paragraph(Text("The proof first transports ordinary physical locality through the exact shifted lift, with both parity cases retained. Finite field addition takes maxima of genuine killing orders, while scalar multiplication and original even Corr shifts preserve locality. Each original normalWord is reconstructed from its two physical words. The final proof consumes Ytw_enumerated_expansion with the actual finite charge, Corr-shift and supported monomial sets, then the existing delta binomial identity. No sharp weight bound is asserted.")),
            Paragraph(Text("The owning Reg mirror binds the entire original telescope and the literal finite commutator readout. The contract-obligation types are not completed four-slot registrations; variation, sensitivity and observational dependence are separate pending admission requirements. Kernel verification, source admission, required CI, remote publication and merge are distinct states.")),
            Paragraph(Text("Physical two-sheet locality does not establish full twisted Jacobi, a Moonshine extension, full anomaly/fusion theory, a no-ghost theorem beyond the separately supplied branches, or a complete string/AdS mathematical bridge. Those original goals remain active and open.")))));
}
