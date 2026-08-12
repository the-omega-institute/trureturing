using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class OnticStateCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("States have a lossless five-coordinate presentation with a canonical prime-ledger code.",
        H("Canonical Coordinates for States"),
        Blocks(
            Describe.Lean(DescribeId.Create("canonical-five-coordinates-are-lossless"),
                DeclarationHandle.Create(
                                    "D5/S1/Dynamics/OnticStateCoordinates."
                                    + "canonical_five_coordinates_bijective"),
                H("Canonical five coordinates are lossless"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Operatorname, Grp(F.Id("Bijective")), Open,
                                    Operatorname, Grp(F.Id("onticStateEquivCoordinates")), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "A state records a finitely supported prime-exponent ledger, a phase "
                                        + "coordinate, a finite readout, and a ledger coordinate. Its fifth "
                                        + "coordinate is the positive-natural code determined by the canonical "
                                        + "prime-axis encoding. The formal coordinate type carries an equality "
                                        + "proof tying that code to the prime ledger, so an arbitrary or stale "
                                        + "code cannot inhabit the representation. Forgetting the dependent code "
                                        + "and recomputing it gives mutually inverse maps, which makes the source "
                                        + "atom's single state definition an explicit lossless equivalence.")),
                                    Paragraph(Text(
                                        "The pinned library was searched before construction. It provides "
                                        + "Equiv.bijective, Equiv.apply_eq_iff_eq, and Equiv.subtypeEquiv, but no "
                                        + "five-coordinate state equivalence tied to the repository's canonical "
                                        + "prime-axis encoder. The Lean declaration is therefore a new local "
                                        + "constrained-coordinate construction using the existing "
                                        + "D5.S1.Digit.primeAxisEncoding, with only the final bundled bijectivity "
                                        + "step delegated to Mathlib. The source atom carries no numerical "
                                        + "certificate."))),
                DescribeRole.Theorem))));
}
