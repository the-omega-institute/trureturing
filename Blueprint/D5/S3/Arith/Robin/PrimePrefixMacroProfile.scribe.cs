using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class PrimePrefixMacroProfileDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal complete-prefix macro profile has a strict quantitative decrease on the positive axis.",
        H("The Complete Prime-Prefix Macro Profile"),
        Blocks(
            Paragraph(Text(
                "Write Q(u)=u*Re(zeta(1+u)) and C=exp(Euler's constant). The macro profile "
                + "is C/Q(u). The domain is the entire positive real axis.")),
            Describe.Lean(
                DescribeId.Create("prime-prefix-macro-profile-strong-decrease"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PrimePrefixMacroProfile.result"),
                H("A strict decrease bound for the literal macro profile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every 0<a<b, the profile drop C/Q(a)-C/Q(b) is strictly greater "
                        + "than C*(b-a)/(2*Q(a)*Q(b)).")),
                    Paragraph(Text(
                        "The existing Fermi Mellin formula is converted to a complete Bose integral "
                        + "after paying both Gamma majorants on the whole positive axis. The exact "
                        + "doubled-scale identity and a positive cancellation factor give the literal "
                        + "Q integral. The Gamma density ratio crosses once. Equal total masses and "
                        + "first moments, together with the strictly increasing remainder "
                        + "chi(t)=t/(1-exp(-t))-t/2, imply Q(b)-Q(a)>(b-a)/2. Positive denominators "
                        + "then yield the profile bound.")),
                    Paragraph(Text(
                        "The Fermi supplier retains its Sanftenberg (2026), Apache-2.0 provenance. "
                        + "Gamma and Bose representations are classical (NIST DLMF 5.9.1 and 25.5.1). "
                        + "The finite-prefix Euler error, eventual crossing, matched damping constant, "
                        + "and complete Robin pairing require further proofs."))),
                DescribeRole.Theorem))));
}
