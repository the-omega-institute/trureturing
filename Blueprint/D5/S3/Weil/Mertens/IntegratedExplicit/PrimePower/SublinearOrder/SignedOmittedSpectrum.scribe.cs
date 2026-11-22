using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class SignedOmittedSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed sums over omitted root degrees",
        H("Frequency cutoff in the actual zero-occurrence sum"),
        Blocks(
            Paragraph(Text("Fix q=m+1 and the omitted degrees 2n≥q. After extracting "
                + "exp(−(1/2−1/q)u), the normalized mode has envelope exp(−u/q+u/(2n)), "
                + "root coefficient −n/(ρ(n−ρ)), and phase exp(i Im(ρ)u/n).")),
            Paragraph(Text("For each low occurrence, apply finite complex Abel summation in "
                + "the degree. The mode differences split into increments of the decreasing "
                + "envelope, the root coefficient and the phase. Telescoping the envelope "
                + "and the coordinates u/n gives total variation of order "
                + "(1+|Im(ρ)|u/q)/|ρ|.")),
            Paragraph(Text("On the complementary bins use the square-mass estimate with "
                + "the mask outside the cutoff. Finite occurrence estimates pass to the "
                + "summable series at each degree, keeping the analytic multiplicities. "
                + "When q≤u≤q^(29/28), the cutoff floor(q^(1/7)) gives a q^(27/28) "
                + "coefficient under a q^(3/4) ordinary Möbius prefix bound. For larger u, "
                + "the uncut spacing estimate supplies the same power.")))));
}
