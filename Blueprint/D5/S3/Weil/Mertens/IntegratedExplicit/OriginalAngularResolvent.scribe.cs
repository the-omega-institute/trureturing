using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class OriginalAngularResolventDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact angular resolvent", H("The exact angular resolvent"),
        Blocks(
            Paragraph(Text("The Fourier inversion and transform suppliers are imported from Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 under Apache 2.0. Fourier inversion is due to Sebastien Gouezel; the Fourier transform and improper exponential integrals are due to David Loeffler. Their upstream proofs are imported. The angular rescaling and the following proof chain are repository derivations.")),
            Describe.Lean(DescribeId.Create("original-angularresolvent-angular-resolvent"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalAngularResolvent.angular_resolvent"),
                H("The normalized complex integral"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real lag s, the literal complex integrand exp(I*w*s)/(1+4*w^2) is integrable, and (1/(2*pi))*integral exp(I*w*s)/(1+4*w^2)=exp(-abs(s)/2)/4. The proof integrates exp(-abs(t)/2) separately on its two half-lines, obtains its rational Fourier transform, applies Fourier inversion, then changes variables w=2*pi*xi. The statement includes s=0."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-angularresolvent-cosine-resolvent"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/OriginalAngularResolvent.cosine_resolvent"),
                H("The cosine formula"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real part of the same integrable complex kernel gives the normalized cosine integral exp(-abs(s)/2)/4 for every real s. The finite-measure spectral construction uses angular_resolvent to obtain the complex resolvent identity, then takes real parts."))),
                DescribeRole.Theorem))));
}
