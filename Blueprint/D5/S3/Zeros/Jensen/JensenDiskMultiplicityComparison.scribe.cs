using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class JensenDiskMultiplicityComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Analytic units and the principal-log boundary primitive compare root multiset occurrences in the original isolating disk.",
        H("Polynomial occurrences in an isolating disk"),
        Blocks(Paragraph(Text("Let F be analytic near the original closed disk of radius delta>0, with exact order m>=1 at its center c and no other zero. If |P-F|<|F| on the sphere, P has no boundary root and exactly m root occurrences in the disk.")),
        Paragraph(Text("Glue the local unit V to F(z)/(z-c)^m by setting U(c)=V(c). It is analytic and nonzero on the full closed disk, with F(z)=(z-c)^m*U(z). Its logarithmic derivative contributes zero to the circle integral by Cauchy-Goursat; the centered factor contributes 2*pi*i*m.")),
        Paragraph(Text("The boundary quotient P/F lies in the unit ball around 1, hence in the principal-log slit plane. Differentiating log(P/F) gives P'/P-F'/F. The circle primitive theorem makes its integral zero, with continuous boundary integrands supplying integrability.")),
        Paragraph(Text("The polynomial logarithmic derivative is summed over the root multiset with repetitions. Every occurrence inside contributes 2*pi*i; every occurrence outside contributes zero. The nonzero factor 2*pi*i cancels, yielding the original-disk occurrence count used by the source fixed-window clause. This is the classical argument-principle proof of the Rouche disk comparison; it carries no literature originality claim.")))));
}
