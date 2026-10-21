using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KummerRatio;

internal sealed class TransformDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflection of the real argument and complementary upper parameter in the Kummer series.",
        H("Kummer reflection"), Blocks(
            Describe.Lean(DescribeId.Create("kummer-parameter-reflection"),
                DeclarationHandle.Create("D5/S3/Analytic/KummerRatio/Transform.kummer_transform"),
                H("Complementary upper parameters"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real s, positive c and real x, M(s;c;x)=exp(x) M(c-s;c;-x). There is no positivity restriction on the upper parameter s or on the reflected upper parameter c-s.")),
                    Paragraph(Text("The finite binomial sum of (-1)^k times choose(n,k) times (t)_k/(c)_k equals (c-t)_n/(c)_n. Splitting the binomial coefficients at rank n+1 proves this identity by induction, with a simultaneous shift of t and c. Applying it at t=c-s identifies each coefficient in the product of the exponential series and M(c-s;c;-x). Both series converge absolutely for every real x, so their Cauchy product gives the function identity."))),
                DescribeRole.Theorem))));
}
