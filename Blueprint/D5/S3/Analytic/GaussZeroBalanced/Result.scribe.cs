using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.GaussZeroBalanced;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp zero-balanced Gauss quotient classifications", H("The two parameter thresholds"), Blocks(
            Describe.Lean(DescribeId.Create("gauss-zero-balanced-result"),
                DeclarationHandle.Create("D5/S3/Analytic/GaussZeroBalanced/Result.result"),
                H("The two classifications"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every positive real a and b, the derivative in b of quot a b x is strictly negative for every x in (0,1) if and only if b<=sqrt(a(a+1)). For every real a in (0,1), ineq17 a r holds for every r in (0,1) if and only if a>=3/7.")),
                    Paragraph(Text("The first classification follows from the parameter variational equation, the strict Riccati certificate and the initial mixed derivative. For the second classification, the difference w=f(a,b1)-f(a,b2), with 0<b1<b2, satisfies x w prime+P w=(b2-b1)(a squared t f(a,b2) squared/((a+b1)(a+b2))-(1-f(a,b2))), where P=a+b1+ab1 t(f(a,b1)+f(a,b2))/(a+b1) and t=x/(1-x). The certificate makes the source strictly positive when b1 b2<=a(a+1). The singular endpoint comparison yields w>0. Conversely, w>0 on the interval forces its initial slope to be nonnegative, hence b1 b2<=a(a+1). Substitution b1=1-a and b2=3/2-a gives a(a+1)-b1 b2=(7a-3)/2, so the threshold is exactly 3/7."))),
                DescribeRole.Theorem))));
}
