using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class PhaseLawDyadicCoercivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Count-free dyadic phase coercivity.",
        H("Count-free dyadic phase coercivity"),
        Blocks(Describe.Lean(
            DescribeId.Create("phaselawdyadiccoercivity"),
            DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/PhaseLawDyadicCoercivity.phase_law_dyadic_coercivity"),
            H("Count-free dyadic phase coercivity"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let I be any index type with nonnegative summable weights a(i) "
                    + "and positive frequencies gamma(i). Write delta(t)=sum "
                    + "2*a(i)*(1-cos(gamma(i)*t)). For fixed alpha>0, B>=0 and "
                    + "0<T0<=exp(-1), assume the phase estimate "
                    + "abs(delta(t)-alpha*t^2*log(1/t)^2)<=B*t^2*(log(1/t)+1) "
                    + "for every 0<t<=T0.")),
                Paragraph(Text("Put Kinv=2*alpha+3*B. For every Y>=16/T0, both strict and "
                    + "closed fourth moments are at most 64*Kinv*Y^2*(log(Y)+1), "
                    + "and both strict and closed tail masses are at most "
                    + "32*Kinv*Y^(-2)*(log(Y)+1). No moment or tail estimate is assumed.")),
                Paragraph(Text("The exact defect 4*delta(u/2)-delta(u) equals the "
                    + "nonnegative sum 4*a(i)*(1-cos(gamma(i)*u/2))^2. Its upper bound "
                    + "Kinv*u^2*(log(1/u)+1) and the cosine remainder 5/96 force the "
                    + "fourth moment. For high frequencies average the squared kernel "
                    + "over [0,8/Y]. Its mean is at least 15/16. Integrate only finite "
                    + "high subsums under a constant majorant and then take their supremum. "
                    + "Thus no infinite sum-integral interchange or improper logarithmic "
                    + "antiderivative is needed. These bounds supply the Taylor split "
                    + "for phase inversion while preserving arbitrary early and repeated "
                    + "frequencies, zero weights, and infinite bounded-frequency clouds."))),
            DescribeRole.Theorem))));
}
