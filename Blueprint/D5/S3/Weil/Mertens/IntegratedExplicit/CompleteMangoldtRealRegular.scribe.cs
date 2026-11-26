using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class CompleteMangoldtRealRegularDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/IntegratedExplicit/CompleteMangoldtRealRegular.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real regularity of the meromorphic continuation of the complete Mangoldt transform",
        H("The continued complete Mangoldt transform"),
        Blocks(
            Describe.Lean(DescribeId.Create("continued-complete-mangoldt-transform"),
                DeclarationHandle.Create(Module + "continued"),
                H("The normalized expression at and away from one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Write Z(s) for riemannZeta₁(s), the entire pole-removed zeta function, "
                        + "and γ for the Euler–Mascheroni constant. Put "
                        + "N(s)=(((1+γ)s)−1)Z(s)−Z′(s). For s≠1 the numerator of continued(s) "
                        + "is N(s)/(s−1), and at s=1 that quotient is filled by N′(1). "
                        + "In both cases the denominator of continued(s) is sZ(s)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-mangoldt-meromorphic-real-regular"),
                DeclarationHandle.Create(Module + "continuation"),
                H("Meromorphicity, real regularity and agreement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The same function continued is meromorphic on Re(s)>0, analytic at "
                        + "each positive real point viewed as complex, and equals "
                        + "CompleteMangoldtLaurent.transform(s) at every complex s with Re(s)>1.")),
                    Paragraph(Text("The identities Z(1)=1 and Z′(1)=γ give N(1)=0. Local analytic "
                        + "factorization makes N(s)=(s−1)G(s) near 1. Differentiation gives G(1)=N′(1), "
                        + "so the filled quotient is analytic at 1 as well as away from 1. Dividing by "
                        + "the analytic denominator gives meromorphicity. The normalized zeta function "
                        + "is nonzero on the positive real axis, where s is also nonzero. The normalized "
                        + "logarithmic derivative identity gives agreement on Re(s)>1."))),
                DescribeRole.Theorem))));
}
