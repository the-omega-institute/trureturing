using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.WallisRemainder;

internal sealed class StieltjesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict inequalities for Stieltjes transforms of positive probability laws.",
        H("Stieltjes remainder monotonicity"), Blocks(
            Describe.Lean(DescribeId.Create("stieltjes-resolvent-integrability"),
                DeclarationHandle.Create("D5/S3/Analytic/WallisRemainder/Stieltjes.integrable_resolvent"),
                H("Integrability of the positive resolvent"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For z>0 and a probability measure concentrated on positive reals, v maps to 1/(z+v) is integrable. Measurability and the uniform bound 1/z give the result without a moment assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("stieltjes-jensen-remainder-monotonicity"),
                DeclarationHandle.Create("D5/S3/Analytic/WallisRemainder/Stieltjes.strictMonoOn_jensenRemainder"),
                H("Strict increase of the normalized Jensen remainder"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let M be a probability measure on the real line concentrated on strictly positive values. Its Stieltjes transform is S(z)=integral 1/(z+v) dM(v). Let a be its finite mean, and suppose the centered second moment s=integral (v-a)^2 dM(v) is finite and strictly positive. Then z^3(S(z)-1/(z+a))/s is strictly increasing for z>0.")),
                    Paragraph(Text("Centering gives S(z)-1/(z+a)=integral ((v-a)^2/(z+v)) dM(v)/(z+a)^2. Inside the resulting normalized integral, the kernel is the product (z/(z+a))^2 times z/(z+v). Both factors increase, and the kernel increases strictly for every positive v. Positive centered second moment ensures that the multiplier (v-a)^2 does not vanish almost everywhere."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("stieltjes-inverse-offset-monotonicity"),
                DeclarationHandle.Create("D5/S3/Analytic/WallisRemainder/Stieltjes.strictMonoOn_inv_stieltjes_sub"),
                H("Strict increase of the inverse transform offset"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every probability measure M concentrated on positive reals and not concentrated at any single point, the function 1/S(z)-z is strictly increasing for z>0. No moment assumption is required.")),
                    Paragraph(Text("For 0<x<y put q=S(y), d=y-x, and t=1-dq. Positivity of the support gives q>0 and t>0. The pointwise identity 1/(x+v)-q/t-(1/(y+v)-q)/t^2 = d(1/(y+v)-q)^2(y+v)/((x+v)t^2) has a nonnegative right hand side. Its integral is strictly positive: equality would force 1/(y+v)=q almost everywhere and hence concentration at the single value 1/q-y. Integration cancels the centered linear term and yields S(x)>q/t, which is equivalent to the stated strict inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("stieltjes-positive-transform"),
                DeclarationHandle.Create("D5/S3/Analytic/WallisRemainder/Stieltjes.stieltjes_pos"),
                H("Positive Stieltjes transform"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a probability measure concentrated on strictly positive values and z>0, its transform satisfies 0<S(z). The strictly positive integrand is integrable and the measure has mass one; the resulting positivity ensures that the inverse transform expressions have nonzero denominators."))),
                DescribeRole.Theorem))));
}
