using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.WallisRemainder;

internal sealed class StieltjesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict inequalities for Stieltjes transforms of positive probability laws.",
        H("Stieltjes remainder monotonicity"), Blocks(
            Describe.Lean(DescribeId.Create("stieltjes-jensen-remainder-monotonicity"),
                DeclarationHandle.Create("D5/S3/Analytic/WallisRemainder/Stieltjes.strictMonoOn_jensenRemainder"),
                H("Strict increase of the normalized Jensen remainder"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let M be a probability measure on the real line concentrated on strictly positive values. Its Stieltjes transform is S(z)=integral 1/(z+v) dM(v). Let a be its finite mean, and suppose the centered second moment s=integral (v-a)^2 dM(v) is finite and strictly positive. Then z^3(S(z)-1/(z+a))/s is strictly increasing for z>0.")),
                    Paragraph(Text("Centering gives S(z)-1/(z+a)=integral ((v-a)^2/(z+v)) dM(v)/(z+a)^2. Inside the resulting normalized integral, the kernel is the product (z/(z+a))^2 times z/(z+v). Both factors increase, and the kernel increases strictly for every positive v. Positive centered second moment ensures that the multiplier (v-a)^2 does not vanish almost everywhere."))),
                DescribeRole.Theorem))));
}
