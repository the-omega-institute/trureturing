using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit;

internal sealed class PrimeBlindnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Primality of the inputs does not determine the golden Beatty deficit.",
        H("Prime Blindness"),
        Blocks(
            Paragraph(Text(
                "The deficit is already known not to be determined by any fixed modulus. The "
                    + "companion claim is that it is equally blind to primality, and the "
                    + "statement here has the same shape: two witness pairs whose inputs are "
                    + "all prime, whose deficits differ.")),
            Paragraph(Text(
                "Stating it as a witness rather than as a property of the definition is "
                    + "deliberate. The source phrases the claim as the definition containing no "
                    + "primes, which is a remark about how the definition is written and not a "
                    + "proposition about the function. A witness pair is the mathematical "
                    + "content of that remark: no classification by primality can pin a value "
                    + "that two all-prime pairs already disagree on.")),
            Describe.Lean(
                DescribeId.Create("primality-does-not-determine-the-beatty-deficit"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/PrimeBlindness.beattyDeficit_not_determined_by_primality"),
                H("Primality does not determine the Beatty deficit"),
                StatementSource.FromAuthor(BlindFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The witnesses are the two smallest all-prime pairs with distinct "
                        + "deficits; the shift values are read through the public displacement "
                        + "decode bridge rather than from a square-root bracket."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Deficit/GoldenPhaseDeficit")),
        ]));

    private static Formula Def(Formula a, Formula b) =>
        Seq(F.Id("c"), Open, a, Comma, Sp, b, Close);

    private static Formula BlindFormula() =>
        Disp(Seq(
            Def(D(2), D(2)), Sp, Neq, Sp, Def(D(2), D(3)), Comma, Sp,
            Operatorname, Grp(F.Id("all")), Sp, Operatorname, Grp(F.Id("prime")), Dot));
}
