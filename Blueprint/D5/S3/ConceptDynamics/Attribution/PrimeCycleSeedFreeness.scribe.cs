using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class PrimeCycleSeedFreenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime divisibility of a complete grid denominator forces a free seed action.",
        H("Prime-cycle test profiles"),
        Blocks(Describe.Lean(
            DescribeId.Create("prime-divisibility-forces-free-seeds"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Attribution/PrimeCycleSeedFreeness.free_of_prime_divisibility"),
            H("Freeness from prime divisibility"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let I and S be finite types, with decidable equality on I. The full permutation "
                    + "group of I acts on S. Suppose every prime at most the number of labels divides "
                    + "the natural denominator m. Let w be a strictly positive real weight on each seed. "
                    + "For every natural profile of total m, let f assign each seed a label. Exact "
                    + "calibration means the sum of the weights assigned to each label is its profile "
                    + "coordinate in these units. The readout is equivariant when the same permutation "
                    + "acts on the profile and the seed.")),
                Paragraph(Text(
                    "If a seed stabilizer were nontrivial, Cauchy's theorem supplies an element of "
                    + "prime order p. Each nontrivial cycle of that element has length p. Choose "
                    + "the profile that takes value m divided by p on one such cycle and zero "
                    + "elsewhere. The element fixes the seed and the profile. Equivariance forces "
                    + "the seed to return a fixed label outside the chosen cycle. The weight of the "
                    + "seed is positive while the calibrated mass of that label is zero."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula i = F.Id("I");
        Formula s = F.Id("S");
        Formula m = F.Id("m");
        Formula w = F.Id("w");
        Formula f = F.Id("f");
        return Disp(Seq(Forall, Sp, i, Sp, s, Sp, m, Sp, w, Sp, f, Comma, Sp,
            Call("PrimeDivisibility", i, m), Sp, Land, Sp, Call("Positive", w), Sp, Land, Sp,
            Call("Calibrated", m, w, f), Sp, Land, Sp, Call("Equivariant", f),
            Sp, Rightarrow, Sp, Call("FreeAction", i, s)));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
