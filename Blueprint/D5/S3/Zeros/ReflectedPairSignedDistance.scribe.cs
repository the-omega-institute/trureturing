using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class ReflectedPairSignedDistanceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Zeros/ReflectedPairSignedDistance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reflected pair becomes a negative signed distance in the squared normal coordinate.",
        H("Reflected-Pair Signed Distance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reflected-pair-signed-distance-resolvent"),
                DeclarationHandle.Create(
                    Prefix + "reflected_pair_signed_distance_resolvent"),
                H("A reflected pair gives a negative signed-distance resolvent"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive delta, the reflected offsets minus delta and delta "
                            + "determine the negative signed support point minus delta squared. "
                            + "Their product is r squared minus delta squared, and squaring that "
                            + "product agrees with the squared-coordinate intensity at r squared.")),
                    Paragraph(Text(
                        "When u differs from delta squared, the same squared intensity is away "
                            + "from its pole and its logarithmic slope is two divided by u minus "
                            + "delta squared. This is only a finite algebraic separation model; "
                            + "it asserts no converse and no connection to xi or spectral data."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula delta = DeltaLower;
        Formula r = F.Id("r");
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula deltaSquared = Seq(delta, Caret, Grp(D(2)));
        Formula rSquared = Seq(r, Caret, Grp(D(2)));
        Formula uMinusDeltaSquared = Seq(
            u, Sp, Minus, Sp, deltaSquared);
        Formula pairAmplitude = Seq(
            Open, r, Sp, Minus, Sp, delta, Close,
            Open, r, Sp, Plus, Sp, delta, Close);
        Formula centerIntensityAtR = Seq(
            Open, rSquared, Sp, Minus, Sp, deltaSquared, Close,
            Caret, Grp(D(2)));
        Formula centerIntensityAtU = Seq(
            Open, uMinusDeltaSquared, Close, Caret, Grp(D(2)));
        Formula centerIntensity = Seq(
            v, Sp, Mapsto, Sp,
            Open, v, Sp, Minus, Sp, deltaSquared, Close,
            Caret, Grp(D(2)));
        Formula derivativeAtU = Seq(
            Operatorname, Grp(F.Id("deriv")),
            Open, centerIntensity, Close, Open, u, Close);
        Formula hypotheses = Seq(
            Open, D(0), Sp, Lt, Sp, delta, Close,
            Sp, Land, Sp,
            Open, u, Sp, Neq, Sp, deltaSquared, Close);
        Formula conclusion = Seq(
            Minus, deltaSquared, Sp, Lt, Sp, D(0),
            Sp, Land, RowBreak, Grp(),
            pairAmplitude, Sp, Eq, Sp,
            rSquared, Sp, Minus, Sp, deltaSquared,
            Sp, Land, RowBreak, Grp(),
            Open, pairAmplitude, Close, Caret, Grp(D(2)), Sp, Eq, Sp,
            centerIntensityAtR,
            Sp, Land, RowBreak, Grp(),
            derivativeAtU, Sp, Slash, Sp, centerIntensityAtU,
            Sp, Eq, Sp,
            D(2), Sp, Slash, Sp,
            Open, uMinusDeltaSquared, Close);

        return Disp(Seq(
            Forall, Sp, delta, Comma, Sp, r, Comma, Sp, u,
            Colon, Sp, reals, Comma, RowBreak, Grp(),
            hypotheses, Sp, Rightarrow, RowBreak, Grp(),
            Open, conclusion, Close, Dot));
    }
}
