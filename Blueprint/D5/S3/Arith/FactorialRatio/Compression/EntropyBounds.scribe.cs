using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio.Compression;

internal sealed class EntropyBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/Compression/EntropyBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quartic entropy estimate separates the optimized profile from the logarithmic threshold.",
        H("A rational bound for the optimized entropy"),
        Blocks(
            Paragraph(Text(
                "Let h(v)=-v log(v)-(1-v)log(1-v), with continuous endpoint values, "
                + "and let I(t) be the integral of -h(tu) over 0<=u<=1. The profile "
                + "has a unique minimum on 0<=t<=1. Write kappa for the negative "
                + "of this minimum.")),
            Describe.Lean(
                DescribeId.Create("sharp-entropy-profile-bound"),
                DeclarationHandle.Create(Prefix + "sharp_entropy_profile_bound"),
                H("A strict comparison with the Euler constant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real t with 0<=t<=1, I(t)>=-161/288. The same "
                        + "theorem proves 161/288<2 log(2)-(3/4)log(3)<563/1000<gamma, "
                        + "where gamma is the Euler--Mascheroni constant. In particular "
                        + "kappa<=161/288 and gamma-kappa is strictly positive.")),
                    Paragraph(Text(
                        "The corrected entropy h(v)+2(v-1/2)^2+(4/3)(v-1/2)^4 "
                        + "is concave on the closed unit interval. Its second derivative "
                        + "in the interior is -(2v-1)^4/(v(1-v)), which is nonpositive. "
                        + "Reflection about 1/2 therefore gives the pointwise bound "
                        + "h(v)<=log(2)-(2v-1)^2/2-(2v-1)^4/12, including both endpoints.")),
                    Paragraph(Text(
                        "Integrating at v=tu gives log(2)-7/12+4t/3-4t^2/3+2t^3/3-4t^4/15. "
                        + "Use log(2)<=25/36. The resulting polynomial equals "
                        + "161/288-(1-t)^2/60-(4t-3)^2(2(2t-1)^2+21)/480, "
                        + "so it is at most 161/288. Certified logarithm bounds and "
                        + "the Euler-constant lower bound give the strict scalar comparisons."))),
                DescribeRole.Theorem))));
}
