using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.AllOrder;

internal sealed class GoldenWeightCoordinatesDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/AllOrder/GoldenWeightCoordinates."
            + "golden_weight_coordinates";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every golden Euler beta mode has bounded natural Beatty coordinates with its "
            + "exact frozen weight, and the golden weight map is injective.",
        H("Golden Weight Coordinates"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-weight-coordinates"),
            DeclarationHandle.Create(Declaration),
            H("Bounded Beatty coordinates have exact and injective golden weights"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a natural mode v, let q(v) be the natural value of the floor "
                        + "of (v+1)/phi. The inequalities q(v) at most v and v at most "
                        + "2q(v) make both natural subtractions in the coordinate pair "
                        + "(2q(v)-v, v-q(v)) exact.")),
                Paragraph(Text(
                    "Expanding phi squared and phi cubed reduces the weight of that pair "
                        + "to q(v)+v phi. The frozen Zeckendorf theorem identifies this "
                        + "quantity with o5Beta(v) for every v, including the vacuum mode.")),
                Paragraph(Text(
                    "For an arbitrary pair (a,b), its weight has affine coefficients "
                        + "a+2b and a+b over the basis (phi,1). If two weights agree while "
                        + "their phi coefficients differ, phi would equal a quotient of "
                        + "integers, contradicting the pinned irrationality theorem. The "
                        + "two equal coefficients then recover a and b.")),
                Paragraph(Text(
                    "This is one coordinate rung in the golden Euler germ extraction "
                        + "ladder of OACTC parts 580 and 581. It advances the still-open "
                        + "finite all-order census by supplying bounded coordinates, exact "
                        + "weights, and uniqueness. It does not assert growth, divergence, "
                        + "the sublevel census, an all-order extraction, O-5, or the Riemann "
                        + "Hypothesis."))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Analytic/GoldenEulerBetaZeckendorf")),
        ]));

    private static Formula TheoremFormula()
    {
        Formula v = F.Id("v");
        Formula naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        Formula quotient = Call("goldenBeattyQ", v);
        Formula coordinate = Call("goldenBetaCoord", v);
        Formula weight = F.Id("goldenWeight");

        Formula lowerBound = F.Seq(
            quotient, F.Sp, F.Leq, F.Sp, v);
        Formula upperBound = F.Seq(
            v, F.Sp, F.Leq, F.Sp, F.D(2), F.Sp, F.Times, F.Sp, quotient);
        Formula exactWeight = F.Seq(
            Call("goldenWeight", coordinate),
            F.Sp, F.Eq, F.Sp,
            Call("o5Beta", v));

        Formula allCoordinates = F.Seq(
            F.Forall, F.Sp, v, F.InMacro, F.Sp, naturals, F.Comma, F.Sp,
            F.Open,
            lowerBound, F.Sp, F.Land, F.Sp,
            upperBound, F.Sp, F.Land, F.Sp,
            exactWeight,
            F.Close);
        Formula injectiveWeight = F.Seq(
            F.Operatorname, F.Grp(F.Id("Injective")),
            F.Open, weight, F.Close);

        return F.Disp(F.Seq(
            allCoordinates,
            F.Sp, F.Land, F.Sp,
            injectiveWeight,
            F.Dot));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula>
        {
            F.Operatorname,
            F.Grp(F.Id(name)),
            F.Open,
        };

        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(F.Comma);
                pieces.Add(F.Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(F.Close);
        return F.Seq(pieces.ToArray());
    }
}
