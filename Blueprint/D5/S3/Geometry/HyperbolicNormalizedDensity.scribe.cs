using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class HyperbolicNormalizedDensityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native Hausdorff three-measure and its coordinate density.",
        H("Native Hausdorff density"),
        Blocks(
            Paragraph(Text(
                "Coordinates3 is UpperHalfSpace over Complex: the positive-height subtype of "
                + "the Euclidean space WithLp 2 (Complex times Real). Native3 is HyperbolicThreeSpace. "
                + "If D is Euclidean coordinate distance and hx, hy are the two positive heights, "
                + "native distance is 2 arsinh(D/(2 sqrt(hx hy))). Both spaces have their Borel "
                + "measurable structures; in the formulas, borel and BorelSpace denote this choice "
                + "and its compatibility with the topology.")),
            FormulaBlock(Equal(X("Coordinates3"), Call("UpperHalfSpace", X("Complex")))),
            FormulaBlock(Equal(X("Native3"), X("HyperbolicThreeSpace"))),
            FormulaBlock(Equal(Call("measurableSpace", X("Coordinates3")), Call("borel", X("Coordinates3")))),
            FormulaBlock(Call("BorelSpace", X("Coordinates3"))),
            FormulaBlock(Equal(Call("measurableSpace", X("Native3")), Call("borel", X("Native3")))),
            FormulaBlock(Call("BorelSpace", X("Native3"))),
            Paragraph(Text(
                "coordinatesEquiv is the measurable equivalence underlying the coordinate homeomorphism. "
                + "It sends a native point to its coordinates, and its inverse is the constructor mk.")),
            FormulaBlock(Equal(X("coordinatesEquiv"),
                Call("toMeasurableEquiv", Call("coordinatesHomeomorph", X("Complex"))))),
            FormulaBlock(All("z", X("Native3"), Equal(Call("coordinatesEquiv", X("z")), Call("coordinates", X("z"))))),
            FormulaBlock(All("s", Call("Set", X("Coordinates3")),
                Equal(Call("preimage", X("coordinatesEquiv"), X("s")), Call("image", X("mk"), X("s"))))),
            Paragraph(Text(
                "The two raw measures are Mathlib's unnormalized Hausdorff three-measures on their "
                + "respective metric spaces. heightDensity takes values in the extended nonnegative "
                + "reals; ofReal is the canonical map from real numbers to that space.")),
            FormulaBlock(Equal(X("rawCoordinateMeasure"), Call("hausdorffMeasure", Num(3), X("Coordinates3")))),
            FormulaBlock(Equal(X("rawNativeMeasure"), Call("hausdorffMeasure", Num(3), X("Native3")))),
            FormulaBlock(All("x", X("Coordinates3"), Equal(Call("heightDensity", X("x")),
                Call("ofReal", Pow(Call("inv", Call("height", X("x"))), Num(3)))))),
            Describe.Lean(
                DescribeId.Create("raw-native-density"),
                DeclarationHandle.Create("D5/S3/Geometry/HyperbolicNormalizedDensity.raw_native_density"),
                H("Raw Hausdorff density identity"),
                StatementSource.FromAuthor(Disp(Equal(NativePushforward(), CoordinateDensity()))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here map denotes measure pushforward, and withDensity denotes multiplication "
                        + "of a measure by a nonnegative measurable density through the lower integral. "
                        + "The equality has no hypotheses and is an equality of measures, including "
                        + "sets with zero or infinite measure. The two sides use the original native "
                        + "and coordinate metrics. The argument combines local metric distortion, "
                        + "pointwise height bounds, countable additivity and an extended-real limit.")),
                    Paragraph(Text(
                        "For a positive radius below the height of its centre, local Hausdorff "
                        + "comparison and the preimage identity above give the following bounds on "
                        + "each Borel subset of the coordinate ball. Every ball in this exposition "
                        + "uses the Euclidean coordinate metric.")),
                    FormulaBlock(RawLocalComparison()),
                    Paragraph(Text(
                        "Define the distortion factor for real epsilon by the formula below. For "
                        + "zero less than epsilon less than one, pointwise bounds on height over a ball "
                        + "of radius epsilon times the centre height bound the density from above and "
                        + "below. Combining these bounds with local Hausdorff comparison yields the "
                        + "two inequalities with the same factor.")),
                    FormulaBlock(All("epsilon", X("Real"), Equal(Factor(),
                        Call("ofReal", Pow(new Formula.Fraction(
                            Add(Num(1), Multiply(Num(2), X("epsilon"))),
                            Subtract(Num(1), X("epsilon"))), Num(3)))))),
                    FormulaBlock(LocalSandwich()),
                    Paragraph(Text(
                        "These balls cover Coordinates3. A Lindelof countable subcover can be "
                        + "disjointified into Borel pieces Dn. For a Borel set s, the sets s intersect Dn "
                        + "form a countable measurable partition of s. Applying the local estimates to "
                        + "each piece and summing in the extended nonnegative reals gives the global bounds.")),
                    FormulaBlock(GlobalSandwich()),
                    Paragraph(Text(
                        "Take epsilon(n)=1/(n+2) for natural n. The distortion factors tend to one. "
                        + "For every fixed extended nonnegative real b, their products with b tend to b: "
                        + "multiplication is continuous at the nonzero limiting factor even if b is infinite. "
                        + "Closedness of the order relation therefore turns the two global inequalities "
                        + "into equality on every Borel set, which determines equality of measures.")),
                    Paragraph(Text(
                        "An application is the usual Euclidean volume normalization. In the same L2 "
                        + "ambient space A, let Q be the parallelepiped of the standard real orthonormal "
                        + "basis, c3 its raw Hausdorff three-mass, j the coordinate subtype inclusion, "
                        + "and coordinateHaar the pullback of canonical ambient volume along j.")),
                    FormulaBlock(Equal(X("A"), Call("WithLp", Num(2), Call("Product", X("Complex"), X("Real"))))),
                    FormulaBlock(Equal(X("Q"), Call("parallelepiped", Call("toBasis", Call("stdOrthonormalBasis", X("Real"), X("A")))))),
                    FormulaBlock(Equal(X("c3"), Call("mass", Call("hausdorffMeasure", Num(3), X("A")), X("Q")))),
                    FormulaBlock(Equal(X("j"), X("subtypeVal"))),
                    FormulaBlock(Equal(X("coordinateHaar"), Call("comap", Call("volume", X("A")), X("j")))),
                    Paragraph(Text(
                        "The real dimension of A is three. Its raw Hausdorff measure is an additive Haar "
                        + "measure. Haar uniqueness and orthonormal-cube calibration identify it with c3 "
                        + "times canonical volume. The cube has nonempty interior and is compact, so c3 "
                        + "is strictly positive and finite. The inclusion j is isometric and an open "
                        + "measurable embedding, giving the coordinate calibration below.")),
                    FormulaBlock(And(LT(Num(0), X("c3")), LT(X("c3"), Infty))),
                    FormulaBlock(Equal(Call("hausdorffMeasure", Num(3), X("A")),
                        Call("smul", X("c3"), Call("volume", X("A"))))),
                    FormulaBlock(Equal(X("rawCoordinateMeasure"), Call("smul", X("c3"), X("coordinateHaar")))),
                    Paragraph(Text(
                        "Substituting this calibration into the raw identity and cancelling c3 once "
                        + "gives the normalized formula. No set mass is divided out, and no sup-norm "
                        + "Hausdorff measure is substituted for the L2 measure.")),
                    FormulaBlock(Equal(Call("map", Call("smul", Call("inv", X("c3")), X("rawNativeMeasure")), X("coordinatesEquiv")),
                        Call("withDensity", X("coordinateHaar"), X("heightDensity")))),
                    Paragraph(Text("Natural-dimension application of the same local-distortion and squeeze argument. For every natural d, let Hcoord_d and Hnative_d be raw Hausdorff d-measure in the unchanged Euclidean coordinate and native H3 metrics. Then map(Hnative_d,coordinatesEquiv)=withDensity(Hcoord_d,x |-> ofReal(height(x)^(-d))). In the local Hausdorff image inequalities, use the original ball_distortion with powers d; on a ball of radius epsilon*height(p), the common density distortion factor is ((1+2*epsilon)/(1-epsilon))^d. The same countable Borel partition and extended-real squeeze prove the equality, including d=0 and sets of infinite measure.")),
                    Paragraph(Text("For d=2 this identifies the native H3 surface-dimension measure with height^(-2) times ambient Euclidean-coordinate Hausdorff two-measure. Ambient three-dimensional Hausdorff two-measure is not assumed sigma-finite: the argument evaluates withDensity only on Borel sets, uses countable additivity with values in the extended nonnegative reals, and cancels only finite positive local distortion scalars. This application does not replace that coordinate two-measure by three-dimensional volume, or identify it with dxdy on a specified plane. A plane-area formula still needs the actual Euclidean embedding, an independent dimension-two Euclidean calibration and isometric measure transport; the c3 normalization above supplies none of those identifications.")),
                    Paragraph(Text(
                        "The density identity concerns measures on the whole upper half-space. "
                        + "It gives no Gram-map Jacobian, frame-independence statement, finite positive "
                        + "mass for a specified geometric body, Schlaefli variation formula or "
                        + "strictly positive flat-boundary limit."))),
                DescribeRole.Theorem)),
        []));

    private static Formula X(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula LT(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LE(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Pow(Formula a, Formula b) =>
        new Formula.Power(a is Formula.Fraction ? Seq(Open, a, Close) : a, b);
    private static DocumentBlock FormulaBlock(Formula formula) => new DocumentBlock.DisplayFormula(formula);
    private static Formula NativePushforward() => Call("map", X("rawNativeMeasure"), X("coordinatesEquiv"));
    private static Formula CoordinateDensity() => Call("withDensity", X("rawCoordinateMeasure"), X("heightDensity"));
    private static Formula Mass(Formula measure) => Call("mass", measure, X("s"));
    private static Formula Factor() => Call("distortionFactor", X("epsilon"));
    private static Formula Sandwich() => And(
        LE(Mass(CoordinateDensity()), Multiply(Factor(), Mass(NativePushforward()))),
        LE(Mass(NativePushforward()), Multiply(Factor(), Mass(CoordinateDensity()))));
    private static Formula EpsilonRange() => And(LT(Num(0), X("epsilon")), LT(X("epsilon"), Num(1)));
    private static Formula Measurable() => Call("MeasurableSet", X("s"));
    private static Formula Inside(Formula radius) => new Formula.Relation(X("s"), FormulaRelationOperator.SubsetOf,
        Call("ball", X("p"), radius));
    private static Formula RawLocalComparison()
    {
        var h = Call("height", X("p"));
        var r = X("r");
        var bounds = And(
            LE(Mass(X("rawCoordinateMeasure")), Multiply(Pow(Call("ofReal", Add(h, Multiply(Num(2), r))), Num(3)), Mass(NativePushforward()))),
            LE(Mass(NativePushforward()), Multiply(Pow(Call("ofReal", Call("inv", Subtract(h, r))), Num(3)), Mass(X("rawCoordinateMeasure")))));
        return All("p", X("Coordinates3"), All("r", X("Real"),
            Imp(And(LT(Num(0), r), LT(r, h)), All("s", Call("Set", X("Coordinates3")),
                Imp(And(Measurable(), Inside(r)), bounds)))));
    }
    private static Formula LocalSandwich() => All("epsilon", X("Real"), Imp(EpsilonRange(),
        All("p", X("Coordinates3"), All("s", Call("Set", X("Coordinates3")),
            Imp(And(Measurable(), Inside(Multiply(X("epsilon"), Call("height", X("p"))))), Sandwich())))));
    private static Formula GlobalSandwich() => All("epsilon", X("Real"), Imp(EpsilonRange(),
        All("s", Call("Set", X("Coordinates3")), Imp(Measurable(), Sandwich()))));
}
