using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels.ContractionGeometry;

internal sealed class NorthPoleBallCriterionDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Display(Formula x) => new DocumentBlock.DisplayFormula(Disp(x));
    private static Formula Sq(Formula x) => Seq(Open, x, Close, Caret, D(2));
    private static Formula AllReal(Formula x, Formula body) => Seq(
        Forall, Sp, x, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp, body);
    private static Formula Product(Formula x, Formula y) => Seq(x, Sp, Cdot, Sp, y);
    private static Formula Sum(Formula x, Formula y) => Seq(x, Plus, y);
    private static Formula Axis => Seq(F.Id("a"), F.Id("z"), Plus, D(1), Minus, F.Id("a"));
    private static Formula Radius => Sum(Sum(Sq(F.Id("x")), Sq(F.Id("y"))), Sq(F.Id("z")));
    private static Formula ImageRadius => Sum(Sum(
        Sq(Product(Lambda, F.Id("x"))), Sq(Product(Lambda, F.Id("y")))), Sq(Axis));
    private static Formula Exponent(Formula x) => Seq(F.Id("e"), Caret, Grp(x));
    private static Formula Time(byte i) => Seq(F.Id("T"), Underscore, D(i));
    private static Formula Decay(byte i) => Exponent(Seq(Minus, Frac, Grp(F.Id("t")), Grp(Time(i))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact unit-ball criterion for an axial affine map fixing the north pole gives the "
            + "relaxation-time bound for positive exponential decay times.",
        H("Exact North-Pole Ball Preservation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("north-pole-ball-preserving-iff"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumChannels/ContractionGeometry/NorthPoleBallCriterion."
                    + "north_pole_ball_preserving_iff"),
                H("Sharp transverse criterion for the whole closed ball"),
                StatementSource.FromAuthor(Disp(AllReal(F.Id("a"), AllReal(Lambda, Seq(
                    Open, D(0), Sp, Leq, Sp, F.Id("a"), Sp, Land, Sp,
                    F.Id("a"), Sp, Leq, Sp, D(1), Close, Sp, Rightarrow, Sp,
                    Open, Open,
                    AllReal(F.Id("x"), AllReal(F.Id("y"), AllReal(F.Id("z"), Seq(
                        Radius, Sp, Leq, Sp, D(1), Sp, Rightarrow, Sp,
                        ImageRadius, Sp, Leq, Sp, D(1))))),
                    Close, Sp, Iff, Sp, Sq(Lambda), Sp, Leq, Sp, F.Id("a"), Close))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The three real coordinates describe the closed Euclidean unit ball. "
                        + "Both transverse coordinates have the same real factor lambda, with "
                        + "either sign allowed. The axis drifts toward the fixed north pole. "
                        + "The Lean statement uses dampedAxis with gamma equal to one minus a; "
                        + "expanding that existing coordinate gives exactly a z plus one minus a. "
                        + "The criterion includes a equal to zero and a equal to one.")),
                    Paragraph(Text(
                        "For sufficiency, the squared transverse radius is first multiplied by "
                        + "lambda squared, bounded by a, and then bounded using the input ball. "
                        + "The remaining axial defect is nonnegative:")),
                    Display(Seq(
                        Product(F.Id("a"), Seq(Open, D(1), Minus, Sq(F.Id("z")), Close)),
                        Plus, Sq(Axis), Sp, Eq, Sp, D(1), Minus,
                        Product(Product(F.Id("a"), Seq(Open, D(1), Minus, F.Id("a"), Close)),
                            Sq(Seq(D(1), Minus, F.Id("z")))), Sp, Leq, Sp, D(1))),
                    Paragraph(Text(
                        "For necessity, suppose lambda squared exceeds a and choose the positive "
                        + "height deficit delta below. It is at most one. The sphere point has "
                        + "y equal to zero, z equal to one minus delta, and nonnegative x whose "
                        + "square is delta multiplied by (two minus delta).")),
                    Display(Seq(Delta, Sp, Eq, Sp, Frac,
                        Grp(Sq(Lambda), Minus, F.Id("a")), Grp(Sq(Lambda), Plus, D(1)))),
                    Paragraph(Text(
                        "Its image has squared radius exceeding one by delta times the bracket "
                        + "below. Since delta multiplied by (lambda squared plus one) equals "
                        + "(lambda squared minus a), and a squared is nonnegative, the bracket "
                        + "is at least lambda "
                        + "squared minus a and is strictly positive. Thus a specific sphere point "
                        + "violates preservation whenever the criterion fails; no infinitesimal "
                        + "approximation is needed.")),
                    Display(Seq(Product(Delta, Seq(Open,
                        D(2), Open, Sq(Lambda), Minus, F.Id("a"), Close, Minus,
                        Delta, Open, Sq(Lambda), Minus, Sq(F.Id("a")), Close,
                        Close)), Sp, Gt, Sp, D(0)))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(H("Exponential relaxation in the same affine model"), Blocks(
            Paragraph(Text(
                "Assume positive real longitudinal time T one, transverse time T two, and "
                + "observation time t. Set a and lambda to the following exponential factors, "
                + "and assume that the very same map preserves the entire closed unit ball:")),
            Display(Seq(F.Id("a"), Sp, Eq, Sp, Decay(1), Comma, Sp,
                Lambda, Sp, Eq, Sp, Decay(2))),
            Paragraph(Text(
                "The axial factor lies strictly between zero and one. The criterion gives "
                + "the following exact chain; injectivity and monotonicity of the real "
                + "exponential and cancellation of positive time and denominators justify "
                + "each step:")),
            Display(Seq(Exponent(Seq(Minus, Frac, Grp(D(2), F.Id("t")), Grp(Time(2)))),
                Sp, Leq, Sp, Decay(1), Sp, Iff, Sp,
                Minus, Frac, Grp(D(2), F.Id("t")), Grp(Time(2)), Sp, Leq, Sp,
                Minus, Frac, Grp(F.Id("t")), Grp(Time(1)), Sp, Iff, Sp,
                Time(2), Sp, Leq, Sp, D(2), Time(1))),
            Paragraph(Text(
                "At zero observation time both factors are one for every positive pair of "
                + "time constants, so that time alone gives no rate inequality. At the "
                + "zero-axial endpoint preservation forces lambda to be zero; at the "
                + "unit-axial endpoint it permits precisely absolute lambda at most one. "
                + "Pure amplitude damping has lambda squared equal to a and saturates the bound. "
                + "This concerns a fixed north pole, a zero-temperature axial drift and an "
                + "isotropic transverse factor. It does not extend that physical model to "
                + "every environment or identify ball preservation with complete positivity.")))),
            new DocumentBlock.Section(H("Additional dephasing requires a product envelope"), Blocks(
            Paragraph(Text(
                "If an additional nonnegative dephasing rate k is supplied together with the "
                + "product-envelope assumption, exponential factors multiply as follows:")),
            Display(Seq(Decay(2), Sp, Eq, Sp,
                Product(Exponent(Seq(Minus, Frac, Grp(F.Id("t")), Grp(D(2), Time(1)))),
                    Exponent(Seq(Minus, F.Id("k"), F.Id("t")))), Comma, Sp,
                F.Id("k"), Sp, Geq, Sp, D(0))),
            Paragraph(Text(
                "At positive time this implies the reciprocal rate is one over twice T one "
                + "plus k, hence the same relaxation bound. Rate addition depends on the "
                + "assumed exponential individual envelopes and their product relation; "
                + "geometric preservation alone does not supply that relation. For physical "
                + "context see Krantz et al., A quantum engineer's guide to superconducting "
                + "qubits, arXiv:1904.06560v3, equations 40–43 and the adjacent qualification "
                + "on exponential individual decay functions.")))))));
}
