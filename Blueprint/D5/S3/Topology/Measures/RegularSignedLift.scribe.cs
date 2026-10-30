using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.Measures;

internal sealed class RegularSignedLiftDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/Measures/RegularSignedLift.";
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula CarrierHypotheses(string name) => Seq(
        Call("TopologicalSpace", V(name)), Sp, Land, Sp,
        Call("CompactSpace", V(name)), Sp, Land, Sp,
        Call("T2Space", V(name)), Sp, Land, Sp,
        Call("MeasurableSpace", V(name)), Sp, Land, Sp,
        Call("BorelSpace", V(name)));
    private static Formula TV(string name) => Call("totalVariation", V(name));
    private static Formula Mass(string name) => Call("totalVariation", V(name), Call("univ"));
    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(All("K", Call("Type", V("u"))), All("L", Call("Type", V("v")))),
        Seq(CarrierHypotheses("K"), Sp, Land, Sp,
            CarrierHypotheses("L"), Sp, Rightarrow),
        Seq(All("p", Seq(V("K"), Sp, To, Sp, V("L"))), Call("Continuous", V("p")),
            Sp, Land, Sp, Call("Surjective", V("p")), Sp, Rightarrow),
        Seq(All("mu", Call("SignedMeasure", V("L"))),
            Call("Regular", TV("mu")), Sp, Rightarrow),
        Seq(Exists, Sp, V("nu"), Colon, Sp, Call("SignedMeasure", V("K")), Comma, Sp,
            Call("Regular", TV("nu")), Sp, Land, Sp,
            Call("map", V("nu"), V("p")), Sp, Eq, Sp, V("mu"), Sp, Land, Sp,
            Mass("nu"), Sp, Eq, Sp, Mass("mu"))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite signed measure with regular total variation has a regular total-variation-mass-preserving lift along a compact Hausdorff continuous surjection.",
        H("Regular signed lifts on compact Hausdorff quotients"),
        Blocks(
            Paragraph(Text(
                "The carrier hypotheses are the exact TopologicalSpace, CompactSpace, T2Space, MeasurableSpace, and BorelSpace structures in the Lean telescope. "
                + "K and L have independent universes and arbitrary compact Hausdorff Borel structures; either carrier may be empty. "
                + "The input is an actual finite SignedMeasure mu on L whose totalVariation is explicitly regular. "
                + "For every continuous surjection p there is an actual SignedMeasure nu on K with regular totalVariation, exact signed pushforward map(nu,p)=mu, and equal totalVariation mass.")),
            Describe.Lean(
                DescribeId.Create("positive-of-unit-norm-bound"),
                DeclarationHandle.Create(Owner + "positive_of_norm_le_one"),
                H("Order-unit positivity"),
                StatementSource.FromAuthor(Disp(Seq(
                    All("K", Call("Type", V("u"))), Call("Compact", V("K")), Sp, Rightarrow,
                    All("Lambda", Call("StrongDual", Call("Real"), Call("ContinuousMap", V("K"), Call("Real")))),
                    Call("norm", V("Lambda")), Sp, Le, Sp, Call("Lambda", Num(1)), Sp, Rightarrow,
                    All("f", Call("ContinuousMap", V("K"), Call("Real"))),
                    Num(0), Sp, Le, Sp, V("f"), Sp, Rightarrow, Num(0), Sp, Le, Sp, Call("Lambda", V("f"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A real continuous linear functional Lambda is positive when its norm is at most its value at the unit. "
                    + "For nonnegative f, set M=norm(f) and u=M*1-f. Then norm(u) is at most M, "
                    + "and Lambda(u)=M*Lambda(1)-Lambda(f) forces Lambda(f) to be nonnegative. "
                    + "No nonempty or Hausdorff premise is needed. restrictionPositive restricts a positive functional to compactly supported continuous functions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-regular-measure-lift"),
                DeclarationHandle.Create(Owner + "exists_regular_measure_lift"),
                H("Positive regular lift by real Hahn–Banach and RMK"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(All("K", Call("Type", V("u"))), All("L", Call("Type", V("v")))),
                    Seq(CarrierHypotheses("K"), Sp, Land, Sp,
                        CarrierHypotheses("L"), Sp, Rightarrow),
                    Seq(All("p", Seq(V("K"), Sp, To, Sp, V("L"))), Call("Continuous", V("p")),
                        Sp, Land, Sp, Call("Surjective", V("p")), Sp, Rightarrow),
                    Seq(All("alpha", Call("Measure", V("L"))),
                        Call("IsFiniteMeasure", V("alpha")), Sp, Land, Sp,
                        Call("Regular", V("alpha")), Sp, Rightarrow),
                    Seq(Exists, Sp, V("eta"), Colon, Sp, Call("Measure", V("K")), Comma, Sp,
                        Call("IsFiniteMeasure", V("eta")), Sp, Land, Sp, Call("Regular", V("eta")), Sp, Land, Sp,
                        Call("map", V("eta"), V("p")), Sp, Eq, Sp, V("alpha"), Sp, Land, Sp,
                        Call("measure", V("eta"), Call("univ")), Sp, Eq, Sp,
                        Call("measure", V("alpha"), Call("univ")))
                ]))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/kania2026talagrand")),
                Blocks(
                    Paragraph(Text(
                        "The pullback C(L,Real) to C(K,Real) is a unital real linear isometry by the compact supremum norm and surjectivity. "
                        + "Integration against alpha is transported to its range, extended by exists_extension_norm_eq, and shown positive from the bound norm(Lambda) <= Lambda(1) using M*1-h. "
                        + "PositiveLinearMap.mk₀ and CompactlySupportedContinuousMap.continuousMapEquiv feed RealRMK.rieszMeasure. "
                        + "The resulting finite regular measure has equal mass and equal integrals after pushforward; regular compactly-supported integral uniqueness gives map(p,eta)=alpha.")),
                    Paragraph(Text(
                        "No nonemptiness, metric, zero-dimensionality, probability, positivity of the signed input, finite support, or abstract unrepresented functional is added. "
                        + "The regularity hypothesis is explicit because arbitrary compact Hausdorff Borel measures need not be regular.")),
                    Paragraph(Text(
                        "The construction uses the pinned Mathlib real Hahn–Banach, positive real Riesz–Markov–Kakutani, regular restriction, continuous pushforward inner-regularity, and compactly-supported integral uniqueness declarations. "
                        + "The source attribution to the Talagrand route records the surrounding application; no external theorem is claimed as a project invention."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("regular-jordan-parts-of-regular-total-variation"),
                DeclarationHandle.Create(Owner + "regular_jordanParts_of_regular_totalVariation"),
                H("Regularity of the Jordan parts"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(All("L", Call("Type", V("v")))),
                    Seq(CarrierHypotheses("L"), Sp, Rightarrow),
                    Seq(All("mu", Call("SignedMeasure", V("L"))),
                        Call("Regular", TV("mu")), Sp, Rightarrow),
                    Seq(Call("Regular", Call("posPart", Call("toJordanDecomposition", V("mu")))),
                        Sp, Land, Sp,
                        Call("Regular", Call("negPart", Call("toJordanDecomposition", V("mu")))))
                ]))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A mutually singular separator for the Jordan parts identifies the positive part with totalVariation restricted to the complement and the negative part with totalVariation restricted to the separator. "
                    + "Measure.Regular.restrict_of_measure_ne_top supplies both regularity conclusions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-regular-norm-preserving-signed-measure-lift"),
                DeclarationHandle.Create(Owner + "exists_regular_normPreserving_signedMeasure_lift"),
                H("Signed lift with exact total variation mass"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Lift the two actual Jordan parts by the positive theorem. Pulling the target separator back along p proves the two lifted positive measures are mutually singular. "
                    + "Their JordanDecomposition difference is the output signed measure, so its totalVariation is exactly the sum of the two regular lifts. "
                    + "The signed pushforward is proved by measurable-set extensionality using VectorMeasure.map_apply and Measure.toSignedMeasure_sub_apply, and the exact mass follows from the two positive mass equalities.")),
                    Paragraph(Text(
                        "The theorem is a construction supplier for the existing NormPreservingLifts.arbitrary_lifts_tendsto consumer. "
                        + "It does not construct the CH recursion, supported clopen rows, fibre hypotheses, or any global solution of Kania–Kąkol Problem 8.2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("regular-add"),
                DeclarationHandle.Create(Owner + "regular_add"),
                H("Regularity of a sum of regular positive measures"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On a compact Hausdorff Borel carrier, the sum of two regular measures is regular. The existing proof obtains outer approximation of each summand, intersects the two open supersets, and combines their mass bounds; native inner regularity supplies the other obligation. This exposes the original consumed helper, preserving its statement and implementation. Its signed-lift consumer and the norm-compact-family variation proof both use it; exposing it is no new mathematical result."))),
                DescribeRole.Theorem))));
}
