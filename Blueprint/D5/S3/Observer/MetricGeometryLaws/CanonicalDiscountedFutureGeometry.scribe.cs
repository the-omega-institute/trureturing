using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometryLaws;

internal sealed class CanonicalDiscountedFutureGeometryDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/MetricGeometryLaws/CanonicalDiscountedFutureGeometry."
            + "canonical_discounted_future_geometry";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Discounted future distance is the canonical bounded-observer pseudometric.",
        H("Canonical Discounted Future Geometry"),
        Blocks(Describe.Lean(
            DescribeId.Create("canonical-discounted-future-geometry"),
            DeclarationHandle.Create(Declaration),
            H("Discounted future distance gives the observer pseudometric"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let F be a deterministic state update and q a readout into a bounded "
                        + "metric space. For a discount gamma strictly between zero and one, "
                        + "D_gamma is the supremum of gamma^n times the output distance after "
                        + "n updates.")),
                Paragraph(Text(
                    "The existing Bellman equation supplies both current-output domination "
                        + "and the one-step gamma-inverse contraction. The latter is also "
                        + "packaged as the standard Mathlib LipschitzWith predicate.")),
                Paragraph(Text(
                    "Strict positivity of every discount power makes zero D_gamma equivalent "
                        + "to equality of every finite future readout, namely membership in "
                        + "the infinite-future relation K_infty."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula gamma = F.Id("gamma");
        Formula bound = F.Id("B");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula first = F.Id("x");
        Formula second = F.Id("y");
        Formula distance = F.Id("Dgamma");
        Formula gammaInverse = Seq(gamma, Caret, Grp(Seq(Minus, D(1))));
        Formula distanceAt = Call("Dgamma", first, second);
        Formula current = Seq(
            Call("d", Call("q", first), Call("q", second)), Sp, Leq, Sp, distanceAt);
        Formula contraction = Seq(
            Call("Dgamma", Call("F", first), Call("F", second)), Sp, Leq, Sp,
            gammaInverse, Sp, distanceAt);
        Formula kernel = Seq(
            Open, distanceAt, Sp, Eq, Sp, D(0), Close, Sp, Iff, Sp,
            Call("KInfinity", first, second));
        Formula hypotheses = Seq(
            D(0), Sp, Lt, Sp, gamma, Sp, Lt, Sp, D(1), Sp, Land, Sp,
            Call("BoundedOutputMetric", readout, bound));
        Formula structure = Seq(
            Call("CanonicalDiscountedDistance", distance, update, readout, gamma),
            Sp, Land, Sp, Call("PseudoMetric", F.Id("Y"), distance));
        Formula laws = Seq(
            current, Sp, Land, RowBreak,
            contraction, Sp, Land, RowBreak,
            Call("LipschitzWith", gammaInverse, update, distance), Sp, Land, RowBreak,
            kernel);

        return Disp(Seq(
            hypotheses, Sp, Rightarrow, RowBreak,
            Exists, Sp, distance, Comma, Sp, structure, Sp, Land, RowBreak,
            Forall, Sp, first, Comma, Sp, second, InMacro, Sp, F.Id("Y"), Comma,
            RowBreak, Grp(), laws, Dot));
    }
}
