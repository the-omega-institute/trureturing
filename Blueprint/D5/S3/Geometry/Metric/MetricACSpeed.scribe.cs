using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Metric;

internal sealed class MetricACSpeedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual measurable metric-speed limit is integrable and exactly recovers the variation of every subinterval.",
        H("Metric speed and accumulated variation"),
        Blocks(
            Paragraph(Text("Let X be any metric space, T a positive real number, and z : real -> X absolutely continuous on [0,T]. Let r : real -> real be nonnegative everywhere and almost everywhere strongly measurable for volume restricted to [0,T]. Assume that dist(z(t+h),z(t))/abs(h) tends to r(t), through nonzero h tending to zero, at almost every t in that same restricted interval. Neither integrability nor an upper-gradient estimate is a premise.")),
            Describe.Lean(
    DescribeId.Create("metric-ac-speed-variation-bridge"),
    DeclarationHandle.Create("D5/S3/Geometry/Metric/MetricACSpeed.metric_AC_speed_variation_bridge"),
    H("Integrable speed and exact variation"),
    StatementSource.WithoutFormula(),
    AssessedProvenance.FromRepo(),
    Blocks(Paragraph(Text("Put A(t)=variationOnFromTo z (Icc 0 T) 0 t. Then r is interval integrable on 0..T, deriv A(t)=r(t) almost everywhere for volume restricted to [0,T], and the extended integral of ofReal(r(t)) over [0,T] equals eVariationOn z (Icc 0 T). For every 0<=a<=b<=T, the real integral of r over a..b equals (eVariationOn z (Icc a b)).toReal and bounds dist(z(a),z(b)) from above. The same r supplies all conclusions."))),
    DescribeRole.Theorem),
            Paragraph(Text("The frozen VariationPrimitive supplies absolute continuity and exact increments of A. At an interior differentiability point, each forward chord is bounded by the corresponding variation increment, so the speed limit is at most deriv A. This gives integrability of r by domination. For each fixed a, distance to z(a) is a 1-Lipschitz composition of z and is absolutely continuous. Its derivative has absolute value at most r, by the reverse triangle inequality and the speed limit. The real fundamental theorem of calculus yields the chord bound on every subinterval.")),
            Paragraph(Text("The chord bounds control every monotone partition sum by the speed integral. This step uses the port of TauCeti eVariationOn.le_lintegral_of_edist_le_lintegral at revision 49035f0ebf0e506dc2f1c078374b2dea4ac9c6dd. The port sums adjacent half-open interval integrals and uses measure monotonicity; its state and parameter spaces remain arbitrary. Its immutable source, license and retirement condition are recorded in the corresponding Library note.")),
            Paragraph(Text("Integrating r<=deriv A gives the opposite inequality. Equality of the integrals and almost-everywhere domination give deriv A=r almost everywhere. Applying the fundamental theorem to A on each subinterval gives all exact increments. The result uses no completeness, separability, finite-energy or Riemannian hypothesis.")),
            Paragraph(Text("Source for the port: "), Ref("D5/L/Geometry/tauceti2026metricvariation"))),
        []));
}
