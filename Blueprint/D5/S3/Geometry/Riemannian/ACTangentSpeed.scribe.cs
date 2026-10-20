using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Riemannian;

internal sealed class ACTangentSpeedDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolutely continuous manifold curves: chart partitions, tangent derivatives and intrinsic speed.",
        H("Chart absolute continuity and Riemannian metric speed"),
        Blocks(
            Paragraph(Text(
                "Let E be any finite-dimensional real inner-product space, with its normed additive group, "
                + "and let M have its original topology, an E-charted smooth manifold structure, the Hausdorff "
                + "and connected-space instances, and a continuous Riemannian metric on its tangent bundle. "
                + "Write I for the self model with corners on E and IR for that on the real line. "
                + "Every distance and absolute-continuity assertion on M below uses exactly "
                + "Original172.canonicalMetric (E := E) (M := M), constructed in ChartComparison. "
                + "The tangent norm is the norm of the given Riemannian bundle. The canonical metric retains "
                + "the original manifold topology; no auxiliary metric or topology is a hypothesis.")),
            Describe.Lean(
                DescribeId.Create("actual-chart-ac-tangent-and-metric-speed"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Riemannian/ACTangentSpeed.actual_chart_AC_tangent_and_metric_speed"),
                H("Finite chart partition, almost-everywhere tangent formula and intrinsic speed"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real T > 0 and every z : real -> M absolutely continuous on [0,T] "
                        + "in that canonical metric, all three conclusions in the displayed conjunction hold. "
                        + "Geometry(E,M) in the display abbreviates exactly the structures in the preceding "
                        + "paragraph. ACg means AbsolutelyContinuousOnInterval with that fixed metric. "
                        + "The Lean declaration is Original172.actual_chart_AC_tangent_and_metric_speed.")),
                    Paragraph(Text(
                        "ChartPartition(z,T) means that there exist tau : natural -> [0,T], chart centers "
                        + "p_n in M, open sets U_n in M, and nonnegative real Lipschitz constants K_n. "
                        + "One has tau_0=0, tau monotone, and an m such that tau_n=T for every n>=m. "
                        + "For every n, U_n is contained in the source of phi_n=extChartAt I p_n, "
                        + "phi_n is LipschitzOnWith K_n on U_n, z maps [tau_n,tau_(n+1)] into U_n, "
                        + "and phi_n composed with z is absolutely continuous on that interval. "
                        + "Repeated terminal points encode the finite partition; strict increase is not asserted.")),
                    Paragraph(Text(
                        "TangentAndSpeed(z,t) means MDifferentiableAt IR I z t and the following two claims. "
                        + "For every p in M whose actual chart phi=extChartAt I p contains z(t) in its source, "
                        + "phi composed with z is differentiable at t, and v(t)=(mfderiv IR I z t)(1) equals "
                        + "(mfderiv I I phi.symm (phi(z(t))))(deriv (phi composed with z) t). "
                        + "Also dist_g(z(t+h),z(t))/abs(h) tends to the Riemannian norm of v(t) as real h "
                        + "tends to zero through nonzero values, from both sides. AETangentAndSpeed(z,T) asserts this TangentAndSpeed(z,t) almost everywhere. The almost-everywhere "
                        + "quantifier uses volume restricted to the closed interval [0,T].")),
                    Paragraph(Text(
                        "SpeedAEMeasurable(z,T) means AEMeasurable of t mapped to the ENNReal norm "
                        + "of (mfderiv IR I z t)(1), for volume restricted to [0,T]. "
                        + "It asserts almost-everywhere measurability, without adding an energy-integrability "
                        + "premise or concluding an energy or action identity."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Derivation of the chart partition. The lower half of canonical_pairwise_local_comparison "
                + "at tolerance one half, together with the chart/inverse-chart derivative identity, gives "
                + "a genuine chart Lipschitz bound. Metric AC gives continuity: for each fixed t, distance "
                + "to z(t) is a 1-Lipschitz real-valued composition, hence AC and continuous, and the metric "
                + "distance-limit criterion recovers continuity of z. The continuous restricted curve pulls "
                + "the chart neighborhoods back to an open cover of [0,T]. The compact-interval open-cover "
                + "partition gives tau; Lipschitz composition and interval restriction give coordinate AC.")),
            Paragraph(Text(
                "Derivation of the tangent formula. Each coordinate AC curve is of bounded variation "
                + "and differentiable almost everywhere. Remove the countable partition times and the "
                + "endpoints, which have zero volume. Every remaining time lies inside a subordinate "
                + "partition interval, and continuity and coordinate differentiability give actual manifold "
                + "differentiability. In any admissible chart, the manifold chain rule and the inverse-chart "
                + "derivative identity yield the stated tangent vector formula.")),
            Paragraph(Text(
                "Derivation of intrinsic speed. Fix a manifold differentiability time t, put p=z(t), "
                + "phi=extChartAt I p, A=mfderiv I I phi.symm (phi(p)), and r=norm(v(t)). The chart "
                + "derivative limit gives Q(h)=norm(A(phi(z(t+h))-phi(p)))/abs(h) tending to r. For every "
                + "small positive epsilon the canonical pairwise comparison on a neighborhood of p gives "
                + "(1-epsilon)Q(h) <= D(h) <= (1+epsilon)Q(h), where "
                + "D(h)=dist_g(z(t+h),z(t))/abs(h). Continuity places the moving point in that neighborhood. "
                + "For any delta>0 choose epsilon=min(1/2,delta/(4*(r+1))); eventually Q<=r+1, "
                + "abs(Q-r)<delta/4, and abs(D-Q)<=epsilon*Q<=delta/4. This proves the two-sided "
                + "punctured limit without dividing by r.")),
            Paragraph(Text(
                "Derivation of measurability. Project real time continuously onto [0,T] and compose "
                + "with the restricted curve to get a continuous extension c. The continuous quotients "
                + "(n+1)*dist_g(c(t+1/(n+1)),c(t)) are measurable. At almost every interior time their "
                + "limit, by the speed theorem, is norm(v(t)). The measurable almost-everywhere limit "
                + "and conversion of the nonnegative norm to ENNReal give SpeedAEMeasurable.")),
            Paragraph(Text(
                "The proof includes E of dimension zero and zero tangent velocity. No positive-dimension, "
                + "nonzero-speed, completeness, finite-energy, extra curve Lipschitz, or supplied chart-comparison "
                + "assumption is introduced. The source requires T>0 and makes no claim for T<=0. "
                + "Its statements about derivatives and speed are almost everywhere on the restricted interval; "
                + "they do not assert endpoint differentiability. The private metric_AC_continuousOn helper "
                + "is consumed by chart_AC_partition, ae_actual_mdifferentiable and actual_speed_aemeasurable. "
                + "It is structural support, with no separately claimed escape result.")),
            Paragraph(Text(
                "The C2/C3 public result retains the canonicalMetric and canonical_pairwise_local_comparison "
                + "dependency from ChartComparison. The full energy, action, geodesic and non-shortest "
                + "conclusions of the original larger problem remain open. The single public root has one unfinished registration audit and zero declared_validated records, disclosed at https://github.com/the-omega-institute/trureturing/issues/19386 under the linked-issue delivery rule. This issue supplies no mathematical proof or registration validation."))),
        []));

    private static Formula X(string name) => F.Id(name);

    private static Formula Statement() =>
        All("E", X("FiniteDimensionalRealInnerProductSpace"),
            All("M", Call("Geometry", X("E")),
                All("T", X("Real"), All("z", Call("RealTo", X("M")),
                    Implies(And(Lt(Num(0), X("T")), Call("ACg", X("z"), Num(0), X("T"))),
                        And(Call("ChartPartition", X("z"), X("T")),
                            And(Call("AETangentAndSpeed", X("z"), X("T")),
                                Call("SpeedAEMeasurable", X("z"), X("T")))))))));

    private static Formula All(string n, Formula d, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
}
