using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk;

internal sealed class CriterionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/Criterion.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Hamming/ide2026scaling");

    private static Formula RhoLaw(string time) =>
        Seq(Nu, Underscore, Grp(F.Id(time), Comma, F.Id("d")));

    private static Formula ToLimit(string time) => Seq(RhoLaw(time), Sp, To, Sp, Pi);

    private static Formula BothLimits() =>
        Seq(Open, ToLimit("C"), Sp, Land, Sp, ToLimit("D"), Close);

    private static Formula PositiveOrder() => Seq(Forall, Sp, F.Id("k"), Gt, D(0), Comma, Sp);

    private static Formula GapLimit() =>
        Seq(Delta, Underscore, Grp(F.Id("d"), Comma, F.Id("k")), Sp, To, Sp, D(0));

    private static Formula CollisionLimit(Formula moment) =>
        Seq(F.Id("B"), Underscore, Grp(F.Id("d"), Comma, F.Id("k")), Sp, To, Sp, moment);

    private static DocumentBlock Theorem(string id, string name, string title, Formula statement,
        params DocumentBlock[] notes) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(Source),
            Blocks(notes), DescribeRole.Theorem);

    private static DocumentBlock CoincidenceResolution(Formula statement,
        params DocumentBlock[] notes) =>
        Describe.Lean(DescribeId.Create("conditional-coincidence"),
            DeclarationHandle.Create(Prefix + "common_shell_weakLimit_iff_gap"),
            H("Coincidence when one law converges"), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(Source), Blocks(notes), DescribeRole.Theorem,
            openProblemResolutionClaim: new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("ide-konno-mano-2026-hypercube-walk-limit-coincidence"),
                ResolutionKind.Proved));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every family of symmetric hypercube walks, a common weak limit exists exactly "
        + "when all fixed-order CT–DT Walsh gaps vanish and all corresponding CT collision coefficients converge.",
        H("Coincidence of symmetric hypercube quantum-walk limits"),
        Blocks(
            Paragraph(Text(
                "In arXiv:2611.31635v1, Section 5, printed p. 14, Ide, Konno and Mano write, "
                + "“It is therefore an open problem to find a necessary and sufficient condition "
                + "for the coincidence of the scaling limits.” At each dimension d choose nonnegative weights w_d(h) for "
                + "0 ≤ h ≤ d whose sum is one. The increment law is w_d(|y|)/choose(d,|y|). "
                + "Both walks start at the origin. Take their respective Cesàro limits at fixed d, "
                + "then push the position laws forward by normalized Hamming weight |x|/d. "
                + "Write ν_{C,d} and ν_{D,d} for the resulting probability laws on [0,1]. "
                + "All displayed arrows are along the full sequence d → ∞ and denote weak convergence for laws. "
                + "The source starts at d ≥ 3. Extending the weights at the finitely many smaller dimensions "
                + "has no effect on these limits.")),
            Theorem("common-weak-limit", "exists_common_shell_weakLimit_iff",
                "Existence of a common weak limit",
                Seq(Open, Exists, Sp, Pi, Comma, Sp, BothLimits(), Close, Sp, Iff, Sp, PositiveOrder(),
                    Open, GapLimit(), Sp, Land, Sp, Open, Exists, Sp, F.Id("m"), Comma, Sp,
                    CollisionLimit(F.Id("m")), Close, Close),
                Paragraph(Text(
                    "B_{d,k} is the CT coefficient and Δ_{d,k} is CT minus DT. For fixed k and d ≥ k "
                    + "their normalized double sums use binomial weights choose(d−k,i) choose(k,j)/2^d. "
                    + "The CT coefficient counts equal numerical eigenvalues at shells i+j and i+k−j. "
                    + "The gap uses (1−ρ_k)/(2(1−ρ_{i+j}²)) at equal interior eigenvalues and zero otherwise. "
                    + "Both equal endpoints contribute one to the CT and DT coefficients and zero to the gap. At k = 0, B_{d,0} = 1 and Δ_{d,0} = 0.")),
                Paragraph(Text(
                    "Coordinate permutations preserve both time-averaged laws. Sampling bounds compare "
                    + "their Walsh coefficients with their shifted radial moments, with error at most k(k−1)/d "
                    + "per law. Compactness of the probability measures on [0,1] and the shifted moment "
                    + "criterion produce CT convergence from convergence of all B_{d,k}. The gap condition "
                    + "transfers this limit to DT. Conversely, both laws converging to π gives the same "
                    + "shifted moments, so every gap vanishes and every CT coefficient converges."))),
            CoincidenceResolution(
                Seq(Open, ToLimit("C"), Sp, Lor, Sp, ToLimit("D"), Close, Sp, Implies, Sp,
                    Open, BothLimits(), Sp, Iff, Sp, PositiveOrder(), GapLimit(), Close),
                Paragraph(Text(
                    "For any probability law π on [0,1], if either sequence converges weakly to π, "
                    + "the other converges to π exactly when every fixed positive-order gap vanishes. "
                    + "If existence is unknown, vanishing gaps characterize agreement in the limit on "
                    + "every continuous test, as formalized by shell_continuous_tests_gap_iff. "
                    + "As an example of the existence distinction, take deterministic zero increments "
                    + "in even dimensions and deterministic all-ones increments in odd dimensions. "
                    + "The two laws agree at each dimension, but alternate between a point mass at 0 "
                    + "and an equal mixture of the point masses at 0 and 1."))),
            Theorem("collision-limit-moments", "tendsto_shell_collisions_to_shiftedMoment",
                "Collision limits identify the limiting moments",
                Seq(ToLimit("C"), Sp, Implies, Sp, Forall, Sp, F.Id("k"), Comma, Sp,
                    CollisionLimit(Seq(Int, Underscore, Grp(OpenBracket, D(0), Comma, D(1), CloseBracket),
                        Open, D(1), Minus, D(2), F.Id("x"), Close, Caret, Grp(F.Id("k")), Sp,
                        F.Id("d"), Pi, Open, F.Id("x"), Close))),
                Paragraph(Text(
                    "For every natural k, the collision limit is the kth shifted moment of the CT limit. "
                    + "This also identifies the common limit uniquely when the gaps vanish."))))));
}
