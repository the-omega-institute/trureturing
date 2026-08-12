using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence.MeanKernels;

internal sealed class MeanKernelLowerTowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The logarithmic-mean reciprocal kernel is bounded above by the geometric, harmonic and squared-geometric reciprocal kernels.",
        H("The Lower Reciprocal-Mean Tower"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("logarithmic-mean-kernel-below-geometric-harmonic-and-squared-geometric"),
                DeclarationHandle.Create("D5/S3/Divergence/MeanKernels/MeanKernelLowerTower.mean_kernel_lower_tower"),
                H("The logarithmic-mean kernel is bounded above by the geometric, harmonic and squared-geometric kernels"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("a"), Comma, F.Id("b"), Comma, Sp,
                    D(0), Lt, F.Id("a"), Sp, Rightarrow, Sp,
                    D(0), Lt, F.Id("b"), Sp, Rightarrow, Sp,
                    F.Id("a"), Neq, Sp, F.Id("b"), Sp, Rightarrow, Sp,
                    F.Id("a"), Plus, F.Id("b"), Le, D(2), Sp, Rightarrow, RowBreak,
                    Frac, Grp(Log, Sp, F.Id("a"), Minus, Log, Sp, F.Id("b")), Grp(F.Id("a"), Minus, F.Id("b")),
                    Le, Sp,
                    Frac, Grp(D(1)), Grp(Sqrt, Grp(F.Id("a"), F.Id("b"))),
                    Le, Sp,
                    Frac,
                    Grp(F.Id("a"), Caret, Grp(Minus, D(1)), Plus, F.Id("b"), Caret, Grp(Minus, D(1))),
                    Grp(D(2)),
                    Le, Sp,
                    Frac, Grp(D(1)), Grp(F.Id("a"), F.Id("b"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For distinct positive reals a and b whose sum is at most 2, the reciprocal kernel of "
                        + "the logarithmic mean, (log a − log b)/(a − b), is bounded above in turn by the "
                        + "reciprocal kernel of the geometric mean, 1/√(ab), the reciprocal kernel of the "
                        + "harmonic mean, (a⁻¹ + b⁻¹)/2, and the reciprocal kernel of the squared geometric "
                        + "mean, 1/(ab). Inverting the kernels, this is the mean chain H(a,b) ≤ G(a,b) ≤ L(a,b) "
                        + "of the harmonic, geometric and logarithmic means, together with the endpoint "
                        + "G(a,b)² ≤ H(a,b), which holds exactly when a + b ≤ 2.")),
                    Paragraph(Text(
                        "The two scale-invariant steps reduce to a one-variable inequality in u = √(a/b) ≥ 1 "
                        + "(taken by symmetry of the kernels under exchanging a and b). The geometric–logarithmic "
                        + "step G ≤ L is 2u·log u ≤ u² − 1, i.e. log u ≤ (u − 1/u)/2, which is the statement that "
                        + "a real number is at most its hyperbolic sine, applied at log u ≥ 0. The harmonic step "
                        + "H ≤ G is the arithmetic–geometric mean inequality 2√(ab) ≤ a + b. The endpoint "
                        + "G² ≤ H, by contrast, is scale-dependent: (a⁻¹ + b⁻¹)/2 ≤ 1/(ab) rearranges directly "
                        + "to a + b ≤ 2.")),
                    Paragraph(Text(
                        "This is not a restatement of a library lemma: a search of Mathlib finds the logarithm "
                        + "quotient and power laws, the arithmetic–geometric mean inequality, and the "
                        + "sine-hyperbolic bound, but no logarithmic mean, no geometric–logarithmic mean "
                        + "inequality G ≤ L, and no assembled reciprocal-kernel chain. Only the lower portion "
                        + "of the reciprocal-mean tower is claimed here: the top link 2/(a + b) ≤ "
                        + "(log a − log b)/(a − b) (the L ≤ A step) is recorded in the sibling logarithmic-mean "
                        + "sandwich and is not restated, and the operator divergence tower over density matrices "
                        + "that this scalar chain drives is not covered."))),
                DescribeRole.Theorem
            )),
        []));
}
