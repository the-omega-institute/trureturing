using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal;

internal sealed class TypicalDensityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "The minimum diagonal-distance density concentrates between any fixed lower "
                + "and upper densities straddling the nonzero-choice density.",
            H("Typical Minimum-Distance Density"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("binomial-upper-tail-kl"),
                    DeclarationHandle.Create("D5/S0/Diagonal/TypicalDensity.binomial_upper_tail_kl"),
                    H("Binomial upper-tail KL bound"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("Pr", Call("Bin", F.Id("r"), F.Id("p")), Ge,
                            Multiply(F.Id("q"), F.Id("r"))),
                        Le, Call("exp", Subtract(D(0), Multiply(F.Id("r"),
                            Call("bernoulliKL", F.Id("q"), F.Id("p"))))), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For p below q below one, the positive exponential tilt in the standard "
                        + "moment-generating-function Chernoff inequality gives the upper-tail "
                        + "rate KL(q||p). The Bernoulli KL definition is reused from "
                        + "MarginBound."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("minimum-upper-tail-single-row"),
                    DeclarationHandle.Create("D5/S0/Diagonal/TypicalDensity.upper_failure_probability_le_row_probability"),
                    H("The minimum upper tail reduces to one row"),
                    StatementSource.FromAuthor(Disp(new Formula.Relation(
                        Call("upperFailureProbability", F.Id("f"), F.Id("alpha")),
                        FormulaRelationOperator.LessThanOrEqual,
                        Call("rowUpperProbability", F.Id("f"), F.Id("alpha"))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The event that the minimum exceeds a threshold forces every row, hence "
                        + "any fixed row, to exceed it. The exact distance-profile factorization "
                        + "makes the minimum probability a power of the single-row factor; since "
                        + "that factor lies in the unit interval, the power is no larger."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("two-sided-typical-density"),
                    DeclarationHandle.Create("D5/S0/Diagonal/TypicalDensity.typical_density_failure_probability_tendsto_zero"),
                    H("Two-sided typical density"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Lim, Underscore, Grp(F.Id("A"), To, Infty),
                        Call("typicalDensityFailureProbability", F.Id("f"),
                            new Formula.Subscript(F.Id("alpha"), F.Id("lo")),
                            new Formula.Subscript(F.Id("alpha"), F.Id("hi"))),
                        Eq, D(0), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Fix zero below alpha_lo below p below alpha_hi below one, where p is "
                        + "the nonzero-choice density (n-1)/n. The lower failure probability "
                        + "vanishes by MarginVanishing. For the upper failure, every row distance "
                        + "is at most one plus a Bin(A-1,p) count; the preceding single-row "
                        + "reduction and upper-tail KL bound make this probability vanish. A "
                        + "finite union bound combines the two sides. Thus the minimum distance "
                        + "lies in [alpha_lo A, alpha_hi A] outside a set of probability tending "
                        + "to zero."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Diagonal/MarginVanishing")),
            ]));
}
