using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal;

internal sealed class MarginVanishingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S0/Diagonal/MarginVanishing",
                "Corrected KL margin bounds and the associated failure probabilities vanish "
                + "as the address cardinality grows."),
            H("Vanishing Linear-Margin Failure"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("corrected-linear-margin-bound"),
                    DeclarationHandle.Create("D5/S0/Diagonal/MarginVanishing.linearMarginBound"),
                    H("Corrected linear-margin bound"),
                    StatementSource.FromLean(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "At address cardinality A, the bound is A times the exponential of "
                        + "minus A minus one times the Bernoulli KL divergence. Its first "
                        + "parameter is the corrected alpha A divided by A minus one, and its "
                        + "second parameter is the fixed nonzero-choice density."))),
                    DescribeRole.Definition
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("corrected-bound-vanishes"),
                    H("The corrected bound vanishes"),
                    LeanTheorem(
                        "D5/S0/Diagonal/MarginVanishing.linear_margin_bound_tendsto_zero"),
                    Disp(Seq(
                        Lim, Underscore, Grp(F.Id("A"), To, Infty),
                        Call("linearMarginBound", F.Id("n"), F.Id("alpha"), F.Id("A")),
                        Eq, D(0), Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "For fixed n at least two and alpha strictly between zero and "
                            + "(n-1)/n, the corrected bound tends to zero. Continuity of the "
                            + "frozen Bernoulli KL divergence gives a strictly positive limiting "
                            + "rate, and the standard real-power times negative-exponential "
                            + "asymptotic dominates the linear factor.")),
                        Paragraph(Text(
                            "This limit does not claim that every finite prefix is monotone. "
                            + "For n=2 and alpha=1/4, the complete union bound increases on "
                            + "A=3 through A=8 before its eventual decrease.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("failure-probability-vanishes"),
                    H("The actual failure probability vanishes"),
                    LeanTheorem(
                        "D5/S0/Diagonal/MarginVanishing.margin_failure_probability_tendsto_zero"),
                    Disp(Seq(
                        Lim, Underscore, Grp(F.Id("A"), To, Infty),
                        Call("marginFailureProbability", F.Id("f"), F.Id("alpha")),
                        Eq, D(0), Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For a fixed finite value type and a fixed diagonal map, instantiate the "
                        + "address type by Fin A. The finite theorem from MarginBound supplies the "
                        + "eventual upper bound, so nonnegativity and the vanishing corrected "
                        + "bound squeeze the actual failure probability to zero.")))
                )),
            [
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Diagonal/MarginBound")),
            ]));

}
