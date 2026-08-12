using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal;

internal sealed class MarginBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var cardA = Call("card", Id("A"));
        var cardY = Call("card", Id("Y"));
        var alpha = Id("alpha");
        var q = new Formula.Fraction(
            Multiply(alpha, cardA),
            Subtract(cardA, Num(1)));
        var p = new Formula.Fraction(
            Subtract(cardY, Num(1)),
            cardY);
        var exponent = Multiply(
            Subtract(Num(0), Subtract(cardA, Num(1))),
            Call("bernoulliKL", q, p));
        var bound = Multiply(cardA, Call("exp", exponent));

        return DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S0/Diagonal/MarginBound",
                "Finite diagonal listings satisfy a corrected KL-Chernoff linear-margin bound."),
            H("Diagonal Linear Margin Bound"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("bernoulli-kl-divergence"),
                    DeclarationHandle.Create("D5/S0/Diagonal/MarginBound.bernoulliKL"),
                    H("Bernoulli KL divergence"),
                    StatementSource.FromLean(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The scalar Bernoulli divergence is q log(q/p) plus one minus q "
                        + "times log((1-q)/(1-p)). Its local nonnegativity, strict positivity "
                        + "off the diagonal, and continuity are proved on the open unit square."))),
                    DescribeRole.Definition
                ),
                Describe.Lean(
                    DescribeId.Create("finite-margin-failure-probability"),
                    DeclarationHandle.Create("D5/S0/Diagonal/MarginBound.marginFailureProbability"),
                    H("Finite margin-failure probability"),
                    StatementSource.FromLean(),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The probability is the finite cardinality ratio of listings having "
                        + "some row at Hamming distance below alpha times the address "
                        + "cardinality, divided by the cardinality of all listings."))),
                    DescribeRole.Definition
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("linear-margin-has-corrected-kl-bound"),
                    H("A linear margin has the corrected KL bound"),
                    LeanTheorem("D5/S0/Diagonal/MarginBound.linear_margin_bound"),
                    FormulaDsl.Disp(new Formula.Relation(
                        Call("marginFailureProbability", Id("f"), alpha),
                        FormulaRelationOperator.LessThanOrEqual,
                        bound)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For finite address and value types with cardinalities at least two, "
                        + "positive alpha, and q less than p, the failure probability is at "
                        + "most the address cardinality times exp(-(card(A)-1) KL(q||p)), "
                        + "where q is alpha card(A)/(card(A)-1) and p is "
                        + "(card(Y)-1)/card(Y). The corrected q is retained in the displayed "
                        + "exponent. The proof combines the frozen minimum-distance tail, a "
                        + "rowwise union bound, the exact binomial moment-generating function, "
                        + "and the KL-Chernoff lower tail.")),
                    Paragraph(Text(
                        "The limit as the address cardinality tends to infinity and the "
                        + "two-sided concentration of minimum distance density are deferred; "
                        + "neither asymptotic statement is claimed by this finite theorem.")))
                )),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Diagonal/DistanceProfile")),
            ]));
    }

}
