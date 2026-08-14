using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.WeightedProbability;

internal sealed class FiniteProductPairCaptureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var a = F.Id("a");
        var ap = Seq(a, Apos);
        var b = F.Id("b");
        var y = F.Id("y");
        var qby = Seq(F.Id("q"), Underscore, Grp(b), Open, y, Close);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Distinct captured rows have the exact second-order weighted intersection mass.",
            H("Finite Product Pair Capture Law"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("two-row-weighted-capture-law"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/WeightedProbability/FiniteProductPairCapture."
                        + "pair_capture_probability_exact"),
                    H("Exact two-row weighted capture probability"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Open, Forall, Sp, b, Comma, Esc,
                        Sum, Underscore, Grp(y), Sp, qby, Sp, Eq, Sp, D(1), Close,
                        Sp, Rightarrow, Sp,
                        Forall, Sp, a, Comma, Sp, ap, Comma, Esc,
                        a, Neq, Sp, ap, Sp, Rightarrow, Sp,
                        Call("pairCaptureProbability", F.Id("q"), F.Id("f"), a, ap),
                        Sp, Eq, Sp,
                        Call("fixedSquareMass", F.Id("q"), F.Id("f"), a), Sp,
                        Call("fixedSquareMass", F.Id("q"), F.Id("f"), ap), Sp,
                        Prod, Underscore,
                        Grp(b, Neq, Sp, a, Comma, Sp, b, Neq, Sp, ap), Sp,
                        Call("collisionSquareMass", F.Id("q"), F.Id("f"), b), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "At the selected columns the two captured rows give fixedSquareMass; at every other column they give collisionSquareMass.")),
                        Paragraph(Text(
                            "These are the source's second-order sums of squared weights, not squares of the one-row masses."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Asymptotics/WeightedProbability/FiniteProductCapture")),
            ]));
    }
}
