using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.WeightedProbability;

internal sealed class FiniteProductCaptureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var y = F.Id("y");
        var qby = Seq(F.Id("q"), Underscore, Grp(b), Open, y, Close);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Independent column-weighted finite listings have an exact one-row twisted-diagonal capture mass.",
            H("Finite Product Capture Law"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("one-row-weighted-capture-law"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/WeightedProbability/FiniteProductCapture."
                        + "capture_probability_exact"),
                    H("Exact one-row weighted capture probability"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Open, Forall, Sp, b, Comma, Esc,
                        Sum, Underscore, Grp(y), Sp, qby, Sp, Eq, Sp, D(1), Close,
                        Sp, Rightarrow, Sp,
                        Forall, Sp, a, Comma, Esc,
                        Call("captureProbability", F.Id("q"), F.Id("f"), a),
                        Sp, Eq, Sp,
                        Call("fixedMass", F.Id("q"), F.Id("f"), a), Sp,
                        Prod, Underscore, Grp(b, Neq, Sp, a), Sp,
                        Call("collisionMass", F.Id("q"), F.Id("f"), b), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The sample stores the listing diagonal and each off-diagonal row as independent coordinates, and reassembly uses EscapeCount.diagonal.")),
                        Paragraph(Text(
                            "Summing the free rows gives one; the captured row leaves exactly fixedMass and the remaining column collisionMass factors."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Diagonal/EscapeCount")),
            ]));
    }
}
