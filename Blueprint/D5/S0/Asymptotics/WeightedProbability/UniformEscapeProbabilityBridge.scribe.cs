using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.WeightedProbability;

internal sealed class UniformEscapeProbabilityBridgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var b = F.Id("b");
        var f = F.Id("f");
        var y = F.Id("Y");
        var z = F.Id("y");
        var uniformWeight = Seq(
            Open, Open, b, Comma, Sp, z, Close, Sp, Mapsto, Sp,
            new Formula.Fraction(D(1), Seq(Lvert, Sp, y, Rvert)), Close);
        var weightedEscape = Seq(
            Operatorname, Grp(F.Id("escapeProbability")),
            Underscore, Grp(F.Id("weighted")),
            Open, uniformWeight, Comma, Sp, f, Close);
        var countingEscape = Seq(
            Operatorname, Grp(F.Id("escapeProbability")),
            Underscore, Grp(F.Id("counting")), Open, f, Close);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Uniform cell weights identify weighted escape probability with the frozen counting probability.",
            H("Uniform Escape Probability Bridge"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("uniform-weighted-escape-is-counting-escape"),
                    DeclarationHandle.Create(
                        "D5/S0/Asymptotics/WeightedProbability/UniformEscapeProbabilityBridge."
                        + "uniform_escapeProbability_eq_counting"),
                    H("Uniform weighted escape is counting escape"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, f, Colon, Sp, y, Sp, To, Sp, y, Comma, Esc,
                        weightedEscape, Sp, Eq, Sp, countingEscape, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let A and Y be finite types, let A have decidable equality, and let f map Y to Y. "
                            + "The weighted escape probability uses the constant marginal 1/card(Y) in every cell. "
                            + "The counting escape probability is the frozen ratio of escaped matrices to all matrices.")),
                        Paragraph(Text(
                            "The public listingEquiv reassembles a diagonal and all off-row coordinates into a matrix. "
                            + "Restricting that equivalence with no_capture_iff_isEscaped identifies the two event subtypes. "
                            + "The uniform sample weight is independently proved to be the reciprocal of the matrix-space cardinality.")),
                        Paragraph(Text(
                            "No Nonempty instance for A or Y, no DecidableEq instance for Y, and no LinearOrder instance for A is required. "
                            + "The exponent calculation also covers empty types, so the theorem states the exact finite hypotheses used by the two definitions.")),
                        Paragraph(Text(
                            "Repository search found the coordinate equivalence only in two private frozen declarations and found no probability bridge. "
                            + "Pinned Mathlib supplies subtype-equivalence, cardinal-congruence, function-cardinality, and finite sum/product lemmas, which are reused here."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Asymptotics/WeightedProbability/FiniteBonferroni")),
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Asymptotics/FixedPointFreeEscapeProbability")),
            ]));
    }
}
