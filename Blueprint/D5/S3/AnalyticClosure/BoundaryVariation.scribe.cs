using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class BoundaryVariationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The rational variation law tends to one third at the integer boundary.",
        H("Boundary Variation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("boundary-variation-tends-to-one-third"),
                DeclarationHandle.Create(
                    "D5/S3/AnalyticClosure/BoundaryVariation."
                    + "boundary_variation_tendsto_one_third"),
                H("The boundary variation tends to one third"),
                StatementSource.FromAuthor(Disp(Seq(
                    Lim, Underscore, Grp(F.Id("beta"), To, D(2)), Sp,
                    Frac,
                    Grp(F.Id("beta"), Caret, Grp(D(2)), Minus, F.Id("beta"), Minus, D(1)),
                    Grp(F.Id("beta"), Caret, Grp(D(2)), Minus, D(1)),
                    Sp, Eq, Sp, Frac, Grp(D(1)), Grp(D(3)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the rational variation law V(beta) = "
                        + "(beta^2 - beta - 1)/(beta^2 - 1), the denominator is nonzero at "
                        + "beta = 2. Continuity of powers, subtraction, and division therefore "
                        + "makes the limit equal to the value at that boundary, namely 1/3.")),
                    Paragraph(Text(
                        "The Lean proof directly reuses Mathlib's ContinuousAt.div after "
                        + "checking the nonzero denominator, then normalizes the boundary value.")),
                    Paragraph(Text(
                        "This closes only the boundary-continuity sentence in remark 27.781, "
                        + "clause 2. It does not derive the variation formula for the beta family, "
                        + "the d >= 3 values, or the separate degenerate d = 2 case."))),
                DescribeRole.Theorem))));
}
