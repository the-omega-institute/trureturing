using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class DivisorAssociation5040Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/DivisorAssociation5040.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The 5040 divisor count and the four-block association quotient are joined by explicit finite cardinality anchors.",
        H("5040 Association Cardinality Anchors"),
        Blocks(
            Paragraph(Text("The general association theorem counts sources and observed positions for "
                + "every finite exponent box. This document records the exact specialization for the "
                + "four-prime 5040 box and connects its sixty source coordinates to the existing "
                + "positive-divisor count.")),
            Entry("box_card", "Finite source-box cardinality",
                "The box (A,B,C,D) has (A+1)(B+1)(C+1)(D+1) sources.", DescribeRole.Theorem),
            Entry("box_card_5040", "The 5040 source count",
                "The (4,2,1,1) exponent box has exactly 60 sources.", DescribeRole.Theorem),
            Entry("image_card_5040", "The 5040 observed-position count",
                "The association image of the (4,2,1,1) box has exactly 48 positions, by the "
                    + "general image-card formula.", DescribeRole.Theorem),
            Entry("divisor_5040_card_eq_box_card", "Divisor/source count interface",
                "The existing GoldenDivisorLanguage theorem Nat.card (Div 5040)=60 is identified "
                    + "with the cardinality of the association source box. This is a finite count "
                    + "interface only; it does not identify the q coordinates with all divisor data "
                    + "and does not assert Robin's inequality or RH.", DescribeRole.Theorem),
            Paragraph(Text("These anchors are intended as exact consumers for later source lifts. "
                + "The 48-position quotient and the 60-source divisor count remain finite checks "
                + "inside the already-proved general formula."))
        )));

    private static DocumentBlock Entry(string selector, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(selector.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
