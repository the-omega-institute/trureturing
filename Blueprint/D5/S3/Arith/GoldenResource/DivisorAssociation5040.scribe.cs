using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

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
                "The box (A,B,C,D) has (A+1)(B+1)(C+1)(D+1) sources.", BoxCardFormula(), DescribeRole.Theorem),
            Entry("box_card_5040", "The 5040 source count",
                "The (4,2,1,1) exponent box has exactly 60 sources.", BoxCard5040Formula(), DescribeRole.Theorem),
            Entry("image_card_5040", "The 5040 observed-position count",
                "The association image of the (4,2,1,1) box has exactly 48 positions, by the "
                    + "general image-card formula.", ImageCard5040Formula(), DescribeRole.Theorem),
            Entry("divisor_5040_card_eq_box_card", "Divisor/source count interface",
                "The existing GoldenDivisorLanguage theorem Nat.card (Div 5040)=60 is identified "
                    + "with the cardinality of the association source box. This is a finite count "
                    + "interface only; it does not identify the q coordinates with all divisor data "
                + "and does not assert Robin's inequality or RH.", DivisorCardFormula(), DescribeRole.Theorem),
            Paragraph(Text("These anchors are intended as exact consumers for later source lifts. "
                + "The 48-position quotient and the 60-source divisor count remain finite checks "
                + "inside the already-proved general formula."))
        )));

    private static DocumentBlock Entry(string selector, string title, string prose, Formula formula,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(selector.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula BoxCardFormula() =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [Bound("A"), Bound("B"), Bound("C"), Bound("D")],
            Equal(Card(Box(Id("A"), Id("B"), Id("C"), Id("D"))),
                Multiply(Multiply(Multiply(Add(Id("A"), D(1)), Add(Id("B"), D(1))),
                    Add(Id("C"), D(1))), Add(Id("D"), D(1)))));

    private static Formula BoxCard5040Formula() => Equal(Card(Box(D(4), D(2), D(1), D(1))), D(6, 0));

    private static Formula ImageCard5040Formula() =>
        Equal(Card(Call("image", F.Id("q"), Box(D(4), D(2), D(1), D(1)))), D(4, 8));

    private static Formula DivisorCardFormula() =>
        Equal(Call("NatCard", Call("Div", D(5, 0, 4, 0))), Card(Box(D(4), D(2), D(1), D(1))));

    private static Formula.BoundVariable Bound(string name) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), Seq(Mathbb, Grp(F.Id("N"))));

    private static Formula Id(string name) => F.Id(name);
    private static Formula Box(params Formula[] args) => Call("box", args);
    private static Formula Card(Formula value) => Call("card", value);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
