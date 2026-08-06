using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Solenoid;

internal sealed class ThroatTransitionCocycleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Solenoid/ThroatTransitionCocycle",
                "Equal visible projections determine unique hidden-fiber differences, which compose additively."),
            H("Throat-Transition Cocycle"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("three-lift-difference-cocycle"),
                    H("Visible agreement determines the hidden-fiber cocycle"),
                    LeanTheorem(
                        "D5/S1/Solenoid/ThroatTransitionCocycle."
                        + "three_lift_difference_cocycle"),
                    Disp(Seq(Pi, Circ, Sp, F.Id("s"), Underscore, Grp(Alpha), Eq, Pi, Circ, Sp, F.Id("s"), Underscore, Grp(Beta), Comma, Quad, Sp, Pi, Circ, Sp, F.Id("s"), Underscore, Grp(Beta), Eq, Pi, Circ, Sp, F.Id("s"), Underscore, Grp(GammaLower), Quad, Rightarrow, Quad, Sp, Begin, Grp(F.Id("gathered")), Exists, Bang, Thin, F.Id("k"), Underscore, Grp(Alpha, Beta), Colon, F.Id("U"), To, Mathcal, Sp, F.Id("S"), Comma, Esc, Pi, Open, F.Id("k"), Underscore, Grp(Alpha, Beta), Open, F.Id("u"), Close, Close, Eq, D(0), Comma, Esc, F.Id("s"), Underscore, Grp(Beta), Open, F.Id("u"), Close, Eq, F.Id("s"), Underscore, Grp(Alpha), Open, F.Id("u"), Close, Plus, F.Id("k"), Underscore, Grp(Alpha, Beta), Open, F.Id("u"), Close, Comma, RowBreak, Exists, Bang, Thin, F.Id("k"), Underscore, Grp(Beta, GammaLower), Colon, F.Id("U"), To, Mathcal, Sp, F.Id("S"), Comma, Esc, Pi, Open, F.Id("k"), Underscore, Grp(Beta, GammaLower), Open, F.Id("u"), Close, Close, Eq, D(0), Comma, Esc, F.Id("s"), Underscore, Grp(GammaLower), Open, F.Id("u"), Close, Eq, F.Id("s"), Underscore, Grp(Beta), Open, F.Id("u"), Close, Plus, F.Id("k"), Underscore, Grp(Beta, GammaLower), Open, F.Id("u"), Close, Comma, RowBreak, Exists, Bang, Thin, F.Id("k"), Underscore, Grp(Alpha, GammaLower), Colon, F.Id("U"), To, Mathcal, Sp, F.Id("S"), Comma, Esc, Pi, Open, F.Id("k"), Underscore, Grp(Alpha, GammaLower), Open, F.Id("u"), Close, Close, Eq, D(0), Comma, Esc, F.Id("s"), Underscore, Grp(GammaLower), Open, F.Id("u"), Close, Eq, F.Id("s"), Underscore, Grp(Alpha), Open, F.Id("u"), Close, Plus, F.Id("k"), Underscore, Grp(Alpha, GammaLower), Open, F.Id("u"), Close, Comma, RowBreak, F.Id("k"), Underscore, Grp(Alpha, GammaLower), Open, F.Id("u"), Close, Eq, F.Id("k"), Underscore, Grp(Alpha, Beta), Open, F.Id("u"), Close, Plus, F.Id("k"), Underscore, Grp(Beta, GammaLower), Open, F.Id("u"), Close, End, Grp(F.Id("gathered")), Qquad, Open, F.Id("u"), InMacro, Sp, F.Id("U"), Close, Comma)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Each difference is constructed pointwise by subtraction. "
                        + "The additive projection sends it to zero, group cancellation "
                        + "gives uniqueness, and the cocycle identity follows by "
                        + "telescoping the two successive differences."))))),
[
                                DocumentEdge.TruthAnchor.Create(
                                    LeanDeclarationRef.Create("D5/S1/Solenoid/ThroatTransitionCocycle.three_lift_difference_cocycle")),
                                DocumentEdge.Dependency.Create(
                                    GidRef.Create("D5/S1/Dynamics/UniversalSolenoid")),
                                DocumentEdge.Dependency.Create(
                                    GidRef.Create("D5/S1/Solenoid/HiddenFiberCompact")),
                            ]));
}
