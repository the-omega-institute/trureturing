using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class KnasterTarskiDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Dynamics/KnasterTarski",
                "Monotone endomorphisms have extremal fixed points, separated by a three-state cycle."),
            H("Knaster-Tarski Extremal Fixed Points"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("least-and-greatest-fixed-points"),
                    H("Least and greatest fixed points"),
                    LeanTheorem(
                        "D5/S1/Dynamics/KnasterTarski.knaster_tarski_extremal_fixed_points"),
                    new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexWord(FormulaIdentifier.Create("f")), new Formula.LatexSymbol(FormulaLatexSymbol.Colon), new Formula.LatexWord(FormulaIdentifier.Create("L")), new Formula.LatexMacro(FormulaLatexMacro.To), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("L")), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Text), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("monotone"))]), new Formula.LatexMacro(FormulaLatexMacro.Rightarrow), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Mu), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("lfp"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("f")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Min), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Fix"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("f")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Nu), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("gfp"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("f")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Max), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Fix"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("f")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Period)])),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "The classical Knaster-Tarski theorem states that every monotone "
                            + "endomorphism of a complete lattice has a least fixed point and a "
                            + "greatest fixed point. The Lean declaration is an honest "
                            + "repository wrapper around Mathlib's least and greatest fixed-point "
                            + "constructions and their extremality theorems. No repository "
                            + "literature note currently attests the classical source, so the "
                            + "provenance is conservatively recorded as repository-derived rather "
                            + "than literature-attested.")))
                ),
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("three-state-successor-cycle"),
                    H("Three-state successor cycle"),
                    LeanTheorem(
                        "D5/S1/Dynamics/KnasterTarski.three_cycle_extremal_fixed_points"),
                    new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("X")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.OpenBrace), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexMacro(FormulaLatexMacro.Mid), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("succ"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("X")), new Formula.LatexMacro(FormulaLatexMacro.CloseBrace), new Formula.LatexMacro(FormulaLatexMacro.Rightarrow), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("lfp"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Varnothing), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("gfp"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("F")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexWord(FormulaIdentifier.Create("S")), new Formula.LatexSymbol(FormulaLatexSymbol.Period)])),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "On the three-state successor cycle, the induced powerset operator is "
                            + "inverse image under succession. It preserves the empty set and the "
                            + "full carrier; extremality therefore identifies the least fixed point "
                            + "with the empty set and the greatest fixed point with the full set. "
                            + "The inductive interpretation has no grounded state from which to "
                            + "begin, whereas the coinductive interpretation accepts the entire "
                            + "self-sustaining cycle.")))
                ))));
}
