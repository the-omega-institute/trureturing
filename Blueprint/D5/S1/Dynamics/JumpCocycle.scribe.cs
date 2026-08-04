using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class JumpCocycleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Dynamics/JumpCocycle",
                "Hidden-fiber jump legality is exactly cocycle consistency."),
            H("Hidden-Fiber Jump Cocycle"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("hidden-fiber-jump-cocycle"),
                    H("Hidden-fiber jump legality is cocycle consistency"),
                    LeanTheorem(
                        "D5/S1/Dynamics/JumpCocycle.jump_cocycle"),
                    new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Beta)]), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Alpha)]), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexMacro(FormulaLatexMacro.Iota), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Alpha), new Formula.LatexMacro(FormulaLatexMacro.Beta)]), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.Quad), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.GammaLower)]), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Beta)]), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexMacro(FormulaLatexMacro.Iota), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Beta), new Formula.LatexMacro(FormulaLatexMacro.GammaLower)]), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Rightarrow), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Left), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.GammaLower)]), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Alpha)]), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexMacro(FormulaLatexMacro.Iota), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Alpha), new Formula.LatexMacro(FormulaLatexMacro.GammaLower)]), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Leftrightarrow), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Alpha), new Formula.LatexMacro(FormulaLatexMacro.GammaLower)]), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Alpha), new Formula.LatexMacro(FormulaLatexMacro.Beta)]), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexWord(FormulaIdentifier.Create("k")), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexMacro(FormulaLatexMacro.Beta), new Formula.LatexMacro(FormulaLatexMacro.GammaLower)]), new Formula.LatexMacro(FormulaLatexMacro.Right), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis)])),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "Over a nonempty indexing domain, the visible circle projection is a "
                            + "surjective additive homomorphism. An additive equivalence "
                            + "identifies "
                            + "the product of all p-adic integer fibers with its kernel. Two "
                            + "realized hidden jumps connect three local lifts. Kernel membership "
                            + "first forces "
                            + "all three lifts to have the same visible projection.")),
                        Paragraph(Text(
                            "A proposed direct jump is legal when translating the first lift by "
                            + "that jump reaches the third lift. This endpoint condition is "
                            + "independent of the cocycle equation. Cancelling the first lift, "
                            + "applying additivity, "
                            + "and using injectivity of the kernel equivalence prove that endpoint "
                            + "legality is equivalent to the pointwise sum of the two intervening "
                            + "jumps. Any disagreement therefore supplies an explicit endpoint "
                            + "residual and cannot be a legal motion.")))
                ))));
}
