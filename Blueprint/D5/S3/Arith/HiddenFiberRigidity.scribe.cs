using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class HiddenFiberRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Arith/HiddenFiberRigidity",
            "A continuous map from a connected real interval into the profinite fiber product is constant."),
        H("Rigidity of the Hidden Profinite Fiber"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("a-continuous-interval-map-into-the-profinite-fiber-is-constant"),
                H("A continuous interval map into the profinite fiber is constant"),
                LeanTheorem(
                    "D5/S3/Arith/HiddenFiberRigidity.hidden_fiber_rigidity"),
                new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Subseteq), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("R"))]), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Text), new Formula.LatexGroup([new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("preconnected"))]), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Land), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("f")), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.Colon), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.To), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Prod), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("p")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Text), new Formula.LatexGroup([new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("prime"))])]), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Z"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexWord(FormulaIdentifier.Create("p")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Text), new Formula.LatexGroup([new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("continuous"))]), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Rightarrow), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("y")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexWord(FormulaIdentifier.Create("f")), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("f")), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("y")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis)])),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The hidden fiber K_infinity is the product of the rings of p-adic integers over "
                        + "all primes, carrying the product topology under which a map is continuous exactly "
                        + "when each coordinate reading into a single p-adic factor is continuous. The theorem "
                        + "fixes an arbitrary preconnected subset s of the real line as the domain and a map f "
                        + "continuous on s into this fiber product, and concludes that f is constant on s: any "
                        + "two arguments in s share the same image. The preconnected hypothesis is not a "
                        + "weakening of the informal connected interval but its exact characterization, since "
                        + "the preconnected subsets of the real line are precisely its intervals; the "
                        + "conclusion therefore covers every connected real interval without loss.")),
                    Paragraph(Text(
                        "The proof is the profinite reading of the informal layerwise argument. Each factor is "
                        + "an ultrametric metric space, hence totally separated and a fortiori totally "
                        + "disconnected; the arbitrary product of totally disconnected spaces is again totally "
                        + "disconnected, so the fiber product is totally disconnected. The continuous image of "
                        + "the preconnected domain is preconnected, and a preconnected subset of a totally "
                        + "disconnected space is a subsingleton. The two candidate images thus coincide. The "
                        + "layerwise projection to a discrete residue quotient of the informal proof is "
                        + "subsumed here by total disconnectedness of the factors, which is the topological "
                        + "content of the reading being single-valued on any connected source. The result is "
                        + "purely topological: it asserts no arithmetic of the p-adic factors and no numerical "
                        + "certificate.")))
            ))));
}
