using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Carrier;

internal sealed class NormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S0/Carrier/Norm",
            "The golden norm is multiplicative and agrees with the scaled mathlib norm."),
        H("Golden Norm"),
        Blocks(
            Paragraph(
                Ref("D5/S0/Carrier/Norm"),
                Text(" defines `N(a+b*phi)=a^2+ab-b^2`. Multiplying an element by its conjugate eliminates the `phi` coordinate and produces this integer, which makes the multiplicativity proof a direct polynomial identity.")),
            Paragraph(
                Text("Under the doubled `Zsqrtd 5` coordinates from the carrier module, the mathlib norm is exactly four times the golden norm. This factor is the expected square of the coordinate scaling.")),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("two-square-norm-as-a-shared-interpretive-core"),
                H("The two-square norm as a shared interpretive core"),
                DescribeStatement.FromFormula(Equal(
                    Call("gaussianNorm", Id("a"), Id("b")),
                    Add(
                        new Formula.Power(Id("a"), Num(2)),
                        new Formula.Power(Id("b"), Num(2))))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The source groups a^2+b^2 under four roles: the defining two-axis norm, the Gaussian norm, the modulus-four obstruction, and the splitting reading modulo a prime. It states that each role has its own theorem and that norm multiplicativity is the pivot used in the composition step. The vocabulary in which primes congruent to one split, primes congruent to three remain inert, and two ramifies is explicitly interpretive: the classification theorem is said not to depend on that Gaussian-integer language. A separate dynamical role is referenced but not added as a claim of this module.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("norm-euclidean-division"),
                H("Norm-Euclidean division"),
                LeanTheorem(
                    "D5/S0/Carrier/Euclidean.golden_division"),
                new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("b")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Z"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenBracket), new Formula.LatexMacro(FormulaLatexMacro.Varphi), new Formula.LatexSymbol(FormulaLatexSymbol.CloseBracket), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexWord(FormulaIdentifier.Create("b")), new Formula.LatexMacro(FormulaLatexMacro.Neq), new Formula.LatexSpace(), new Formula.LatexDigits([0]), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Rightarrow), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Exists), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("q")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("r")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Z"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenBracket), new Formula.LatexMacro(FormulaLatexMacro.Varphi), new Formula.LatexSymbol(FormulaLatexSymbol.CloseBracket), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexWord(FormulaIdentifier.Create("qb")), new Formula.LatexSymbol(FormulaLatexSymbol.Plus), new Formula.LatexWord(FormulaIdentifier.Create("r")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Land), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("r")), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexDigits([0]), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Lor), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Lvert), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("norm"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("r")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Rvert), new Formula.LatexSymbol(FormulaLatexSymbol.LessThan), new Formula.LatexMacro(FormulaLatexMacro.Lvert), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("norm"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("b")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Rvert), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis)])),
                DescribeProvenance.LiteratureAttested(
                    LibraryNoteRef.Create("D5/L/Carrier/chatland1949euclidean")),
                Blocks(
                    Paragraph(Text(
                        "For `a` and nonzero `b`, divide `a * conj(b)` by the nonzero integer `N(b)` and round both rational coordinates in the integral basis `(1, phi)`. Mathlib's nearest-integer operation makes the tie rule deterministic.")),
                    Paragraph(Text(
                        "If the two coordinate errors are `x` and `y`, then each has absolute value at most `1/2`. Completing squares bounds `|x^2 + xy - y^2|` by `5/16`, so multiplicativity of the norm gives a remainder with strictly smaller absolute norm.")),
                    Paragraph(Text(
                        "The `EuclideanDomain GoldenInt` instance uses this quotient and remainder with Euclidean relation `(N(r)).natAbs < (N(b)).natAbs`.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("principal-ideal-domain"),
                H("Principal ideal domain"),
                LeanTheorem(
                    "D5/S0/Carrier/PrincipalIdeal.golden_int_is_pid"),
                new Formula.Layout(FormulaLayoutMode.Inline, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Z"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenBracket), new Formula.LatexMacro(FormulaLatexMacro.Varphi), new Formula.LatexSymbol(FormulaLatexSymbol.CloseBracket), new Formula.LatexMacro(FormulaLatexMacro.Text), new Formula.LatexGroup([new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("is")), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("principal")), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("ideal")), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("domain")), new Formula.LatexSymbol(FormulaLatexSymbol.Period)])])),
                DescribeProvenance.LiteratureAttested(
                    LibraryNoteRef.Create("D5/L/Carrier/chatland1949euclidean")),
                Blocks(
                    Paragraph(Text(
                        "The norm-Euclidean structure supplies `IsPrincipalIdealRing GoldenInt` through mathlib's generic Euclidean-domain instance, so every ideal of `GoldenInt` is generated by one element.")),
                    Paragraph(Text(
                        "Mathlib's generic principal-ideal-domain instance then supplies `UniqueFactorizationMonoid GoldenInt`; the formal node records this consequence as `golden_int_is_ufd` without declaring redundant specialized instances.")),
                    Paragraph(Text(
                        "This result does not classify the units of `GoldenInt`. The converse assertion that every norm-unit is a signed integral power of `phi` remains open in `D5-T0008`.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("golden-norm-is-power-multiplicative"),
                H("The golden norm is power-multiplicative"),
                LeanTheorem(
                    "D5/S0/Carrier/NormPowers.norm_pow"),
                new Formula.Layout(FormulaLayoutMode.Inline, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("Z"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenBracket), new Formula.LatexMacro(FormulaLatexMacro.Varphi), new Formula.LatexSymbol(FormulaLatexSymbol.CloseBracket), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("n")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("N"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("norm"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSymbol(FormulaLatexSymbol.Caret), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("n"))]), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("norm"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("x")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Caret), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("n"))])])),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The golden norm is a monoid homomorphism from `GoldenInt` to the integers, packaged as `normMonoidHom` out of its unit and multiplicativity laws. The norm of a power is therefore the same power of the norm, obtained directly as `map_pow normMonoidHom` rather than by a coordinate induction.")))
            ))));
}
