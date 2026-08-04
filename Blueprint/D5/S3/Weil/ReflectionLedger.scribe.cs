using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class ReflectionLedgerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Weil/ReflectionLedger",
            "Conjugate reflection reverses scaling entries around the critical line."),
        H("Conjugate Reflection and Scaling"),
        Blocks(
            DocumentBlock.Describe.Proposition(
                DescribeId.Create("mirror-fixed-points-lie-on-the-critical-line"),
                H("Mirror fixed points lie on the critical line"),
                LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq"),
                new Formula.Layout(FormulaLayoutMode.Inline, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("C"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("mirror"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Rightarrow), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Re), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Frac), new Formula.LatexGroup([new Formula.LatexDigits([1])]), new Formula.LatexGroup([new Formula.LatexDigits([2])])])),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Conjugate reflection sends a spectral parameter to one minus its conjugate. Every fixed point therefore has real part one half; no zero-location claim is made.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("mirror-reverses-every-scaling-entry"),
                H("The mirror reverses every scaling entry"),
                LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_reversal_spec"),
                new Formula.Layout(FormulaLayoutMode.Display, new Formula.LatexSequence([new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("A")), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexSymbol(FormulaLatexSymbol.OpenBracket), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("AddMonoid"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("A")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.CloseBracket), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Ell), new Formula.LatexSymbol(FormulaLatexSymbol.Colon), new Formula.LatexWord(FormulaIdentifier.Create("A")), new Formula.LatexMacro(FormulaLatexMacro.To), new Formula.LatexSymbol(FormulaLatexSymbol.Underscore), new Formula.LatexGroup([new Formula.LatexSymbol(FormulaLatexSymbol.Plus)]), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("R"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexMacro(FormulaLatexMacro.In), new Formula.LatexMacro(FormulaLatexMacro.Mathbb), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("C"))]), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.EscapedSpace), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Forall), new Formula.LatexSpace(), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("scalingLedger"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Ell), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("mirror"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexSymbol(FormulaLatexSymbol.Minus), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("scalingLedger"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexMacro(FormulaLatexMacro.Ell), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.Comma), new Formula.LatexWord(FormulaIdentifier.Create("a")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Land), new Formula.LatexSpace(), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Operatorname), new Formula.LatexGroup([new Formula.LatexWord(FormulaIdentifier.Create("mirror"))]), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Leftrightarrow), new Formula.LatexSpace(), new Formula.LatexMacro(FormulaLatexMacro.Re), new Formula.LatexSymbol(FormulaLatexSymbol.OpenParenthesis), new Formula.LatexWord(FormulaIdentifier.Create("s")), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis), new Formula.LatexSymbol(FormulaLatexSymbol.Equal), new Formula.LatexMacro(FormulaLatexMacro.Frac), new Formula.LatexGroup([new Formula.LatexDigits([1])]), new Formula.LatexGroup([new Formula.LatexDigits([2])]), new Formula.LatexSymbol(FormulaLatexSymbol.CloseParenthesis)])),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For the entry given by displacement from one half times ledger length, mirroring negates every coordinate. The same theorem identifies the full fixed locus.")))
            ),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("symmetry-channel-is-not-location-force"),
                H("A symmetry channel is not a location force"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Reflection identifies the critical fixed line and can serve as a channel for spectral comparisons. It is not a force that places zeros on that line; positivity and the open analytic obligations remain separate.")))
            ),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("symmetry-does-not-force-fixed-points"),
                H("Symmetry does not force fixed points"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_reversal_spec")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Invariance under the mirror permits two-cycles away from the fixed line. The checked coordinate reversal supplies pairing symmetry but no positivity argument, self-adjoint realization, or zero-location result.")))
            ),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("fixed-line-versus-orbit-collapse"),
                H("Fixed line versus orbit collapse"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_reversal_spec")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Real part one half is exactly the fixed locus of the mirror. Interpreting the Riemann hypothesis as collapse of every zero orbit to that locus is a classification of the open problem, not a conclusion of the fixed-point theorem.")))
            ),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("set-invariance-versus-pointwise-invariance"),
                H("Set invariance versus pointwise invariance"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_reversal_spec")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Mirror reversal can preserve a collection while exchanging its members. Even and odd combinations may change phase conventions, but they do not turn set-level symmetry into the pointwise fixedness needed for a critical-line conclusion.")))
            ),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("antilinear-reflection-produces-a-line"),
                H("Antilinear reflection produces a line"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_reversal_spec")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Combining conjugation with reflection gives an antiholomorphic involution whose fixed locus is the entire critical line rather than a single real point. The theorem establishes that stage; it does not establish that a zero lies on it.")))
            ),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("invariant-set-need-not-lie-in-fixed-locus"),
                H("An invariant set need not lie in the fixed locus"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "A mirror-stable pair may have neither member fixed. This elementary distinction is the precise gap between a symmetric zero inventory and the assertion that every zero has real part one half.")))
            ),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("scaled-midline-reading"),
                H("Scaled midline reading"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "A positive rescaling transports the half-density coordinate to a correspondingly scaled midline. This is an interpretive coordinate change: the checked declaration proves only the original mirror fixed locus and makes no claim about quasiperiodic zeta zeros, structural zeros, or denominator safety.")))
            ),
            DocumentBlock.Describe.Remark(
                DescribeId.Create("three-order-two-mechanisms-have-different-sources"),
                H("Three order-two mechanisms have different sources"),
                DescribeStatement.FromFormula(Equal(
                    Call("J", Id("s")),
                    Subtract(Num(1), Call("conj", Id("s"))))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The source distinguishes three independent appearances of two. Complex conjugation supplies the code-blind pair behind J(s) = 1-conj(s), squared modulus, and the coefficient inner product. The real Galois pair phi <-> psi supplies the code-specific integrality of the deficit. Additive multiplicity two, through the double-occupancy prohibition, supplies the denominator zeta(2*phi^2*s). Replacing Fibonacci by Tribonacci is reported to preserve the half-line while destroying integrality, so the conjugation and Galois mechanisms are independently replaceable. All three are order-two structures, but only the first two are compared through fixed sets: the critical midline is fixed by the complex involution, while the integers are fixed by the real conjugation. The source consequently reads ontological zeros on the midline and integral deficits as parallel fixed-point statements, and places their intersection where the quasiperiodic critical line meets the multiplicity pole, one deficit unit from its carry image.")))
            ))));
}
