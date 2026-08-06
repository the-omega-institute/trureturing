using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

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
                In(Seq(Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, Operatorname, Grp(F.Id("mirror")), Open, F.Id("s"), Close, Eq, F.Id("s"), Sp, Rightarrow, Sp, Re, Open, F.Id("s"), Close, Eq, Frac, Grp(D(1)), Grp(D(2)))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Conjugate reflection sends a spectral parameter to one minus its conjugate. Every fixed point therefore has real part one half; no zero-location claim is made.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("mirror-reverses-every-scaling-entry"),
                H("The mirror reverses every scaling entry"),
                LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_reversal_spec"),
                Disp(Seq(Forall, Sp, F.Id("A"), Esc, OpenBracket, Operatorname, Grp(F.Id("AddMonoid")), Open, F.Id("A"), Close, CloseBracket, Comma, Esc, Forall, Sp, Ell, Colon, F.Id("A"), To, Underscore, Grp(Plus), Mathbb, Grp(F.Id("R")), Comma, Esc, Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, Open, Forall, Sp, F.Id("a"), Comma, Operatorname, Grp(F.Id("scalingLedger")), Open, Ell, Comma, Operatorname, Grp(F.Id("mirror")), Open, F.Id("s"), Close, Comma, F.Id("a"), Close, Eq, Minus, Operatorname, Grp(F.Id("scalingLedger")), Open, Ell, Comma, F.Id("s"), Comma, F.Id("a"), Close, Close, Sp, Land, Sp, Open, F.Id("s"), Eq, Operatorname, Grp(F.Id("mirror")), Open, F.Id("s"), Close, Sp, Leftrightarrow, Sp, Re, Open, F.Id("s"), Close, Eq, Frac, Grp(D(1)), Grp(D(2)), Close)),
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
                    Call("J", DefinitionDsl.Id("s")),
                    Subtract(Num(1), Call("conj", DefinitionDsl.Id("s"))))),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "The source distinguishes three independent appearances of two. Complex conjugation supplies the code-blind pair behind J(s) = 1-conj(s), squared modulus, and the coefficient inner product. The real Galois pair phi <-> psi supplies the code-specific integrality of the deficit. Additive multiplicity two, through the double-occupancy prohibition, supplies the denominator zeta(2*phi^2*s). Replacing Fibonacci by Tribonacci is reported to preserve the half-line while destroying integrality, so the conjugation and Galois mechanisms are independently replaceable. All three are order-two structures, but only the first two are compared through fixed sets: the critical midline is fixed by the complex involution, while the integers are fixed by the real conjugation. The source consequently reads ontological zeros on the midline and integral deficits as parallel fixed-point statements, and places their intersection where the quasiperiodic critical line meets the multiplicity pole, one deficit unit from its carry image.")))
            )),
[
                    DocumentEdge.TruthAnchor.Create(
                        LeanDeclarationRef.Create("D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq")),
                    DocumentEdge.TruthAnchor.Create(
                        LeanDeclarationRef.Create("D5/S3/Weil/ReflectionLedger.mirror_reversal_spec")),
                    DocumentEdge.Dependency.Create(
                        GidRef.Create("D5/S3/Weil/LabeledZeta")),
                ]));
}
