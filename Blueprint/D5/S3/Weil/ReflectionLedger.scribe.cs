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
            new DocumentBlock.Describe(
                DescribeId.Create("mirror-fixed-points-lie-on-the-critical-line"),
                DescribeKind.Proposition,
                H("Mirror fixed points lie on the critical line"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Conjugate reflection sends a spectral parameter to one minus its conjugate. Every fixed point therefore has real part one half; no zero-location claim is made.")))),
            new DocumentBlock.Describe(
                DescribeId.Create("mirror-reverses-every-scaling-entry"),
                DescribeKind.Theorem,
                H("The mirror reverses every scaling entry"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_reversal_spec")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For the entry given by displacement from one half times ledger length, mirroring negates every coordinate. The same theorem identifies the full fixed locus.")))),
            new DocumentBlock.Describe(
                DescribeId.Create("symmetry-channel-is-not-location-force"),
                DescribeKind.Remark,
                H("A symmetry channel is not a location force"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Reflection identifies the critical fixed line and can serve as a channel for spectral comparisons. It is not a force that places zeros on that line; positivity and the open analytic obligations remain separate.")))),
            new DocumentBlock.Describe(
                DescribeId.Create("symmetry-does-not-force-fixed-points"),
                DescribeKind.Remark,
                H("Symmetry does not force fixed points"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_reversal_spec")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Invariance under the mirror permits two-cycles away from the fixed line. The checked coordinate reversal supplies pairing symmetry but no positivity argument, self-adjoint realization, or zero-location result.")))),
            new DocumentBlock.Describe(
                DescribeId.Create("fixed-line-versus-orbit-collapse"),
                DescribeKind.Remark,
                H("Fixed line versus orbit collapse"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_reversal_spec")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Real part one half is exactly the fixed locus of the mirror. Interpreting the Riemann hypothesis as collapse of every zero orbit to that locus is a classification of the open problem, not a conclusion of the fixed-point theorem.")))),
            new DocumentBlock.Describe(
                DescribeId.Create("set-invariance-versus-pointwise-invariance"),
                DescribeKind.Remark,
                H("Set invariance versus pointwise invariance"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_reversal_spec")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Mirror reversal can preserve a collection while exchanging its members. Even and odd combinations may change phase conventions, but they do not turn set-level symmetry into the pointwise fixedness needed for a critical-line conclusion.")))),
            new DocumentBlock.Describe(
                DescribeId.Create("antilinear-reflection-produces-a-line"),
                DescribeKind.Remark,
                H("Antilinear reflection produces a line"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_reversal_spec")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "Combining conjugation with reflection gives an antiholomorphic involution whose fixed locus is the entire critical line rather than a single real point. The theorem establishes that stage; it does not establish that a zero lies on it.")))),
            new DocumentBlock.Describe(
                DescribeId.Create("invariant-set-need-not-lie-in-fixed-locus"),
                DescribeKind.Remark,
                H("An invariant set need not lie in the fixed locus"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "A mirror-stable pair may have neither member fixed. This elementary distinction is the precise gap between a symmetric zero inventory and the assertion that every zero has real part one half.")))),
            new DocumentBlock.Describe(
                DescribeId.Create("scaled-midline-reading"),
                DescribeKind.Remark,
                H("Scaled midline reading"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Weil/ReflectionLedger.mirror_fixed_re_eq")),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "A positive rescaling transports the half-density coordinate to a correspondingly scaled midline. This is an interpretive coordinate change: the checked declaration proves only the original mirror fixed locus and makes no claim about quasiperiodic zeta zeros, structural zeros, or denominator safety.")))))));
}
