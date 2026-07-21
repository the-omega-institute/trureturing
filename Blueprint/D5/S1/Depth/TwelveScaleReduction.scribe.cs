using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth;

internal sealed class TwelveScaleReductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Depth/TwelveScaleReduction",
                "Derive the exact twelve-scale floor from a rational sample's continued fraction."),
            H("Twelve-Scale Reduction"),
            Blocks(
                Paragraph(Text(
                    "This module extracts a rational sample's finite simple continued fraction with Mathlib's Euclidean algorithm, applies the Barkan-Hickerson-Knuth odd-length terminal convention, and derives the normalization denominator as the largest extracted partial quotient. It does not supply the 2958-case or minimum-attainment certificates, does not identify the moat, envelope, or diffusion readings with the normalized finite-sample minimum, and does not reconstruct the historical sampling configuration or its leakage.")),
                new DocumentBlock.Describe(
                    DescribeId.Create("canonical-continued-fraction-parity"),
                    DescribeKind.Theorem,
                    H("Canonical partial quotients are empty or odd in length"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Depth/TwelveScaleReduction.canonical_partial_quotients_empty_or_odd")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "An integral rational has no fractional partial quotients. Every nonempty extracted sequence has odd length after the unique terminal rewrite used by the Barkan-Hickerson-Knuth convention."))),
                    LatexStatement.Create(@"$$\forall q\in\mathbb{Q},\ C(q)=\varnothing\ \lor\ |C(q)|\equiv1\mod2$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("canonical-continued-fraction-reconstruction"),
                    DescribeKind.Theorem,
                    H("Canonical extraction reconstructs the rational sample"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Depth/TwelveScaleReduction.canonical_continued_fraction_value")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The extracted finite continued fraction evaluates exactly to its input rational. The proof connects the finite coefficient list back to Mathlib's GenContFract.of computation and proves that the odd-length terminal rewrite preserves the value."))),
                    LatexStatement.Create(@"$$\forall q\in\mathbb{Q},\ [\lfloor q\rfloor;C(q)]=q$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("normalized-twelve-lower-bound"),
                    DescribeKind.Theorem,
                    H("Nonzero multiples of twelve obey the normalized floor"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Depth/TwelveScaleReduction.twelve_scale_le_normalized_magnitude")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "A nonzero integer divisible by twelve has absolute value at least twelve. Dividing by the positive maximum partial quotient extracted from the rational sample preserves the inequality."))),
                    LatexStatement.Create(@"$$\forall q\in\mathbb{Q},\ \forall\psi\in\mathbb{Z},\ (A(q)>0\land12\mid\psi\land\psi\neq0)\Rightarrow\frac{12}{A(q)}\leq\frac{|\psi|}{A(q)}$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("normalized-twelve-equality"),
                    DescribeKind.Theorem,
                    H("The normalized floor equality detects absolute value twelve"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Depth/TwelveScaleReduction.normalized_magnitude_eq_twelve_scale_iff")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For a positive extracted maximum partial quotient, cancellation shows that the normalized magnitude equals twelve over that quotient exactly when the integer magnitude is twelve. The theorem does not produce such a sample member."))),
                    LatexStatement.Create(@"$$\forall q\in\mathbb{Q},\ \forall\psi\in\mathbb{Z},\ A(q)>0\Rightarrow\left(\frac{|\psi|}{A(q)}=\frac{12}{A(q)}\Leftrightarrow|\psi|=12\right)$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("finite-sample-twelve-minimum"),
                    DescribeKind.Theorem,
                    H("A witnessed finite sample has exact twelve-scale minimum"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Depth/TwelveScaleReduction.twelve_scale_is_normalized_sample_minimum")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "If every member of a finite integer sample is a nonzero multiple of twelve and one supplied member has magnitude twelve, then twelve over the rational sample's positive maximum partial quotient is a member and lower bound of the normalized sample. The enumeration and witness remain explicit premises."))),
                    LatexStatement.Create(@"$$\forall q\in\mathbb{Q},\ \forall S\subset_{\mathrm{fin}}\mathbb{Z},\ A(q)>0\land(\forall\psi\in S,\ 12\mid\psi\land\psi\neq0)\land(\exists\psi_0\in S,\ |\psi_0|=12)\Rightarrow\min\left\{\frac{|\psi|}{A(q)}:\psi\in S\right\}=\frac{12}{A(q)}$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("finite-sample-minimum-uniqueness"),
                    DescribeKind.Theorem,
                    H("A normalized finite-sample minimum is unique"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Depth/TwelveScaleReduction.normalized_sample_minimum_unique")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Two normalized sample members that are each no greater than every member are equal by antisymmetry. This order-theoretic uniqueness does not identify any other statistical reading with the sample minimum."))),
                    LatexStatement.Create(@"$$\forall x,y\in N_q(S),\ ((\forall z\in N_q(S),\ x\leq z)\land(\forall z\in N_q(S),\ y\leq z))\Rightarrow x=y$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("continued-fraction-twelve-floor"),
                    DescribeKind.Theorem,
                    H("The normalized sample floor uses the extracted maximum partial quotient"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Depth/TwelveScaleReduction.normalized_sample_floor_eq_twelve_over_maximum_partial_quotient")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Under the explicit divisibility, nonzero, attainment, and derived-maximum positivity premises, the actual Finset minimum of the normalized sample equals twelve divided by the largest partial quotient extracted from the rational sample. No independent scale parameter remains."))),
                    LatexStatement.Create(@"$$\forall q\in\mathbb{Q},\ \forall S\subset_{\mathrm{fin}}\mathbb{Z},\ A(q)>0\land(\forall\psi\in S,\ 12\mid\psi\land\psi\neq0)\land(\exists\psi_0\in S,\ |\psi_0|=12)\Rightarrow\min\left\{\frac{|\psi|}{A(q)}:\psi\in S\right\}=\frac{12}{A(q)},\qquad A(q)=\max C(q)$$")))));
}
