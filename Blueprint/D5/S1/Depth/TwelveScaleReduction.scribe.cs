using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth;

internal sealed class TwelveScaleReductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S1/Depth/TwelveScaleReduction",
                "Record partial arithmetic progress toward the unresolved source floor reduction."),
            H("Twelve-Scale Reduction"),
            Blocks(
                Paragraph(Text(
                    "This module records four partial arithmetic lemmas toward the unresolved source floor reduction. It does not identify the rational parameter with the largest partial quotient, does not supply the 2958-case or minimum-attainment certificates, does not identify the moat, envelope, or diffusion readings with the normalized finite-sample minimum, and does not reconstruct the historical sampling configuration or its leakage.")),
                new DocumentBlock.Describe(
                    DescribeId.Create("normalized-twelve-lower-bound"),
                    DescribeKind.Theorem,
                    H("Nonzero multiples of twelve obey the normalized floor"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Depth/TwelveScaleReduction.twelve_scale_le_normalized_magnitude")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "A nonzero integer divisible by twelve has absolute value at least twelve. Dividing by a positive rational parameter preserves the inequality; no orbit or maximum-partial-quotient interpretation is inferred."))),
                    LatexStatement.Create(@"$$\forall \psi\in\mathbb{Z},\ \forall A\in\mathbb{Q}_{>0},\ (12\mid\psi \land \psi\neq0) \Rightarrow \frac{12}{A}\leq\frac{|\psi|}{A}$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("normalized-twelve-equality"),
                    DescribeKind.Theorem,
                    H("The normalized floor equality detects absolute value twelve"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Depth/TwelveScaleReduction.normalized_magnitude_eq_twelve_scale_iff")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For a positive denominator, cancellation shows that the normalized magnitude equals twelve over that denominator exactly when the integer magnitude is twelve. The theorem does not produce such a sample member."))),
                    LatexStatement.Create(@"$$\forall \psi\in\mathbb{Z},\ \forall A\in\mathbb{Q}_{>0},\ \frac{|\psi|}{A}=\frac{12}{A}\Leftrightarrow|\psi|=12$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("finite-sample-twelve-minimum"),
                    DescribeKind.Theorem,
                    H("A witnessed finite sample has exact twelve-scale minimum"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Depth/TwelveScaleReduction.twelve_scale_is_normalized_sample_minimum")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "If every member of a finite integer sample is a nonzero multiple of twelve and one supplied member has magnitude twelve, then twelve over the positive parameter is a member and lower bound of the normalized sample. The enumeration and witness remain explicit premises."))),
                    LatexStatement.Create(@"$$\forall S\subset_{\mathrm{fin}}\mathbb{Z},\ \forall A\in\mathbb{Q}_{>0},\ ((\forall\psi\in S,\ 12\mid\psi\land\psi\neq0)\land(\exists\psi_0\in S,\ |\psi_0|=12))\Rightarrow \min\left\{\frac{|\psi|}{A}:\psi\in S\right\}=\frac{12}{A}$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("finite-sample-minimum-uniqueness"),
                    DescribeKind.Theorem,
                    H("A normalized finite-sample minimum is unique"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S1/Depth/TwelveScaleReduction.normalized_sample_minimum_unique")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Two normalized sample members that are each no greater than every member are equal by antisymmetry. This order-theoretic uniqueness does not identify any other statistical reading with the sample minimum."))),
                    LatexStatement.Create(@"$$\forall x,y\in N_A(S),\ ((\forall z\in N_A(S),\ x\leq z)\land(\forall z\in N_A(S),\ y\leq z))\Rightarrow x=y$$")))));
}
