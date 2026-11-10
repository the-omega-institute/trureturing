using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveKuperbergDefsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveKuperbergDefs.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real smooth weights and Kuperberg exponential-sum moments",
        H("Real smooth weights and Kuperberg exponential-sum moments"),
        Blocks(
            Paragraph(Text(
                "The source is Kuperberg, Sums of singular series along arithmetic progressions and with smooth weights, "
                + "arXiv:2301.06095v1, equations (11)–(13) and Theorem 1.3. "
                + "The paper allows complex weights and every positive moment order. "
                + "Here the weights are real and only orders three and four are retained. "
                + "The paper's functions on the nonnegative half-line are represented by smooth functions on the whole real line, "
                + "with compact closed support inside the positive half-line; this is the smooth zero-extension representation. "
                + "The two bounds are explicit hypotheses, with a constant for each fixed weight family preceding every modulus and scale quantifier.")),
            Describe.Lean(
                DescribeId.Create("smooth-positive-weight"),
                DeclarationHandle.Create(Prefix + "SmoothPositiveWeight"),
                H("Smooth weight supported in the positive half-line"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A real function is infinitely differentiable on the real line and has compact closed support contained in (0,infinity). "
                    + "In particular its value at zero and all its negative samples vanish."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("fourier-at"),
                DeclarationHandle.Create(Prefix + "fourierAt"),
                H("Fourier transform convention"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Fourier transform at xi is the Lebesgue integral of f(x) exp(-2 pi i x xi) over the real line. "
                    + "The real weight is included in the complex numbers before multiplication. "
                    + "The displayed transform preceding equation (10) in v1 reads -integral from +infinity to +infinity. "
                    + "Here it is corrected to the integral from -infinity to +infinity, without an exterior minus sign, retaining the negative exponential phase used in the Poisson identity following equation (12)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quadratic-fourier-decay"),
                DeclarationHandle.Create(Prefix + "QuadraticFourierDecay"),
                H("Quadratic Fourier decay"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "There is a nonnegative constant C such that the Fourier transform has norm at most C/xi squared whenever the absolute value of xi is at least one. "
                    + "This specifies the paper's two-sided quadratic decay using a fixed threshold. "
                    + "For smooth compactly supported weights, boundedness of the transform on compact frequency intervals allows any asymptotic threshold to be replaced by one. "
                    + "The decay premise remains explicit."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("unit-character"),
                DeclarationHandle.Create(Prefix + "unitCharacter"),
                H("Positive additive phase"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The additive phase at t is exp(2 pi i t), with the positive sign used in the paper's exponential sums."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-exponential-sum"),
                DeclarationHandle.Create(Prefix + "weightedExponentialSum"),
                H("Weighted exponential sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At natural scale h, the exponential sum is the sum over all integers d of f(d/h) exp(2 pi i d t), as in equation (12). "
                    + "Finite-support summation represents the paper's sum: compact support gives only finitely many nonzero samples when h is positive. "
                    + "Only h at least three is used in the moment hypotheses."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kuperberg-raw-moment"),
                DeclarationHandle.Create(Prefix + "kuperbergRawMoment"),
                H("Exponential-sum moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a family indexed by Fin k, sum over divisor tuples q_i of Q with q_i different from one. "
                    + "Multiply the coefficients mu(q_i)/phi(q_i) by the sum over reduced residue tuples r_i of the product of their weighted exponential sums at r_i/q_i. "
                    + "A tuple contributes only when the sum of its rational frequencies is an integer. "
                    + "Positive Q ensures that its divisors are positive, so removing one implements the paper's condition q_i greater than one. "
                    + "The rational membership test expresses the exact integer constraint in equation (11). "
                    + "No uniform-average factor or additional sieve-density factor is inserted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kuperberg-raw-wick-defect"),
                DeclarationHandle.Create(Prefix + "kuperbergRawWickDefect"),
                H("Fourth exponential-sum defect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Subtract from the fourth exponential-sum moment the three products of second moments belonging to the pairings 01|23, 02|13 and 03|12. "
                    + "These are bilinear pairings, without complex conjugation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kuperberg-raw"),
                DeclarationHandle.Create(Prefix + "KuperbergRaw"),
                H("Kuperberg's third and fourth exponential-sum bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each fixed family of three admissible real weights, assume a constant C such that the third moment has complex norm at most C h^(3/2-1/21) P^(19/2). "
                    + "For each fixed family of four weights, assume a constant C such that the fourth pairing defect has complex norm at most C h^(2-1/28) P^18. "
                    + "Here P=Q/phi(Q), Q ranges over all positive squarefree moduli including one, and h ranges over natural numbers at least three. "
                    + "The odd pairing sum is empty; the even pairing sum is written explicitly. "
                    + "The complex norm inequality makes the paper's error notation explicit. "
                    + "Constants may depend on the fixed weights, and need not be uniform over varying weights or interval endpoints."))),
                DescribeRole.Definition))));
}
