using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.ExponentialSum;

internal sealed class NeumannCenteredOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A balanced finite signed spectrum gives strict centered prefixes, strict stop-loss inequalities, and an exact optimal pulse gap.",
        H("Conditional centered order for Neumann port kernels"), Blocks(
            Paragraph(Text("For the kernel comparisons, fix T > 0 and assume the two kernels are continuous on [0,T] with plus-minus difference equal to the given balanced finite exponential sum on that interval. This gives strict centered prefixes. The midpoint maximum uses nonincreasing kernels on both sides, and the stop-loss comparison uses monotonicity of the minus kernel and strike bounds from the centered plus endpoints.")),
            Describe.Lean(DescribeId.Create("balanced-spectral-primitive"),
                DeclarationHandle.Create("D5/S3/Analytic/ExponentialSum/NeumannCenteredOrder.primitive_eq"),
                H("The primitive of the balanced spectral difference"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let the slow rates lambda_i lie strictly between zero and the fast rate Lambda. The nonnegative slow weights v_i have at least one positive entry. The difference d(t) is A exp(-Lambda t) minus the finite sum of v_i exp(-lambda_i t). Assume the inverse-rate balance A/Lambda = sum_i v_i/lambda_i. Integrating each exponential from zero to t and using this balance gives P(t) = sum_i (v_i/lambda_i) (exp(-lambda_i t) - exp(-Lambda t)), where P is the time integral of d."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("balanced-spectral-average"),
                DeclarationHandle.Create("D5/S3/Analytic/ExponentialSum/NeumannCenteredOrder.primitive_div_eq"),
                H("A positive spectral integral for the time average"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonzero t, integrate exp(-r t) with respect to the rate r from lambda_i to Lambda. The resulting endpoint difference divided by t gives P(t)/t as the sum of these rate integrals with weights v_i/lambda_i."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strict-spectral-average"),
                DeclarationHandle.Create("D5/S3/Analytic/ExponentialSum/NeumannCenteredOrder.strictAntiOn_primitive_div"),
                H("Strict decrease of the normalized primitive"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 0 < t < T, every rate r in each interval is positive, so exp(-r T) is strictly smaller than exp(-r t). Each interval has positive length. All weights v_i/lambda_i are nonnegative and one is positive, so summing the integral comparisons gives P(T)/T < P(t)/t."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strict-centered-prefix"),
                DeclarationHandle.Create("D5/S3/Analytic/ExponentialSum/NeumannCenteredOrder.centered_prefix_pos"),
                H("Strict order after subtracting the time averages"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take two kernels continuous on [0,T] whose difference there is d. Subtract from each its own average over [0,T]. The integral of the resulting difference up to t is P(t) - t P(T)/T. It is strictly positive for every 0 < t < T by strict decrease of the normalized primitive."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("optimal-midpoint-pulse-gap"),
                DeclarationHandle.Create("D5/S3/Analytic/ExponentialSum/NeumannCenteredOrder.midpoint_optimal_gap"),
                H("Exact advantage for optimal zero-net inputs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume both kernels are nonincreasing on [0,T]. An admissible input is almost everywhere measurable on this interval, has absolute value at most one almost everywhere, and has time integral zero. In lag coordinates the response is the integral of the kernel times the input. The common maximizer takes value +1 on the first half in lag and -1 on the second. To prove optimality, subtract the midpoint value from the kernel using the zero integral of the input. The resulting kernel is nonnegative on the first half and nonpositive on the second, so for each admissible input the pulse gives at least as large a recentered product almost everywhere. Splitting its response at T/2 gives the exact difference of maxima 2 P(T/2) - P(T), which is twice the strictly positive centered prefix at T/2.")),
                    Paragraph(Text("On the finite Neumann paths the port is the marked left endpoint in both cases. The plus path has the short edge at this port and the minus path has it at the other end. Each edge contributes half its length to the mass of each incident vertex in M. The stiffness K is the matrix of the energy given by the sum of squared edge differences divided by edge length. The input enters M u' + K u = e_0 p at the left endpoint and the output is the temperature u_0 at that same endpoint. From zero initial temperature the terminal output uses the kernel H(T-s), where H(t) is the (0,0) entry of exp(-t M^(-1/2) K M^(-1/2)) divided by the left endpoint mass. With the balanced spectrum and kernel hypotheses, the lag pulse gives the exact gain for inputs of unit amplitude bound and zero time integral. It prescribes -1 over the first half in physical input time and +1 over the second half. The switch value is immaterial to the integral."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strict-centered-stop-loss"),
                DeclarationHandle.Create("D5/S3/Analytic/ExponentialSum/NeumannCenteredOrder.centered_stopLoss_lt"),
                H("Strict comparison for strikes between the centered plus endpoints"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For each centered kernel integrate the positive part of its value minus the strike z on [0,T]. Assume the minus kernel is nonincreasing and z lies strictly between the values of the centered plus kernel at T and at 0. The integrated stop loss is strictly greater for the plus kernel. Dividing by T gives the same strict inequality for the average stop loss under uniform time.")),
                    Paragraph(Text("If z lies strictly between the centered minus kernel's endpoints, continuity gives a cutoff where that kernel equals z. Its monotonicity makes its stop loss exactly the integral up to the cutoff of the centered kernel minus z. The plus stop loss bounds the corresponding plus prefix from above, and strict centered prefix order compares the two prefixes. At or above the centered minus initial value, the minus stop loss vanishes and the centered plus kernel exceeds z near zero. At or below the centered minus final value, the minus stop loss equals -Tz by centering, and clipping the centered plus kernel near T strictly increases its integral above -Tz."))),
                DescribeRole.Theorem),
            Paragraph(Text("The ordinary proof A boundary cell defect on reflected lumped Neumann paths supplies the finite spectral hypotheses in Sections 4 and 6. Transfer through the short cell compares the two port weights below the unit-grid band edge 4, and a min-max argument counts the eigenvalues above it. The stationary weights cancel, all positive eigenvalues below 4 have negative plus-minus weights, 4 is absent, and the unique eigenvalue above 4 has positive plus-minus weight. After stationary cancellation the zero-shift limit of the finite resolvent difference gives zero total time integral, hence the inverse-rate balance.")),
            Paragraph(Text("The parent uses the sign pattern for the crossings of the raw kernel difference and its negative derivative. It combines the kernel crossing and the zero total integral to order the uncentered L^2 control Gramians. Section 1 of Strict centered order of the physical Neumann port kernels uses the same spectral data in its rate-integral formula. The finite Lean comparison covers that formula, the strict prefixes and stop-loss comparison between the centered plus endpoints, and the exact q = 1 dual gap for unit L^infinity inputs with zero integral.")),
            Paragraph(Text("A concrete finite Lean instance still needs the lumped mass and stiffness kernels, their continuity and monotonicity, a proof of the signed weights and balance for those kernels, and the terminal response identity. For the half-line, the parent proof derives a negative signed density on (0,4) and a single positive atom above 4 from the two Jacobi resolvents. The signed density is O(lambda^(3/2)) near zero, and the zero-shift resolvent limit gives inverse-moment balance. The half-line application needs those spectral-measure identities in Lean and an extension of the finite rate sum to a positive measure with finite inverse moment.")),
            Paragraph(Text("Further results of the ordinary centered-order proof remain to be formalized, including strict endpoint nesting and the unique centered crossing, strict convex order of the uniform-time laws and martingale coupling, best-constant and effort formulas across all exponents, Gaussian and bounded-noise testing, and the physical scaling and finite-to-half-line convergence.")))));
}
