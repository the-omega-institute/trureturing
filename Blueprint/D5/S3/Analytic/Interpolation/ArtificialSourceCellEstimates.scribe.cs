using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class ArtificialSourceCellEstimatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quartic cells control a perturbed Robin price coordinate on an adaptive grid.",
        H("Quartic cell estimates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("artificial-cell-kernel-hasDerivAt"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.kernel_hasDerivAt"),
                H("The Robin kernel derivative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real x greater than one, k(x)=(log x+1)/(x squared times (log x) squared) has derivative -(2(log x) squared+3 log x+2)/(x cubed times (log x) cubed). This follows from differentiating the scaled Robin weight at scale parameter one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("artificial-cell-cell-derivatives"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.cell_derivatives"),
                H("The two cell derivatives"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary real delta, a and x with width h(delta,a) positive, cellBump(delta,a,x)=-amplitude(delta,a) eta((x-a)/h) has derivative -(amplitude/h) etaOne((x-a)/h). That derivative expression itself has derivative -(amplitude/h squared) etaTwo((x-a)/h). Here etaOne(s)=2s(1-s)(1-2s) and etaTwo(s)=2-12s+12s squared. These identities hold for the polynomial continuation at every real x, including either endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("artificial-cell-cell-estimates"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.cell_estimates"),
                H("Uniform control on a cell"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let delta, a and x be arbitrary real numbers. Assume a>1, log a at least one, 0<h(delta,a)<=a, and a<=x<=a+h. Set c=1/128, epsilon(a)=log(a) exp(-(log a) to the power 1/4). Then the absolute value of cellSlope(delta,a,x)/k(x) is at most 4c epsilon(a) h. The absolute value of the derivative of y-cellSlope(delta,a,y)/k(y), evaluated at x, minus one is at most 44c epsilon(a). The estimates combine the quartic derivatives, the exact amplitude/width-squared cancellation and the Robin kernel bounds on [a,2a]."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("artificial-cell-epsilon-hasDerivAt"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.epsilon_hasDerivAt"),
                H("The increment budget derivative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each real a>1, epsilon has derivative exp(-(log a) to the power 1/4)/a times (1-(log a) to the power 1/4 divided by four). Thus epsilon decreases after its fourth-root logarithm reaches four."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("artificial-cell-epsilon-tendsto-zero"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.epsilon_tendsto_zero"),
                H("Decay of the increment budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The function epsilon(a)=log(a) exp(-(log a) to the power 1/4) tends to zero as a tends to positive infinity. Substitution u=(log a) to the power 1/4 reduces this to polynomial times exponential decay."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("artificial-cell-width-eventually-bounds"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.width_eventually_bounds"),
                H("Eventual admissible width bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every fixed positive real delta, eventually as a tends to positive infinity, log a is at least one and 1<=h(delta,a)<=a. The width is h(delta,a)=a to the power 3/4 times exp((log a) to the power 1/4 divided by two), divided by sqrt(log a), times (log a) to the power delta. Taking logarithms leaves a leading term 3 log(a)/4; the fourth-root and log-log terms are smaller than log(a)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("artificial-cell-epsilon-cell-comparison"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.epsilon_cell_comparison"),
                H("Comparing the budget across a cell"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real a>1 with log a at least one and real x in [a,2a], epsilon(a)<=2 epsilon(x). The logarithmic displacement is at most log 2. The fourth-root function has derivative at most one when its argument is at least one, so its displacement is also at most log 2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("artificial-cell-epsilon-width-identity"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/ArtificialSourceCellEstimates.epsilon_width_identity"),
                H("The remaining exponential saving"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary real delta and a>1, epsilon(a) h(delta,a)=a to the power 3/4 times exp(-(log a) to the power 1/4 divided by two) times (log a) to the power (delta+1/2)."))),
                DescribeRole.Theorem)))));
}
