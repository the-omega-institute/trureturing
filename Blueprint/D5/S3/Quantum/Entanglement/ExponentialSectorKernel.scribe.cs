using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class ExponentialSectorKernelDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Quantum/Entanglement/ExponentialSectorKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An ordered exponential kernel has explicit nonnegative equilibrium weights and an attained simplex minimum, including coincident sites.",
        H("The Ordered Exponential Kernel"),
        Blocks(
            Paragraph(Text(
                "Let loss be a nondecreasing real sequence and take its first n+1 sites. "
                + "The kernel between sites i and j is exp(-abs(loss(i)-loss(j))/2). "
                + "Its adjacent coefficients are exp(-(loss(i+1)-loss(i))/2). "
                + "The quadratic energy is the sum over all ordered site pairs of "
                + "p(i) p(j) times their kernel entry. A simplex weight is nonnegative "
                + "at every site and has total mass one.")),
            Describe.Lean(
                DescribeId.Create("exponential-kernel"),
                DeclarationHandle.Create(DeclarationPrefix + "kernel"),
                H("Kernel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The kernel is the exponential of minus half the absolute separation of the real sites."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("adjacent-coefficient"),
                DeclarationHandle.Create(DeclarationPrefix + "edge"),
                H("Adjacent coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An adjacent coefficient lies in (0,1] for nondecreasing sites; equality to one allows repeated sites."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kernel-energy"),
                DeclarationHandle.Create(DeclarationPrefix + "energy"),
                H("Quadratic energy"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite quadratic form is defined for arbitrary signed real weights, as well as simplex weights."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("equilibrium-weights"),
                DeclarationHandle.Create(DeclarationPrefix + "equilibriumWeight"),
                H("Equilibrium weights"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The singleton weight is one. On adjoining a site with adjacent coefficient a, "
                    + "subtract a/(1+a) from the former last weight, retain the other old weights, "
                    + "and give the new endpoint weight 1/(1+a)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("normalizing-mass"),
                DeclarationHandle.Create(DeclarationPrefix + "normalizer"),
                H("Normalizing mass"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normalizer Z is one plus the sum of (1-a)/(1+a) over the n adjacent coefficients."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ordered-kernel-minimum"),
                DeclarationHandle.Create(DeclarationPrefix + "result"),
                H("Equilibrium, minimum and range bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The quadratic form is nonnegative on every signed weight vector. "
                        + "The equilibrium weights v are nonnegative, satisfy Kv=1, and sum to "
                        + "the positive normalizer Z. Thus p*=v/Z is a simplex weight, its "
                        + "energy is 1/Z, and every simplex weight has energy at least 1/Z. "
                        + "Strictly increasing sites give strictly positive equilibrium weights.")),
                    Paragraph(Text(
                        "Write T for the sum of tanh((loss(i+1)-loss(i))/4) over adjacent sites. "
                        + "Then Z=1+T. With R=loss(n)-loss(0), the quantity 2(1-1/Z) lies "
                        + "between 1-exp(-R/2) and 2R/(4+R). For every real epsilon<2, "
                        + "the inequality 2(1-1/Z)<=epsilon is equivalent to "
                        + "T<=epsilon/(2-epsilon).")),
                    Paragraph(Text(
                        "Adjoining the last site completes a square: the enlarged energy is "
                        + "the old energy at a corrected endpoint weight plus (1-a*a) times "
                        + "the square of the new weight. The equilibrium recursion proves "
                        + "the row equations. Subtracting p* from a competitor makes the "
                        + "mixed energy term vanish, leaving a nonnegative quadratic form. "
                        + "No inverse kernel is needed, so repeated sites are included. "
                        + "For n=0, Z=1 and the minimum energy is one.")),
                    Paragraph(Text(
                        "This statement concerns the finite kernel and its simplex energy. "
                        + "A channel distance requires an additional identification of the "
                        + "physical channel with this kernel."))),
                DescribeRole.Theorem))));
}
