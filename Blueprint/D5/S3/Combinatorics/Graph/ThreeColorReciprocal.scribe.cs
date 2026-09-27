using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ThreeColorReciprocalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ThreeColorReciprocal.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A proper three-coloring whose mixed vertices have degree two forces a reciprocal potential of at least 23/12, without restrictions on the other degrees or on class sizes.",
        H("Three-color reciprocal inequality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("certificate-nonnegativecoefficients"),
                DeclarationHandle.Create(Prefix + "nonnegativeCoefficients"),
                H("Coefficient sign test"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sign test accepts a normalized integer polynomial exactly when every stored coefficient is nonnegative. Such a polynomial is nonnegative at every tuple of nonnegative rational arguments."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("certificate-choice"),
                DeclarationHandle.Create(Prefix + "Choice"),
                H("Ordinary-pair regions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A region is either a thin pair with a specified finite population and an empty opposite side, or a pair with both sides positive and a specified orientation. Positive pairs are parameterized by a smaller side minus one and a nonnegative difference."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("certificate-choices"),
                DeclarationHandle.Create(Prefix + "choices"),
                H("Feasible region choices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For sorted mixed populations a at most b, equal populations permit the empty ordinary pair. Unequal populations permit a thin side of size between one and b-a, on the side with smaller mixed population. Both positive orientations are also included."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("certificate-sizes"),
                DeclarationHandle.Create(Prefix + "sizes"),
                H("Symbolic side sizes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each positive pair uses two nonnegative variables: its smaller size is one plus the first variable, and its larger size adds the second variable. A thin pair has its specified constant size and a zero opposite side. Three pairs use six variables."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("certificate-isfull"),
                DeclarationHandle.Create(Prefix + "isFull"),
                H("Positive-pair indicator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This indicator distinguishes regions with both ordinary sides positive from thin regions. The case where all three pairs are positive is handled by the attachment-charge estimate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("certificate-charge"),
                DeclarationHandle.Create(Prefix + "charge"),
                H("Pair fractions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("These rational-expression numerators and denominators encode twelve times a pair contribution. The quadratic branch uses six times each ordinary size squared and its degree-sum denominator; a thin side uses its exact mixed-population difference. The linear branch records the corresponding size-over-degree expression."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("certificate-numerator"),
                DeclarationHandle.Create(Prefix + "numerator"),
                H("Cleared polynomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The polynomial multiplies twelve times the lower expression minus twenty-three by the product of its positive denominators. Its terms include the three class reciprocals, the mixed contribution, and the three ordinary-pair contributions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("certificate-checkmixed"),
                DeclarationHandle.Create(Prefix + "checkMixed"),
                H("Fixed mixed-population check"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a fixed sorted triple of mixed populations, the check ranges over every permitted ordinary-pair region and tests nonnegativity of the cleared polynomial coefficients. The case of three positive pairs is reserved for the separate analytic estimate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("certificate-checktotal"),
                DeclarationHandle.Create(Prefix + "checkTotal"),
                H("Fixed total mixed-population check"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This check ranges over every sorted triple of mixed populations having the specified total. Totals zero through five contain 754 regions with at most two positive ordinary pairs; the six side parameters remain unrestricted nonnegative integers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("certificate-side"),
                DeclarationHandle.Create(Prefix + "side"),
                H("Numerical region sizes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This evaluates a region at its two nonnegative integer parameters, retaining the specified orientation. Every feasible ordinary pair has one of these representations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("certificate-context"),
                DeclarationHandle.Create(Prefix + "context"),
                H("Six-variable evaluation context"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The evaluation context supplies the six nonnegative parameters of the three ordinary pairs to their symbolic polynomials."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("certificate-assembled"),
                DeclarationHandle.Create(Prefix + "assembled"),
                H("Common-denominator construction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Given a constant and a list of rational-expression numerators and denominators, the construction forms their common-denominator numerator. Each fraction contributes its numerator times the product of all other denominators. Positivity of every denominator allows the sign of the rational sum to be read from this polynomial."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("population-bound"),
                DeclarationHandle.Create(Prefix + "population_bound"),
                H("Unrestricted numerical population inequality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary natural populations with zero diagonal and the empty-side feasibility inequalities, the maximum of the attachment-charge and Cauchy expressions is at least 23/12. If the mixed total M is at least six and N is the ordinary total, Cauchy gives the lower bound M/6+9/(N+M+3)+N squared divided by N squared plus 2N plus 4M; a polynomial with nonnegative terms proves this is sufficient. For M at most five with all three ordinary pairs positive, the attachment estimate gives at least 9/4-M/36. In all remaining cases, sorting the mixed populations and representing every feasible ordinary pair reduces the inequality to the 754 cleared polynomials, each with nonnegative coefficients. There is no bound on the ordinary sizes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reciprocal-bound"),
                DeclarationHandle.Create(Prefix + "reciprocal_bound"),
                H("Three-color reciprocal bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite vertex set, symmetric adjacency relation, and specified proper coloring into three possibly empty classes, if every mixed vertex has degree exactly two then the potential is at least 23/12. Degrees and class sizes are unrestricted. Delete the isolated vertices; the remaining neighborhoods do not change. Removing r isolates from a class with a remaining vertices cannot increase the potential, since 1/(a+1) is at most 1/(a+r+1)+r/2. Apply the actual population reduction and the numerical inequality to the remaining graph."))),
                DescribeRole.Theorem)),
        []));
}
