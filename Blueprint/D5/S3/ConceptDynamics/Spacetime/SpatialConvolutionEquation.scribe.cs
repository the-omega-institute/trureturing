using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class SpatialConvolutionEquationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spatial convolution equations have principal-multiple and uniqueness criteria.",
        H("Equations in the Finite Spatial Convolution Ring"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("spatial-convolution-equation-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Spacetime/SpatialConvolutionEquation.spatial_convolution_equation_criterion"),
                H("Solvability, uniqueness, and the zero factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The carrier consists of finitely supported integer functions on the three-dimensional "
                    + "integer lattice. Its convolution ring has no zero divisors by the unique-sums "
                    + "instance. The equation f * g = h therefore has a solution exactly when h belongs "
                    + "to the principal multiples of f, and a nonzero f has at most one solution. "
                    + "The principal multiples contain zero and are closed under subtraction and right "
                    + "multiplication. For f = 0, a solution exists exactly when h = 0, in which case "
                    + "every finitely supported g is a solution. Computing a solution is a separate question."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("spatial-convolution-coefficients"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Spacetime/SpatialConvolutionEquation.coefficient_multiplication"),
                H("The carrier and the convolution formula"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coefficient equivalence identifies the additive carrier with finitely supported "
                    + "integer functions. At r, multiplication sums f(p) * g(q) over pairs with p + q = r. "
                    + "Both sums range over finite supports. The multiplicative unit is the unit point "
                    + "mass at the origin."))),
                DescribeRole.Theorem))));
}
