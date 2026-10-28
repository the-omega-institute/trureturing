using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Variational;

internal sealed class JointReciprocalFunctionalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original scalar coordinate constructs a smooth normalized positive profile and its exact reciprocal cost.",
        H("Joint Reciprocal Functional"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-polynomial"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.polynomial"),
                H("The scalar denominator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real b and v, polynomial(b,v) is 2*b+3*(1-b)*v-6*v^2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-upperroot"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.upperRoot"),
                H("The positive denominator root"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real b, upperRoot(b) is [3(1-b)+sqrt(9(1-b) squared+48b)]/12."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-lowerroot"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.lowerRoot"),
                H("The negative root magnitude"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real b, lowerRoot(b) is [sqrt(9(1-b) squared+48b)-3(1-b)]/12."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-coordinate"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.coordinate"),
                H("The original integral coordinate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real b and v, coordinate(b,v) is the oriented Lebesgue integral from 0 to v of (2b+6s)/polynomial(b,s)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-mass"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.mass"),
                H("Competitor mass"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real function u on the real line, mass(u) is its oriented Lebesgue integral from 1 to 2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-primitive"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.primitive"),
                H("Cumulative competitor mass"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real function u and every real x, primitive(u,x) is the oriented Lebesgue integral of u from 1 to x."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-cost"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.cost"),
                H("The joint reciprocal cost"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real b and real function u, cost(b,u) is b times the integral of x/u(x) from 1 to 2 plus the integral of primitive(u,x)/(u(x)^2) over the same interval."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-admissible"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.Admissible"),
                H("The full bounded positive measurable class"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A real function u is admissible when it is almost everywhere measurable for Lebesgue measure restricted to [1,2], and there exist real c and B with c>0 and c<=u(x)<=B almost everywhere there. The bounds belong to u; no fixed common bounds or smoothness condition is imposed. This includes every Lebesgue measurable function in the stated class and all modifications on null sets."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-scalarroot"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.scalarRoot"),
                H("The selected scalar endpoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real b, scalarRoot(b) is the inverse integral coordinate at log(2). The inverse is chosen on (-epsilon,upperRoot(b)), where epsilon is the minimum of lowerRoot(b)/2 and b/6. For 0<b<=1 the coordinate is injective on this open interval and the chosen inverse is its actual inverse at every attained value."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-sharpconstant"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.sharpConstant"),
                H("The candidate sharp value"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real b, sharpConstant(b) is 8 times scalarRoot(b) squared times [b+2 scalarRoot(b)]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-optimizer"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.optimizer"),
                H("The explicit normalized profile"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real b and x, let v(x) be the same inverse integral coordinate applied to log(x), and let vb=scalarRoot(b). The profile optimizer(b,x) is x squared times polynomial(b,v(x)), divided by 8 vb polynomial(b,vb). Its existence uses no differential equation solution or normalization hypothesis."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-exists-unique-scalar-root"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.exists_unique_scalar_root"),
                H("Existence and uniqueness of the original scalar root"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real b with 0<b<=1, there is exactly one real v with 0<v<upperRoot(b) and coordinate(b,v)=log(2). The proof factors the denominator as 6[upperRoot(b)-v][v+lowerRoot(b)], identifies a logarithmic antiderivative, proves its divergence at the positive root, and uses strict monotonicity and the intermediate value theorem. The endpoint b=1 remains in scope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-constructed-profile"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.constructed_profile"),
                H("Smooth construction, normalization and exact cost"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real b with 0<b<=1, scalarRoot(b) is positive, is less than upperRoot(b), solves the original integral equation, and sharpConstant(b)>0. There is an open subset s of the real line containing [1,2] on which optimizer(b) is infinitely continuously differentiable, positive and strictly increasing. This profile is admissible, has mass one, and has cost exactly sharpConstant(b). To obtain smoothness, local inverse uniqueness identifies the chosen inverse with the smooth local inverses. Direct differentiation of x optimizer(b,x) v(x) gives optimizer(b,x), proving normalization. Direct differentiation of x squared times [b v(x)+2v(x) squared] divided by optimizer(b,x) gives the full cost density, and its endpoint difference is the exact value. For every admissible function u, the individual upper and positive lower bounds imply integrability of u and x/u. The cumulative mass is continuous on [1,2], and its boundedness together with the positive lower bound gives integrability of primitive(u,x)/(u(x)^2). These integral facts are used in the cost calculation. Global comparison with arbitrary measurable competitors is a separate mathematical obligation."))),
                DescribeRole.Theorem)))));
}
