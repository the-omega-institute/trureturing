using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Variational;

internal sealed class JointReciprocalFunctionalDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Estimation/trureturing2026pricegapconvexity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The joint reciprocal functional has an explicit smooth increasing minimizer and exact attained infima over the full bounded positive measurable class.",
        H("Joint Reciprocal Functional"),
        Blocks(
            Paragraph(Text("The source is trureturing research synthesis, Actual Robin price gaps, forced-core tail records and the selected-sign boundary, Library/Estimation/trureturing2026pricegapconvexity.md, pinned at https://github.com/the-omega-institute/trureturing/blob/a0bafa0673e5364a1c4f819f5b24311ee00b59ed/Library/Estimation/trureturing2026pricegapconvexity.md. That supplier-relative paper supplies the original analytic construction and JVM1--JVM2 target. This formalization proves only scalar-coordinate existence, the explicit normalized profile and the full measurable-class variational values. It does not verify the paper's source-window, arithmetic, strict-gain, Robin or RH claims. The scalar-coordinate support retains the original Lean constant names so the three public theorem statements remain identical.")),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-mass"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.mass"),
                H("Competitor mass"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real function u on the real line, mass(u) is its oriented Lebesgue integral from 1 to 2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-primitive"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.primitive"),
                H("Cumulative competitor mass"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real function u and every real x, primitive(u,x) is the oriented Lebesgue integral of u from 1 to x."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-cost"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.cost"),
                H("The joint reciprocal cost"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real b and real function u, cost(b,u) is b times the integral of x/u(x) from 1 to 2 plus the integral of primitive(u,x)/(u(x)^2) over the same interval."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-admissible"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.Admissible"),
                H("The full bounded positive measurable class"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A real function u is admissible when it is almost everywhere measurable for Lebesgue measure restricted to [1,2], and there exist real c and B with c>0 and c<=u(x)<=B almost everywhere there. The bounds belong to u; no fixed common bounds or smoothness condition is imposed. This includes every Lebesgue measurable function in the stated class and all modifications on null sets."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-scalarroot"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.scalarRoot"),
                H("The selected scalar endpoint"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real b, scalarRoot(b) is the inverse integral coordinate at log(2). The inverse is chosen on (-epsilon,upperRoot(b)), where epsilon is the minimum of lowerRoot(b)/2 and b/6. For 0<b<=1 the coordinate is injective on this open interval and the chosen inverse is its actual inverse at every attained value."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-sharpconstant"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.sharpConstant"),
                H("The sharp variational value"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real b, sharpConstant(b) is 8 times scalarRoot(b) squared times [b+2 scalarRoot(b)]."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-optimizer"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.optimizer"),
                H("The explicit normalized profile"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For real b and x, let v(x) be the same inverse integral coordinate applied to log(x), and let vb=scalarRoot(b). The profile optimizer(b,x) is x squared times polynomial(b,v(x)), divided by 8 vb polynomial(b,vb). Its existence uses no differential equation solution or normalization hypothesis."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-energy-density"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.energyDensity"),
                H("The original square-root reciprocal defect density"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For b and a real density u, let U be its cumulative mass, let X be the inverse of the constructed optimizer primitive, and put Y(x)=X(U(x)). The energyDensity is u(x)[sqrt(x)/u(x)-sqrt(Y(x))/optimizer(b,Y(x))]^2. The equivalent calibration formula uses (2/3)Q(U(x)) for the second reciprocal. This density is interval integrable for every normalized admissible u, as asserted by normalized_stability; global_stability applies it to u/mass(u)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-energy"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.energy"),
                H("The calibrated reciprocal square energy"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For b and a real density u, write U(x)=primitive(u,x), let W be the constructed optimizer primitive, and let X be its inverse on its positive open domain. Put Y(x)=X(U(x)). Energy is the interval integral on [1,2] of u(x)[sqrt(x)/u(x)-sqrt(Y(x))/optimizer(b,Y(x))]^2. Equivalently, the second term is (2/3)Q(U(x)), where Q(r)=3sqrt(X(r))/(2optimizer(b,X(r))). Integrability and nonnegativity are conclusions for admissible normalized competitors, rather than conventions for the integral."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-normalized-stability"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.normalized_stability"),
                H("Quantitative comparison and normalized a.e. uniqueness"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every real b with 0<b<=1 and every admissible measurable u with mass one, the energy density is interval integrable, E=energy(b,u)>=0, and C+bE<=cost(b,u), where C=sharpConstant(b). The coefficient is exactly b in the reciprocal square-root coordinates. Moreover, E=0 if and only if u=optimizer(b) almost everywhere for volume restricted to [1,2], and cost(b,u)=C if and only if the same a.e. identity holds. The endpoint b=1, individual density bounds, and null-set changes of representative are included.")),
                    Paragraph(Text("The measurable calibration theorem supplies the integrable remainder and the zero-energy transport equation Z(U(x))=x sqrt(x) on all of [1,2]. Since t sqrt(t) is strictly increasing on the positive axis, X(U(x))=x. Combining this with the a.e. reciprocal slope equation gives u(x)=optimizer(b,x) a.e. In the reverse direction, a.e. equality gives equality of every initial cumulative integral, hence zero energy and the exact optimizer cost. No regularity, monotonicity, or common bound on the competitor is added."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-global-stability"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.global_stability"),
                H("Global product remainder and all positive scalar optimizers"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every b with 0<b<=1 and every admissible measurable u, A=mass(u)>0. Set v(x)=u(x)/A. Its energy density is interval integrable, energy(b,v)>=0, and b energy(b,v)<=A cost(b,u)-C. Product equality A cost(b,u)=C holds if and only if u(x)=A optimizer(b,x) a.e. on [1,2]. Equivalently, it holds exactly when u is a positive scalar multiple of the optimizer a.e. The coefficient, domain and null-set convention are those of normalized_stability.")),
                    Paragraph(Text("Positive scaling preserves admissibility, multiplies mass and cumulative mass by the scale, and divides cost by it. Apply normalized stability to v. A positive scalar representative has mass equal to its scale, which proves both directions of the full equality characterization. The original sharp attained variational theorem uses the resulting nonnegative remainder bound. No positive arithmetic separation follows from step shape: positive increasing step approximations can approach the smooth analytic optimizer. The arithmetic signed strict upper, Robin above 5040, and the Riemann hypothesis are not established by these analytic results."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-exists-unique-scalar-root"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.exists_unique_scalar_root"),
                H("Existence and uniqueness of the original scalar root"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real b with 0<b<=1, there is exactly one real v with 0<v<upperRoot(b) and coordinate(b,v)=log(2). The proof factors the denominator as 6[upperRoot(b)-v][v+lowerRoot(b)], identifies a logarithmic antiderivative, proves its divergence at the positive root, and uses strict monotonicity and the intermediate value theorem. The endpoint b=1 remains in scope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-constructed-profile"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.constructed_profile"),
                H("Smooth construction, normalization and exact cost"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every real b with 0<b<=1, scalarRoot(b) is positive, is less than upperRoot(b), solves the original integral equation, and sharpConstant(b)>0. There is an open subset s of the real line containing [1,2] on which optimizer(b) is infinitely continuously differentiable, positive and strictly increasing. This profile is admissible, has mass one, and has cost exactly sharpConstant(b). To obtain smoothness, local inverse uniqueness identifies the chosen inverse with the smooth local inverses. Direct differentiation of x optimizer(b,x) v(x) gives optimizer(b,x), proving normalization. Direct differentiation of x squared times [b v(x)+2v(x) squared] divided by optimizer(b,x) gives the full cost density, and its endpoint difference is the exact value. For every admissible function u, the individual upper and positive lower bounds imply integrability of u and x/u. The cumulative mass is continuous on [1,2], and its boundedness together with the positive lower bound gives integrability of primitive(u,x)/(u(x)^2). These integral facts are used in the cost calculation. The sharp variational theorem compares this profile with every admissible measurable competitor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-reciprocal-sharp-joint-variational"),
                DeclarationHandle.Create("D5/S3/Analytic/Variational/JointReciprocalFunctional.sharp_joint_variational"),
                H("Sharp attained variational values on the full measurable class"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every real b with 0<b<=1, let C=sharpConstant(b)>0. Every admissible u satisfies mass(u)*cost(b,u)>=C. The set of all these product values has least element and infimum C. Every positive scalar multiple of the constructed optimizer belongs to the same class and attains this product value. For every real d>0, the set of values d/8 times [4 mass(u)+cost(b,u)] has least element and infimum d/2 times sqrt(C). The admissible function sqrt(C)/2 times optimizer(b) attains that scalar value. The individual upper and strictly positive lower bounds vary with u; the comparison imposes no smoothness, common bounds, or inverse-function assumption on u.")),
                    Paragraph(Text("For mass-one competitors, U is absolutely continuous with derivative u almost everywhere and range in [0,1]. Only the smooth profile primitive W is inverted. Its inverse X is the unique inverse of W on its open positive domain; local inverse uniqueness gives smoothness of this same X. Put Z(r)=X(r)*sqrt(X(r)), Q(r)=3 sqrt(X(r))/(2 optimizer(b,X(r))), M(r)=4b sqrt(X(r))/(3 optimizer(b,X(r)))+2r/(sqrt(X(r))*optimizer(b,X(r)) squared), and N(r)=-r/(X(r)*sqrt(X(r))*optimizer(b,X(r)) cubed). Direct differentiation of the constructed profile proves M'=N and Z'=Q.")),
                    Paragraph(Text("For nonnegative r and q and positive z, Z and Q, the functional density F(r,z,q)=4bq squared/9+8rq cubed/(27z) lies above its tangent plane at (Z,Q). The cubic tangent gap follows from two polynomial cases: if q<=Q/3 all remaining terms are nonnegative; otherwise four times the denominator-cleared gap is Q times (2Qz-3qZ+QZ) squared plus Z squared times (q-Q) squared times (4q-Q). The quadratic tangent gap is 4b(q-Q) squared/9.")),
                    Paragraph(Text("The comparison function V(x)=M(U(x)) times [x sqrt(x)-Z(U(x))/2] is absolutely continuous: the calibration coefficients are smooth on a neighborhood of the compact range of U and therefore Lipschitz there. The a.e. chain and product rules retain the square remainder: V'(x)+b u(x)[sqrt(x)/u(x)-(2/3)Q(U(x))] squared<=b x/u(x)+U(x)/u(x) squared. The endpoint difference equals the difference of M(W(x))*x sqrt(x)/2 at 2 and 1. Direct differentiation of this latter smooth function gives the profile cost density, so the fundamental theorem of calculus proves cost(b,u)>=C+b energy(b,u). The zero-energy transport and all a.e. equality cases are stated in normalized_stability and global_stability. All integrability facts follow from the original bounds. Positive scaling then removes normalization. Finally, mass(u)>0 and the square (2 mass(u)-sqrt(C)) squared combine with the product bound to give 4 mass(u)+cost(b,u)>=4 sqrt(C); the stated scaled profile attains equality. These are analytic variational values, with no claim of arithmetic attainability, a strict Robin inequality above 5040, or the Riemann hypothesis."))),
                DescribeRole.Theorem))));
}
