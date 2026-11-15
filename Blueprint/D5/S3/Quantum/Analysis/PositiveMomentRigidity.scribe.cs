using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class PositiveMomentRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive unital continuous moment maps satisfy Kadison's self-adjoint inequality. Scalar hinge bounds tested by a faithful positive functional force equality at the square of the interval coordinate and make the entire map a star-algebra homomorphism, for arbitrary ordered complex C-star output.",
        H("Positive continuous moment rigidity"),
        Blocks(
            Describe.Lean(DescribeId.Create("complexify"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/PositiveMomentRigidity.complexify"),
                H("Real continuous functions inside complex continuous functions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("complexify is Mathlib's pointwise real-to-complex algebra homomorphism on the closed unit interval. Its continuous linear realization preserves uniform limits, and nonnegative real functions become positive complex continuous functions."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("interval-coordinate"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/PositiveMomentRigidity.coordinate"),
                H("The interval coordinate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("coordinate sends x in the closed unit interval to the complex number ofReal(x.val). It is the same actual function as NormalMomentFamily.posterior; both endpoints are included."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("kadison-real"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/PositiveMomentRigidity.kadison_real"),
                H("Kadison inequality from finite positive variance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/kadison1952schwarz")),
                Blocks(
                    Paragraph(Text("A is any complex C-star algebra with a compatible partial order and StarOrderedRing structure. Z is an actual positive complex-linear map from the complex continuous functions on the closed unit interval to A, with Z(1)=1. For every real continuous g, Z(complexify(g)) squared is at most Z(complexify(g*g)). Automatic continuity is inherited from Mathlib's PositiveLinearMap instance; boundedness, complete positivity and a dilation are not additional assumptions.")),
                    Paragraph(Text("For finitely many positive effects E_i summing to 1 and real numbers a_i, let S=sum a_i E_i. Expanding sum (a_i 1-S) E_i (a_i 1-S) gives sum a_i^2 E_i-S*S. Each sandwich is positive because S is self-adjoint. The expansion preserves both orders of multiplication and requires no commutation of E_i with S.")),
                    Paragraph(Text("The effects Z(complexify(bernstein(n,k))) are positive and sum to 1 by bernstein_nonneg and bernstein.probability. The finite inequality applies to samples g(k/n). Mathlib's bernsteinApproximation_uniform is applied separately to g and g*g. Continuity of Z and multiplication, and closedness of the positive cone, pass to the limit. The two Bernstein approximants are never identified with one another's square."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("one-coordinate-rigidity"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/PositiveMomentRigidity.exists_starAlgHom_of_square"),
                H("One-coordinate equality determines the entire map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/kadison1952schwarz")),
                Blocks(
                    Paragraph(Text("Assume only Z(coordinate*coordinate)=Z(coordinate)*Z(coordinate), in addition to positivity, complex linearity and Z(1)=1. The conclusion constructs an actual unital complex star-algebra homomorphism Phi on ALL complex continuous functions, with Phi(f)=Z(f) for every f and the exact generator value Phi(coordinate)=Z(coordinate). It applies in particular to the bounded operators on any complete complex inner product space, including the zero space and nonseparable spaces.")),
                    Paragraph(Text("A closed-cone argument shows that t B+t^2 D positive for every real t forces B=0: divide the positive and negative parameter inequalities by a positive scalar, let that scalar decrease to zero, and use antisymmetry. Applying this to Kadison for coordinate+t*h gives the Jordan identity 2 Z(coordinate*h)=Z(coordinate)Z(h)+Z(h)Z(coordinate) for real h. Induction determines every coordinate power, and polynomial induction identifies the images of every real polynomial.")),
                    Paragraph(Text("Multiplicativity for pairs of polynomials follows from polynomial evaluation. Two closed-set extensions using Mathlib's Bernstein-based polynomial density prove multiplicativity for every pair of real continuous functions. Real and imaginary decomposition proves genuine multiplicativity for complex functions. Positive and negative real decompositions show that images of real functions are self-adjoint, and the complex decomposition proves preservation of star. These are the actual fields of the constructed homomorphism.")),
                    Paragraph(Text("This is classical Kadison and multiplicative-domain mathematics, supplied by finite variance and uniform approximation. It asserts no new solved conjecture. The scalar-hinge theorem below supplies coordinate-square equality from the original scalar bounds. Construction of the compressed GNS moment map, faithfulness of its actual functional, its scalar hinge bounds from full-curvature equality, and the intrinsic commutant-centralizer equivalence remain separate obligations."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("scalar-hinge"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/PositiveMomentRigidity.hinge"),
                H("The actual scalar hinge"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real s, hinge(s) is the complex continuous function x maps to ofReal(max(x.val-s,0)) on the entire closed unit interval."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("scalar-hinge-rigidity"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/PositiveMomentRigidity.exists_starAlgHom_of_scalar_hinges"),
                H("Faithful scalar hinge bounds force full moment rigidity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/kadison1952schwarz")),
                Blocks(
                    Paragraph(Text("Let Z be a positive complex-linear map from all complex continuous functions on the closed unit interval into an arbitrary ordered complex C-star algebra A, with Z(1)=1. Let phi be a positive complex-linear functional faithful on positive elements: b positive and phi(b)=0 imply b=0. Assume, for every real 0<s<1, Re(phi(Z(hinge(s)))) is at most Re(phi((Z(coordinate)-algebraMap(s)) positive part)). The positive part here is the actual continuous functional calculus positive part in A. Positivity makes Z and phi continuous automatically. No square comparison, multiplicativity, complete positivity, normality, nonzero carrier or separability is assumed.")),
                    Paragraph(Text("The theorem proves Z(coordinate*coordinate)=Z(coordinate)*Z(coordinate), and constructs a unital complex star-algebra homomorphism Phi with Phi(f)=Z(f) for EVERY complex continuous function f and Phi(coordinate)=Z(coordinate). This includes the zero output algebra and bounded operators on arbitrary complete complex Hilbert spaces.")),
                    Paragraph(Text("The real hinge curve is continuous in the uniform norm. Splitting its scalar integral at x gives integral from 0 to 1 of max(x-s,0) ds=x*x/2, including x=0 and x=1. Continuous point evaluation commutes with the Bochner integral, proving the same identity in the real continuous-function space. Integrating the assumed scalar inequalities uses only the open interval, so the hypothesis requires neither endpoint bound.")),
                    Paragraph(Text("Positivity and unitality put the spectrum of Z(coordinate) inside [0,1]. Mathlib cfcHomSuperset gives a continuous real star-algebra homomorphism Q on this entire interval, with Q(coordinate)=Z(coordinate). The CFC composition and subtraction laws identify Q(realHinge(s)) with the actual positive part of Z(coordinate)-algebraMap(s). The two bounded real functionals Re(phi(Z(complexify(f)))) and Re(phi(Q(f))) commute with integration. Their hinge comparison therefore implies Re(phi(Z(coordinate*coordinate))) at most Re(phi(Z(coordinate)*Z(coordinate))).")),
                    Paragraph(Text("The compiled kadison_real makes B=Z(coordinate*coordinate)-Z(coordinate)*Z(coordinate) positive. Positivity of phi and the scalar comparison give zero real part; the image of a positive element also has zero imaginary part. Faithfulness gives B=0. The proof directly consumes exists_starAlgHom_of_square to obtain equality on the full complex continuous-function space. Every auxiliary lemma is on this conclusion path.")),
                    Paragraph(Text("This supplier does not complete the original arbitrary-von-Neumann full-curvature divergence classification. The actual GNS/commutant functional and its faithfulness, the scalar hinge inequalities from original full-curvature equality, and the remaining intrinsic commutant-centralizer and divergence bridges must still be discharged. No GNS normality premise is introduced here."))
                ), DescribeRole.Theorem)
        )));
}
