using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class PositiveMomentRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive unital continuous moment maps satisfy Kadison's self-adjoint inequality. Equality at the square of the interval coordinate makes the entire map a star-algebra homomorphism, for arbitrary ordered complex C-star output.",
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
                    Paragraph(Text("This is classical Kadison and multiplicative-domain mathematics, supplied by finite variance and uniform approximation. It asserts no new solved conjecture. Scalar hinge optimality and a faithful positive functional must still imply the coordinate-square equality before this result can be used in the full-curvature divergence classification. Construction of the compressed GNS moment map and the intrinsic commutant-centralizer equivalence are separate obligations."))
                ), DescribeRole.Theorem)
        )));
}
