using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.StolarskyMean;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/StolarskyMean/Result";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive profile curvature implies conditional negativity and the class A property for Stolarsky mean matrices.",
        H("Integrating positive mixed curvature"), Blocks(
            Describe.Lean(DescribeId.Create("stolarsky-result-log-kernel"),
                DeclarationHandle.Create(Module + ".logKernel"),
                H("Exponential homogeneous reconstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "A real profile g determines the kernel exp((x+y)/2) g((y-x)/2). For the Stolarsky profile this is the mean of exp(x) and exp(y). These coordinates keep all scalar derivatives on the whole real line."))),
                DescribeRole.Definition),
            Theorem("conditionallyNegative_of_mixed_feature", "Hilbert features integrate to negative type",
                "Let K have a first partial derivative Kx and let v be a continuous path in a real Hilbert space. If the second partial derivative in the other coordinate is minus the inner product of the two feature vectors, then every finite matrix of K is conditionally negative. Integrating v from zero defines V. Two applications of the zero derivative criterion give K(x,y)-K(x,0)-K(0,y)+K(0,0)=-inner(V(x),V(y)). For coefficients summing to zero, the quadratic form is minus the squared norm of the weighted sum of V."),
            Theorem("conditionallyNegative_logKernel", "Positive profile curvature gives conditional negativity",
                "For a twice continuously differentiable real profile g, assume that g''-g is positive definite in the finite translation matrix sense. The corresponding scalar kernel generates a reproducing kernel Hilbert space by the Mathlib construction. Joint continuity gives a continuous feature path. Multiplication by exp(x/2)/2 and dilation by one half produce a feature for the negative mixed derivative of the exponential homogeneous reconstruction. The Hilbert integration theorem then proves conditional negativity on every finite configuration."),
            Theorem("conditionallyNegative_stolarsky", "Conditional negativity of Stolarsky mean matrices",
                "For every real parameter at least two and every finite positive family, the Stolarsky mean matrix is conditionally negative. KernelFactor supplies global smoothness of its exponential profile and positive definiteness of its second derivative defect. The exponential reconstruction theorem applies at the logarithms of the positive inputs. Repeated inputs and the empty family are allowed."),
            Theorem("inClassA_stolarsky", "Exactly one positive eigenvalue",
                "For every real parameter at least two and every nonempty finite positive family, the Stolarsky mean matrix has positive entries and exactly one strictly positive eigenvalue, counted with multiplicity. Symmetry and positivity come from the scalar mean. Conditional negativity limits the positive spectral subspace to dimension at most one, while a positive diagonal entry supplies a positive direction."),
            Describe.Lean(DescribeId.Create("stolarsky-class-a-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The Stolarsky matrix conjecture"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Fourier/bhatia2016mean")),
                Blocks(Paragraph(Text("Every real parameter at least two gives a class A Stolarsky matrix for every nonempty finite positive family. Every parameter from zero inclusive to two exclusive admits a positive three-point family whose mean matrix has at least two positive eigenvalues. The first conclusion follows from positive profile curvature, Hilbert feature integration and the spectral bound. The second uses the ThreePoint theorem. The definitions and the conjecture are those of Bhatia and Jain; the proofs are formal derivations in this repository."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bhatia-jain-2016-stolarsky-mean-matrices-class-a"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Theorem(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("stolarsky-result-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
