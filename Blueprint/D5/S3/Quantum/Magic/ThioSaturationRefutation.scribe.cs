using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class ThioSaturationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/ThioSaturationRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/thio2026tight");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual complex noisy Strange qutrit has eight nonzero Gross-Wigner coordinates and saturates the fixed-purity natural-log entropy bound.",
        H("Saturation with a support that is not a dimension multiple"),
        Blocks(
            Node("grossDisplacement", "Source displacement operators",
                "For local dimension q the root is exp(2*pi*i/q). The shift sends |j> to |j+1>, the clock multiplies |j> by the jth root power, and the phase exponent is ab(q+1)/2 in ZMod q. Thus this is the source's phase-adjusted X^a Z^b, with residue labels including zero.", true),
            Node("grossOrigin", "The source origin operator",
                "Eq. (19) averages all q squared displacement operators with factor 1/q squared. This definition retains that sum and its normalization.", true),
            Node("grossLocal", "Local Gross operators",
                "Conjugating the origin operator by the source displacement gives S_ab. The dagger is the complex conjugate transpose. The dual operator is q*S_ab, as in Eq. (20).", true),
            Node("grossTensor", "Odd-local tensor frames",
                "The matrix entries are products of the local S entries for a family of local dimensions. IsGross specializes this construction to n factors of a common odd dimension q. The Hilbert basis is the dependent product of the residue bases and the coordinate labels are a pair of such products.", true),
            Node("columnProjector", "Basis projectors",
                "A column vector of an orthonormal basis gives its complex rank-one projector by the outer product with its conjugate."),
            Node("IsMUBKD", "The complete MUB-KD source class",
                "The two square basis matrices have orthonormal columns and every squared overlap is the inverse Hilbert dimension. The KD frame is the ordered product of the first and second projectors, Eq. (17), with an arbitrary bijection of coordinate labels. No convex-hull hypothesis from Lemma 2 is imposed.", true),
            Node("IsGross", "The complete odd-local Gross source class",
                "There is at least one local factor. The common local dimension q is positive and odd; the total dimension is q to the power n. The Hilbert basis and coordinate labels are bijectively identified with the tensor residue carriers. A unitary basis matrix permits every orthonormal computational basis. The frame equals the exact tensor product conjugated by this unitary, rather than an arbitrary operator frame.", true),
            Node("IsSourceFrame", "The union of source classes",
                "The allowed frame belongs either to the complete MUB-KD class or to the exact odd-local Gross tensor class.", true),
            Node("coordinate", "Complex coordinates",
                "Eq. (9) is Tr(rho*S dagger). Realness is asserted separately in the positivity hypotheses; taking the real part alone does not define membership in the allowed probability domain.", true),
            Node("coordinateSupport", "Coordinate support",
                "The finite set contains every label with nonzero complex coordinate. Its cardinality is D. This is not the rank of the density matrix.", true),
            Node("coordinateEntropy", "Entropy including zero entries",
                "The Shannon sum uses Real.negMulLog at every coordinate's real part. This uses the natural logarithm and its zero term is exactly zero. Positivity and realness are separate hypotheses in the assertion.", true),
            Node("claim", "Only dimension-multiple supports at saturation",
                "Appendix A A1.p8.1 asks: Whether these are the only possible D-values for which saturation occurs is not clear in general. The preceding values are D=delta*d, 1<=delta<=d. The assertion quantifies over every finite complex Hilbert basis of positive dimension, every finite coordinate carrier, both source classes, and every complex positive-semidefinite trace-one state. Every coordinate must be real and nonnegative, including zero. Source coordinates obey Eq. (10); no extra normalization premise is imposed on the assertion. Purity lies in the closed interval [1/d,1], so both endpoints are retained. Equality refers to H(Q)=-ln(Tr(rho squared))+ln(d). The conclusion requires an integer delta between one and d whose dimension multiple is the coordinate support.", true),
            Node("rho", "The known noisy Strange state",
                "The matrix is [[1/4,0,0],[0,3/8,-1/8],[0,-1/8,3/8]] on ZMod 3. With v=(0,1,-1) it equals I/4+v*v dagger/8=(3I-P)/8, where P|j>=|-j>. This is a known depolarized antisymmetric qutrit ingredient, credited to Gross and the noisy Strange literature in the source note. No new-state or priority claim is made."),
            Node("result", "The universal assertion is false",
                "Take q=d=3 and one tensor factor. The source operator sum equals P/3. The source coordinates of rho are zero at (0,0) and 1/8 at all other eight labels. The Gram decomposition establishes positivity on all complex vectors, and trace is one. The purity is 3/8, strictly between 1/3 and 1. The full entropy sum, including its zero term, is ln(8)=-ln(3/8)+ln(3). Coordinate support is eight, which is not three times an integer. This allowed instance contradicts the universally quantified assertion over both source classes. It saturates the purity-dependent middle bound, while its entropy exceeds ln(3). No classification of every fixed-purity minimizer or of every other attaining support follows.", false, DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("thio-2026-saturation-support-multiples"),
                    ResolutionKind.Refuted))
        ), []));

    private static DocumentBlock Node(string name, string title, string prose,
        bool literature = false, DescribeRole role = DescribeRole.Definition,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("thio-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), role == DescribeRole.Theorem
                ? StatementSource.FromAuthor(Disp(new Formula.Not(
                    new Formula.NamedConstant(FormulaIdentifier.Create("claim")))))
                : StatementSource.WithoutFormula(),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
