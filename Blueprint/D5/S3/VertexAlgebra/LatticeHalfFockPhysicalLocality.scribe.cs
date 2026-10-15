using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockPhysicalLocalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeHalfFockPhysicalLocality.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical coefficient locality of the actual normalized tensor fields", H("Two-Branch Locality"), Blocks(
            Paragraph(Text("For an arbitrary even integral lattice D, hu:IsUnit(det G), native charges a,b, "
                + "integers e,f and every unrestricted ActualTensor state, put g=B(a,b), N=abs(g), "
                + "q_a=B(a,a) and c_a=2^(-q_a). The delivered chargedCoefficient has the cover prefactor x^(-q_a). "
                + "With physical coordinates z=x^2 and w=y^2, multiplication by (z-w)^N uses "
                + "the doubled cover shifts e-2(N-j) and f-2j. Both branch factors are retained for either sign of g.")),
            Describe.Lean(DescribeId.Create("actual-physical-coefficient-locality"),
                DeclarationHandle.Create(Prefix + "charged_coefficient_physical_locality"), H("Locality on every actual tensor state"),
                StatementSource.FromAuthor(Disp(Call("ChargedPhysicalLocality", F.Id("D"), F.Id("hu"),
                    F.Id("a"), F.Id("b"), F.Id("e"), F.Id("f"), F.Id("state")))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "The finite sum over j=0,...,N of (-1)^j choose(N,j) times "
                    + "A_a[e-2(N-j)] A_b[f-2j] state minus the reverse composition vanishes. "
                    + "Both actual ordered products use the common native kernel and statewise finite supports. "
                    + "The two-branch PowerSeries identity produces a reciprocal polynomial; branch exchange identifies "
                    + "its two cleared kernels. The actual quotient ground representation supplies the central "
                    + "(-1)^g interchange sign, cancelling the reversed physical-difference sign. Pure-tensor readout "
                    + "and tensor induction prove the result without a locality premise or cutoffs."))), DescribeRole.Theorem),
            Paragraph(Text("Only the generic finite binomial identity is used from the ordinary difference library; "
                + "ordinary cover delta is not a twisted Jacobi certificate. Coordinate monodromy is a separate native result. "
                + "True all-state twisted Jacobi, physical iterates against ordinary Y, physical derivative covariance, "
                + "corrected descendant normal products, reconstruction and orbifold intertwiners remain separate open obligations. "
                + "Locality alone does not determine c_a. Classical FLM provenance, zero novelty claim; "
                + "no full Leech, Vnatural, Monster, fusion, no-ghost, string or AdS realization follows.")))));
}
