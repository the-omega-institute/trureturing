using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class LatticeBRSTCohomologyGhostGradingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer ghost grading of the full original BRST quotient",
        H("Integer ghost grading of the full original BRST quotient"), Blocks(
            Paragraph(Text("The carrier is literally State D, Q is totalCharge D H, Z is the existing cycles D H, B is the existing boundaries D H h26 hHG hGH, and C is the existing Cohomology D H h26 hHG hGH. Every quotient theorem keeps D : LatticeData, H : Matrix (Fin D.rank) (Fin D.rank) Complex, h26 : D.rank = 26, hHG : H * gramComplex D = 1, and hGH : gramComplex D * H = 1. No momentum or energy sector, relative antighost kernel, NullFrame, positivity, or finite-dimensionality assumption is added.")),
            Paragraph(Text("Write N for tensorNumber D. The existing all-state law NQ-QN=Q gives QNz=0 for a cycle z and N(Qx)=Q(Nx+x) for every original state x. Thus N descends once to the actual quotient. The full tensor basis has integral weights charge(S), the odd occupation count minus the even occupation count. Existing private all-state diagonality laws are reused through their original source module; the basis agrees definitionally with fullBasis. Integer weights are cast injectively into Complex, including negative weights.")),
            Node("project", "A full-state linear map Pi_g defined on the full tensor basis by retaining precisely basis labels of integer ghost number g. Applying the existing number/Q commutator to basis coefficients forces every nonzero Q coefficient to have output weight input weight plus one. Consequently Pi_g Q = Q Pi_(g-1). This gives closed projected cycles, without assuming a degree law.", DescribeRole.Definition),
            Node("stateDegrees", "The image of ghost charge on the finite support of fullBasis.repr x. This finite set depends on x; no uniform grade interval or finite-dimensional state space is asserted. The original state is the sum of its Pi_g components over this set.", DescribeRole.Definition),
            Node("cycleNumber", "The original number operator restricted to the actual full Q-kernel. Its boundary preservation uses the explicit original primitive Nx+x for the image of Qx.", DescribeRole.Definition),
            Node("cycleProject", "Pi_g restricted to actual cycles using the proved Q shift. No family of quotient projection operators is introduced.", DescribeRole.Definition),
            Node("number", "Nbar on the existing full critical quotient, constructed with Submodule.mapQ. Its value at the class of z is the class of Nz.", DescribeRole.Definition),
            Node("grade", "G(g) is the eigenspace of Nbar at the Complex cast of g, indexed by every integer.", DescribeRole.Definition),
            Node("finite_class_decomposition", "For each actual cycle z, the finite sum over stateDegrees z of classOf(cycleProject g z) equals classOf z. Each summand belongs to G(g) because N Pi_g z = g Pi_g z. The finite support and Q shift are proved on the original unrestricted carrier.", DescribeRole.Theorem),
            Node("grades_internal", "DirectSum.IsInternal G for the actual full quotient. Surjectivity follows from the finite class decomposition and surjectivity of classOf. Independence reuses Mathlib's eigenspaces_iSupIndep composed with the injective integer-to-Complex cast. This proves the canonical sum of the eigenspace inclusions is bijective.", DescribeRole.Theorem),
            Node("project_same_class", "For every integer g and every original cycle z whose class belongs to G(g), classOf(cycleProject g z) = classOf z. The proof separates the g component from the finite sum and uses independence against the supremum of all other integer grades. It includes absent support and the zero class. An arbitrary representative is not assumed homogeneous.", DescribeRole.Theorem),
            Node("homogeneous_cycle_lift", "For every g and c in G(g), there exists an actual cycle z with classOf z = c and tensorNumber z = (g : Complex) times z. The lift is obtained by projecting any original cycle representative, with equality of classes supplied by project_same_class.", DescribeRole.Theorem),
            Paragraph(Text("Attribution remains with the actual lattice and ghost suppliers, Bakalov-Kac, Scott Carnahan, Kalle Kytola, and Mathlib's basis, quotient and eigenspace machinery. This result establishes the algebraic integer grading and lift on the specified BRST complex. It makes no product degree, Delta degree, bracket degree, parity conversion, physical spacetime reconstruction, complete string theory, AdS/CFT or literature novelty claim.")))));

    private static DocumentBlock Node(string name, string text, DescribeRole role) => Describe.Lean(
        DescribeId.Create("original-brst-integer-ghost-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyGhostGrading." + name),
        H(name), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), role);
}
