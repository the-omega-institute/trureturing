using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class RootlessGriessProductsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/RootlessGriessProducts.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual quadratic and norm-four charge-orbit products in the production lattice vertex algebra.",
        H("Actual Rootless Lattice Quadratic and Charge Products"),
        Blocks(
            Definition("quadratic-state", "Q", "Neutral quadratic state", "For any even LatticeData D and colours i,j, Q is the zero-charge polynomial X(i,0) X(j,0) in the actual finite-charge carrier. Repeated colours are allowed."),
            Definition("ground-state", "ground", "Charged ground state", "The state at an integral charge a is the literal finitely supported vector with polynomial one in charge sector a."),
            Definition("plus-orbit", "E", "Plus charge orbit", "E(a) is ground(a) plus ground(-a), with no representative choice. Equal and opposite charges describe the same orbit state."),
            Definition("gram-charge", "Gi", "Gram-charge contraction", "Gi(i,a) is the complex cast of the sum over colours j of G(i,j) times the integral coordinate a(j)."),
            Definition("charge-square", "Qcharge", "Actual charge-oscillator square", "Qcharge(a) is the zero-charge state whose polynomial is the square of the existing mode-one chargePolynomial(a)."),
            Theorem("quadratic-quadratic-one", "quadratic_quadratic_one", "Four quadratic contractions at mode one", "For all colours i,j,k,l of every even LatticeData D, the actual normalized product mu(Q(i,j),1,Q(k,l)) is G(i,k) Q(j,l) plus G(i,l) Q(j,k) plus G(j,k) Q(i,l) plus G(j,l) Q(i,k), with matrix entries cast to complex scalars. This includes coincident colours and requires no inverse Gram matrix or positive-rank hypothesis."),
            Theorem("quadratic-quadratic-three", "quadratic_quadratic_three", "Actual quadratic vacuum pairing", "The actual mode-three coefficient mu(Q(i,j),3,Q(k,l)) equals (G(i,k) G(j,l) plus G(i,l) G(j,k)) times the actual vacuum, for arbitrary even LatticeData and all colours."),
            Theorem("quadratic-orbit-one", "quadratic_orbit_one", "Quadratic action on a plus orbit", "For every integral charge a and colours i,j, mu(Q(i,j),1,E(a)) equals Gi(i,a) Gi(j,a) times E(a). No charge-norm or positivity premise is used."),
            Theorem("orbit-quadratic-one", "orbit_quadratic_one", "Reversed mixed contraction", "For every integral charge a and colours i,j, mu(E(a),1,Q(i,j)) equals Gi(i,a) Gi(j,a) times E(a). Actual all-state skew symmetry gives this direction after every positive-translation tail coefficient vanishes."),
            Theorem("mixed-three", "mixed_three", "Both mixed vacuum pairings vanish", "For every integral charge a and colours i,j, both actual coefficients mu(Q(i,j),3,E(a)) and mu(E(a),3,Q(i,j)) vanish. The theorem states their conjunction on the production carrier."),
            Theorem("orbit-orbit-one", "orbit_orbit_one", "Complete rootless charge product at mode one", "Let D be an even LatticeData whose real-cast Gram matrix is positive definite and whose integral charges never have norm two. For arbitrary charges a,b, each of norm four, mu(E(a),1,E(b)) is Qcharge(a) if b equals a or -a. Otherwise it is epsilon(a,b) times E(a+b) when the Gram pairing is -2, epsilon(a,-b) times E(a-b) when the pairing is 2, and zero in the remaining cases. Positivity and rootlessness bound the pairing using both a-b and a-(-b); no Cauchy estimate is assumed. In the coincident orbit the actual second creation coefficients cancel their derivative terms and leave the charge-oscillator square. The phases are the literal lower-cocycle epsilon."),
            Theorem("orbit-orbit-three", "orbit_orbit_three", "Complete rootless charge vacuum pairing", "Under the same positive-definiteness, rootlessness and two norm-four premises, the actual coefficient mu(E(a),3,E(b)) is twice the vacuum if b equals a or -a, and zero otherwise. The proof extracts actual ground-series coefficients rather than assuming a bilinear pairing."),
            Paragraph(Text("All products use the existing Carrier, Y, normalized integer-mode mu, translation, integral Gram pairing and lower cocycle. The derivations reuse quadratic_state_field, quadraticSummand_current_commutator, neutralMode_heisenberg, the actual ground series, the derivative-state theorem, all-state skew symmetry and chargeEnergy_gap. The Gram-coordinate and norm-difference formulas are those of LatticeFiniteNegativeGeneration.")),
            Paragraph(Text("Classical construction context is Bakalov-Kac, Twisted Modules over Lattice Vertex Algebras, arXiv math/0402315v1 section 4.1, and Frenkel-Lepowsky-Meurman, Vertex Operator Algebras and the Monster. The actual normal-product and residue suppliers retain Carnahan, Matsuo-Nagatomo and Kytola attribution and their Apache-2.0 licenses. No literature novelty is claimed.")),
            Paragraph(Text("Rank zero and empty norm-four shells remain in scope. These are local product tables in the existing lattice vertex algebra; Monster, Ising, Peirce and simplicity results, fusion, anomalies, CFT, string theory and AdS/CFT remain outside these statements.")))));

    private static DocumentBlock Theorem(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice"),
                LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static DocumentBlock Definition(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice"),
                LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
