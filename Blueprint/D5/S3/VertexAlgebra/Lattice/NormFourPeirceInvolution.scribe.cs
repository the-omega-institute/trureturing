using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class NormFourPeirceInvolutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The explicit charge character preserves every actual lattice mode and equals the norm-four Peirce spectral sign on the whole fixed energy-two space.",
        H("Charge Characters and the Full Peirce Spectral Sign"),
        Blocks(
            Paragraph(Text("For an even integral lattice D and an arbitrary charge a, define chi_a on a state "
                + "single(b,p) by multiplication by (-1) to the integral pairing B(a,b). The polynomial p is unchanged. "
                + "The map is the finite-support linear sum of these sector maps, and chi is its involutive linear equivalence. "
                + "Neither positivity, rootlessness, norm four nor a choice of sign is required for this construction.")),
            Describe.Lean(
                DescribeId.Create("chi-single"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourPeirceInvolution.chi_single"),
                H("The exact charge-sector action"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("Every oscillator polynomial in sector b is multiplied by the same pairing character; "
                    + "no oscillator coordinate is reflected or removed."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chi-involutive"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourPeirceInvolution.chi_involutive"),
                H("The square is the identity on every state"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The square of the pairing sign is one. Equality on all single-sector states "
                    + "extends to the full carrier. This includes the identity character and rank zero, and asserts no exact order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chi-vacuum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourPeirceInvolution.chi_vacuum"),
                H("The actual vacuum is fixed"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The vacuum has zero charge, whose pairing character is one."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("state-field-chi"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourPeirceInvolution.stateField_chi"),
                H("All states and all integer modes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice"),
                    LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("For every actual u,v and every integer n, chi(Y(u)[n]v)=Y(chi(u))[n]chi(v). "
                    + "The existing LatticeSectorIntertwiner.charge_homogeneity identifies each actual coefficient of "
                    + "Y(single(b,p))[n]single(c,q) with a literal single(b+c,r). Multiplicativity of the pairing character "
                    + "then proves covariance on these states. Two extensions of linear maps from Finsupp singles prove "
                    + "the statement for arbitrary oscillator polynomials and all states. Charge homogeneity is reused "
                    + "from the production fields, without an assumed graded vertex algebra or a new normal-product construction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-fixed-energy-two-spectral-sign"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourPeirceInvolution.actual_fixed_energy_two_spectral_sign"),
                H("The whole literal fixed energy-two space"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice"),
                    LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("Assume the real Gram matrix is positive definite, every integral charge has norm "
                    + "different from two, B(a,a)=4, and the complex scalar s has square one. Let L be the production "
                    + "NormFourVirasoroVector.mode(D,a,s,0). On every vector in the literal intersection of fixedSpace(D) "
                    + "with the eigenvalue-two space of the canonical inverse-Gram Sugawara zero mode, chi equals "
                    + "I-(8192/217)L(L-I/2)(L-2I), as an equality in the ambient actual carrier."))), DescribeRole.Theorem),
            Paragraph(Text("The complete actualFixedEnergyTwoBasis supplies unordered neutral colour pairs and all "
                + "norm-four charge sign orbits. Neutral states have character one. The imported actual Q,R,A,E "
                + "zero-mode actions give the cubic L(L-I/2)(L-2I)=0 on neutral quadratics and on the matching A,E block. "
                + "This reduction includes repeated colours; it is not inferred from a quartic annihilator.")),
            Paragraph(Text("For distinct sign orbits, positivity and rootlessness bound B(a,b) between -2 and 2. "
                + "Pairing zero gives LE(b)=0. Pairing plus or minus one gives LE(b)=E(b)/16 and character minus one. "
                + "At 1/16 the cubic is 217/4096, so the polynomial value is exactly minus one. Pairing -2 uses the "
                + "actual return shift a-(a+b)=-b and the existing cocycle identities: the two-state block has diagonal "
                + "1/4 and off-diagonal c=s epsilon(a,b)/4 with c squared equal to 1/16. Consequently L squared E(b)=LE(b)/2, "
                + "so the cubic vanishes and the polynomial is plus one. Negation gives pairing two. Equal and opposite "
                + "charges have even pairing and use the matching block. The pairing character is unchanged by negating b. "
                + "Equality of linear maps on the complete actual basis proves the stated whole-space equality.")),
            Paragraph(Text("The production norm-four formula is the classical formula attributed by Shimakura, "
                + "arXiv:1202.6107, equation (1.3), to Dong-Mason-Zhu, Theorem 6.3. The lattice construction follows "
                + "Bakalov-Kac, arXiv:math/0402315, section 4.1, and Frenkel-Lepowsky-Meurman. The actual Peirce actions "
                + "and fixed-space basis are imported mathematical suppliers. The result identifies the explicit "
                + "all-mode character with the spectral polynomial; it makes no claim of Ising simplicity or fusion, "
                + "occurrence of all four eigenvalues, numerical Leech multiplicities or Monster moonshine.")))));
}
