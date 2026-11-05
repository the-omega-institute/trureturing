using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class NormFourFixedPeirceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual norm-four Virasoro zero mode obeys the Peirce quartic on the complete theta-fixed energy-two space.",
        H("The Norm-Four Peirce Annihilator on the Whole Fixed Space"),
        Blocks(
            Paragraph(Text("Let D be an even integral lattice whose real-cast Gram matrix is positive definite, "
                + "and suppose every integral charge has norm different from two. Let a have norm four and "
                + "let the complex scalar s satisfy s squared equal to one. Write A for the actual zero-charge "
                + "state with polynomial chargePolynomial(a) squared and E(b) for single(b,1)+single(-b,1). "
                + "The production vector is A/16+s E(a)/4, and L is its actual Y coefficient at integer mode one, "
                + "namely NormFourVirasoroVector.mode(D,a,s,0).")),
            Describe.Lean(
                DescribeId.Create("actual-fixed-energy-two-peirce"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourFixedPeirce.actual_fixed_energy_two_peirce"),
                H("The full actual fixed energy-two space is annihilated"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice"),
                    LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("For every vector in the literal intersection of fixedSpace(D) with the "
                    + "eigenvalue-two space of the Sugawara zero mode formed using the inverse complex Gram matrix, "
                    + "the ambient endomorphism product L(L-1/16)(L-1/2)(L-2) sends that vector to zero. "
                    + "The identities are in the production finite-support lattice carrier and use exact complex rational scalars. "
                    + "There is no premise of invariance, diagonalization, an assumed multiplication table or an Ising representation."))),
                DescribeRole.Theorem),
            Paragraph(Text("For a neutral quadratic Q(i,j)=single(0,X(i,0)X(j,0)), let g_i be the Gram contraction "
                + "with a and R_i=sum_k a_k Q(k,i). The actual contractions give "
                + "LQ(i,j)=g_i R_j/8+g_j R_i/8+s g_i g_j E(a)/4 and "
                + "LR_i=R_i/2+g_i A/8+s g_i E(a). The exceptional block is "
                + "LA=A+4s E(a), LE(a)=s A/4+E(a). These equalities prove "
                + "L(L-1/2)(L-2)Q(i,j)=0 directly, including repeated colours. "
                + "No transverse decomposition is assumed.")),
            Paragraph(Text("For norm-four charges b outside the sign orbit of a, rootlessness and positivity applied "
                + "to a-b and a+b bound the integral pairing between -2 and 2. Pairing zero gives LE(b)=0; "
                + "pairing plus or minus one gives LE(b)=E(b)/16. For pairing -2, the partner a+b has norm four "
                + "and pairing two with a. The actual cocycle obeys epsilon(a,a+b)=epsilon(a,b), since its "
                + "diagonal norm-four phase is one. The return shift a-(a+b)=-b gives the same orbit. "
                + "The resulting two-state block has diagonal 1/4 and off-diagonal s epsilon(a,b)/4; "
                + "the square of the off-diagonal coefficient is 1/16. Thus L squared E(b)=LE(b)/2. "
                + "Negating b gives the pairing-two case. Equal and opposite charges use the exceptional A,E(a) block.")),
            Paragraph(Text("The complete actualFixedEnergyTwoBasis consists of all unordered neutral colour pairs "
                + "and all norm-four charge sign orbits. The neutral coordinate identification and the actual charged "
                + "basis vectors identify their ambient states. Equality of linear maps on this basis then proves "
                + "the quartic for every vector of the full literal fixed energy-two space. Rank zero is included; "
                + "the norm-four premise may then have no witness.")),
            Paragraph(Text("The norm-four state formula is classical: Shimakura, arXiv:1202.6107, equation (1.3), "
                + "attributes the Ising-vector assertion to Dong-Mason-Zhu, Theorem 6.3. The lattice-field construction "
                + "and contractions follow Bakalov-Kac, arXiv:math/0402315, section 4.1, and Frenkel-Lepowsky-Meurman. "
                + "The normal-product and residue sources retain Carnahan, Matsuo-Nagatomo and Kytola attribution "
                + "and their Apache-2.0 licenses. The whole-space argument combines the neutral cubic, the actual "
                + "charge blocks and the complete fixed-space basis.")),
            Paragraph(Text("This polynomial identity does not establish Ising simplicity or fusion, spectral-sign automorphisms, "
                + "Miyamoto involutions, numerical Leech multiplicities, twisted sectors, Monster moonshine, "
                + "CFT anomalies, string theory or AdS/CFT.")))));
}
