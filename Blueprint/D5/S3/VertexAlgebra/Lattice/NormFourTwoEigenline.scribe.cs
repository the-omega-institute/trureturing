using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class NormFourTwoEigenlineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete actual fixed energy-two eigenspace at two is the nonzero norm-four vector line.",
        H("The Actual Norm-Four Two-Eigenline"),
        Blocks(
            Paragraph(Text("Let D be an even integral lattice with positive definite real Gram matrix, "
                + "with no integral charge of norm two. Let a have norm four and let the complex scalar s "
                + "satisfy s squared equal to one. Put e=NormFourVirasoroVector.vector(D,a,s), "
                + "L=NormFourVirasoroVector.mode(D,a,s,0), and let S be the literal intersection of "
                + "theta fixedSpace(D) with the eigenvalue-two space of the canonical inverse-Gram "
                + "Sugawara zero mode on the full production Carrier(D).")),
            Describe.Lean(
                DescribeId.Create("actual-fixed-energy-two-eigenline"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/NormFourTwoEigenline.actual_fixed_energy_two_eigenline"),
                H("The nonzero vector spans the whole two-eigenline"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice"),
                    LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("The actual vector e is nonzero, and S intersected with the actual "
                    + "eigenvalue-two subspace of L equals the complex span of the singleton e. "
                    + "There is no rank, decomposition, diagonalization, eigenline or smaller-span premise."))),
                DescribeRole.Theorem),
            Paragraph(Text("Write A=single(0,chargePolynomial(a)^2), E(b)=single(b,1)+single(-b,1), "
                + "Q(i,j)=single(0,X(i,0)X(j,0)), and g_i for the Gram pairing of colour i with a. "
                + "For P=(16/93)L(L-1/16)(L-1/2), the actual action identities give "
                + "P Q(i,j)=(g_i g_j/2)e, including i=j, and P E(a)=2s e. "
                + "Opposite charges give the same orbit. All other norm-four charge orbits have pairing "
                + "zero, plus or minus one, or plus or minus two. The first three cases are killed "
                + "by P directly. The pairing-two blocks have diagonal 1/4 and off-diagonal "
                + "s epsilon(a,b)/4 whose square is 1/16; the actual return actions show L squared= L/2 "
                + "on these blocks, so P kills them too.")),
            Paragraph(Text("Compose P with the quotient map by the line of e. It vanishes on every "
                + "vector of the existing complete actualFixedEnergyTwoBasis, hence on all of S. "
                + "For Lv=2v the exact polynomial gives Pv=v, proving the forward inclusion. "
                + "For the reverse inclusion, A is a sum of actual neutral quadratic basis states, "
                + "and E(a) is theta fixed and belongs to the actual charge grade-two space. "
                + "The existing canonical Sugawara/grade equality therefore puts e in S. "
                + "The second conjunct of NormFourVirasoroVector.self_products gives Le=2e. "
                + "Finally the actual charge-a constant coefficient of e is s/4. Norm four implies "
                + "a is neither zero nor its own negative; s squared equal to one implies s is nonzero. "
                + "This coefficient proves e is nonzero.")),
            Paragraph(Text("The norm-four formula is classical: Shimakura, arXiv:1202.6107, (1.3), "
                + "attributes the Ising-vector assertion to Dong-Mason-Zhu, Theorem 6.3. "
                + "The production construction and imported contractions retain their Bakalov-Kac, "
                + "Frenkel-Lepowsky-Meurman, Carnahan, Matsuo-Nagatomo and Kytola attribution "
                + "and licenses in their owning sources. This theorem proves the exact whole-space "
                + "two-eigenline; it asserts no Ising simplicity, complete axial fusion, numerical "
                + "Leech multiplicities or Monster completion.")))));
}
