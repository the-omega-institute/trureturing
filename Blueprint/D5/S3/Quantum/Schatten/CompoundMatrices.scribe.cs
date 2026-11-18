using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class CompoundMatricesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compound matrices and singular products.", H("CompoundMatrices"), Blocks(
            Paragraph(Text("The kth compound matrix has entries equal to kth order minors. Cauchy-Binet makes the compound construction multiplicative. Unitary diagonalization identifies its singular values with products over kth order subsets; sorting identifies the largest such product.")),
            Paragraph(Text("The source is Alex Meiburg's Apache-2.0 Physlib at revision "
                + "b9043cc548ef6d63a28454cf3a57fb12a0c2e142. These results support the "
                + "Schatten product Holder inequality. No mathematical originality is claimed.")),
            Paragraph(Text("Ordered Slater amplitudes give a further application of the rectangular "
                + "cauchyBinet formula over the complex numbers and over complex polynomials. "
                + "Let N and k be arbitrary natural numbers, let the sites be Fin N in their natural "
                + "order, and let V be a complex N by k matrix with V†V = I. A Boolean occupation "
                + "word x has occupied set S(x) = {a | x(a) = true}. If this set has cardinality k, "
                + "write V[S(x)] for the square matrix whose rows are selected by "
                + "S(x).orderEmbOfFin in increasing site order and whose columns retain their "
                + "original order. Set ψV(x) = det(V[S(x)]) in this case and ψV(x) = 0 otherwise. "
                + "The empty determinant is 1. These are coordinates in the normalized Boolean "
                + "occupation basis, so no factor involving the square root of k factorial occurs.")),
            Paragraph(Text("Define ρV(x,y) = ψV(x) conjugate(ψV(y)) and P = VV†. Use exactly "
                + "JordanWigner.fullC for each annihilator c(a). HardCoreCompression.fullC_entry "
                + "identifies its entry from t to s: it vanishes unless t occupies a and s is t "
                + "with a emptied; its nonzero value is (−1) raised to prefixCount(t,a), the number "
                + "of occupied sites strictly below a in the original site order. The "
                + "fullC_sparse and fullC_create_sparse identities in "
                + "PeriodicSshExcessPseudoEntropyRefutation apply these same matrices to an "
                + "arbitrary complex coordinate function. They supply the annihilation and creation "
                + "actions without any assumption about Gaussianity or a covariance matrix.")),
            Paragraph(Text("For fixed sites i and j introduce the elementary matrix E(j,i), whose "
                + "only nonzero entry is 1 in row j and column i. Over the polynomial ring in X set "
                + "W(X) = (I + X E(j,i)) V, with all complex entries embedded as constant "
                + "polynomials. Thus only row j changes: W(j,b) = V(j,b) + X V(i,b). Define "
                + "ψW(X)(x) by the same ordered-minor rule. The coefficient of X in ψW(X)(x) is "
                + "exactly the coordinate at x of c(j)† c(i) ψV.")),
            Paragraph(Text("This coefficient correspondence retains every occupation case. If j "
                + "is absent, the selected minor is constant in X and the creation action is zero. "
                + "If j is present, put R = S(x) with j erased. When i belongs to R, replacing "
                + "row j by row i produces two equal rows and the determinant is zero; annihilation "
                + "at the already occupied coordinate of the intermediate word is also zero. "
                + "Otherwise the common coefficient is (−1) raised to "
                + "(|{a in R | a < j}| + |{a in R | a < i}|), multiplied by the ordered minor on "
                + "R with i inserted. The formulas include i = j. Words of the wrong cardinality "
                + "give zero on both sides because this removal followed by insertion preserves "
                + "cardinality.")),
            Paragraph(Text("For the sign comparison, the sorted_position_count and sorted_removeNth "
                + "identities in PhysicalContractionRdmBridge transfer from finite subsets of the "
                + "natural numbers through the order-preserving map Fin.val. Fin.cons_removeNth_eq_comp_cycleRange_symm "
                + "moves the replaced row to the head; Matrix.det_permute and Fin.sign_cycleRange "
                + "give its sign. Applying this once for the erased j and once for the inserted i "
                + "gives the two counts above. Matrix.det_updateRow_add and det_updateRow_smul "
                + "extract the linear coefficient, while det_updateRow_eq_zero handles the repeated "
                + "row case. This uses neither a quotient of minors nor division by an amplitude.")),
            Paragraph(Text("Now set F(X) = det(V† W(X)). Rectangular cauchyBinet over complex "
                + "polynomials gives F(X) as the sum over all Boolean words x of "
                + "conjugate(ψV(x)) ψW(X)(x); Matrix.det_conjTranspose supplies the conjugated "
                + "minor. Since V†V = I, the same polynomial is "
                + "det(I + X V† E(j,i) V). Matrix.coeff_det_one_add_X_smul_one identifies its "
                + "linear coefficient with trace(V† E(j,i) V). Matrix.trace_mul_cycle and "
                + "trace_mul_single turn that trace into P(i,j). On the occupation side, finite "
                + "coefficient extraction and the preceding correspondence give the sum of "
                + "conjugate(ψV(x)) times the coordinate of c(j)† c(i) ψV. "
                + "Matrix.mul_vecMulVec and trace_vecMulVec identify this with "
                + "trace((ρV c(j)†) c(i)). Consequently K(i,j) = P(i,j), whereas the convention "
                + "C(i,j) = trace((ρV c(i)†) c(j)) gives C(i,j) = P(j,i) = conjugate(P(i,j)). "
                + "In matrix notation C is the transpose of P.")),
            Paragraph(Text("The occupation-basis and Slater conventions agree with Jan Dereziński, "
                + "Clifford algebras and fermions, sections 7.1 and 7.2, equations (7.51)–(7.54). "
                + "Theorem 8.1 and equation (8.103), giving the expectation of dΓ(h) as "
                + "trace(πh), state the corresponding one-body expectation formula. "
                + "The source is https://www.fuw.edu.pl/~derezins/clifford.pdf. "
                + "The ordered determinant amplitudes and their two-point identity are standard "
                + "applications; no mathematical originality is claimed for them.")),
            Paragraph(Text("All sums and polynomial identities are finite. The argument covers "
                + "vacuum and full filling, equal sites, either ordering of distinct sites and "
                + "arbitrary complex phases. N = 0 leaves no site indices to choose. No positive "
                + "filling premise or strict inequality k < N is used. The construction concerns "
                + "the specified determinant vector and the original Jordan-Wigner operators; "
                + "it does not by itself identify a ground state of a chosen Hamiltonian or "
                + "establish a spatial reduced spectrum or an entropy scaling law.")))));
}
