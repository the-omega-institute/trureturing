using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.NestedResidues;

internal sealed class LatticeHalfFockABOuterTaylorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete original actual nested-Q weighted middle Taylor equality.",
        H("LatticeHalfFockABOuterTaylor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forward-weighted-identity"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABOuterTaylor.forward_weighted_identity"),
                H("The full original actual weighted middle equality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("Retain every original state, covector, homogeneous six-word coefficient equation, signed lift, supplied inner cutoff K, and independent genuine whole-field locality order H(j). For degree=L+M+K-d-r-2, the original weighted sum over j<(K-r).toNat equals the original sum over u<(degree+1).toNat of collisionTaylor(P,gamma,u,(degree-u).toNat) times orderedResidueWeight(d-L,degree-u+r-K). The conclusion holds for all signed degrees and all cutoffs.")),
                    Paragraph(Text("The unchanged original data collisionTaylor(P,gamma,u,v) sums P.coeff(e) times choose(e(0)-1/2,u) times choose(e(1)-gamma/2,v) over the finite support. orderedResidueWeight(k,m) is zero for nonnegative m and otherwise (-1)^(-m-1) times choose(k,(-m-1).toNat). The source has three cohesive children for local residues, actual readouts and binary evaluation, with only consumed originals exposed across their actual file boundaries.")),
                    Paragraph(Text("For K>r put t=(K-r-1).toNat. The genuine completeAB residue at w=r+j is cleared at B(j)=L+M+t-j. Expanding its original signed Laurent monomials produces a finite sum indexed by ell,u with ell+u<=t-j. Each term is the original remaining monomial with z exponent shifted by e(1)-ell-u, multiplied by (y-z)^(ell+u), the original fractional coefficient choose(-gamma/2,ell), choose(e(1),u), and chooseSign(-L,t-j-ell-u). This polynomial is derived from completeAB, and injectivity of the Laurent polynomial embedding identifies it with the actual Q(j).")),
                    Paragraph(Text("A graded fractional Taylor functional keeps the exact total-exponent fiber. Multiplication by y-z shifts its Taylor order by one, with a zero boundary at order zero. Iteration gives the full ell+u boundary, and Vandermonde combines ell and u into v. The supplied actual coefficient equation supplies the required homogeneous fiber; no extra homogeneity or locality assumption is added. Thus binaryTaylor(Q(j),B(j),1,d-j,n) equals the sum over v<=t-j of collisionTaylor(P,gamma,(degree-v).toNat,v), cut off when v>degree, times chooseSign(-L,t-j-v).")),
                    Paragraph(Text("The proof actually applies finite_forward_outer_taylor at t to this same-P coefficient identity. The K<=r empty branch and negative-degree branch are retained. All original signed numerator exponents, empty supports, zero degree and boundary fibers remain in scope. The fused and reverse components of sameNumeratorCollisionBridge are separate obligations; this result closes its complete middle conjunct.")),
                    Paragraph(Text("The Reg mirror reconstructs the complete source telescope and proves its actual law. Four-slot registration remains unfinished under issue #20163: whole-family intervention, sensitivity, observational dependence and final sourceSelection/escapeFrom evidence are absent. No declared_validated status or independent admission is asserted."))),
                DescribeRole.Theorem))));
}
