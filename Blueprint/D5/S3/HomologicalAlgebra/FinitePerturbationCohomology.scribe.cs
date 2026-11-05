using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class FinitePerturbationCohomologyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite perturbation descends to literal kernel modulo image with explicit inverse and primitives.",
        H("Finite perturbation on actual cohomology quotients"), Blocks(
            Paragraph(Text("Let R be a commutative ring and U,V be R-modules with additive group structures. The input c consists of d0,h,delta on V and i:U→V, p:V→U, with d0²=0, p i=id, d0 i=0, p d0=0, d0 h+h d0=id-i p, h²=0, h i=0, p h=0 and D²=0 for D=d0+delta. For n≥1 assume (h delta)^n=0. The actual finite inverses are K_n=Σ_{j<n}(-h delta)^j and J_n=Σ_{j<n+1}(-delta h)^j: the opposite power vanishes at n+1. Write I_n=K_n i, P_n=p J_n, H_n=K_n h and d_n=p delta I_n. The transferred differential d_n is retained, and its square-zero law is a conclusion of the perturbation identities.")),
            Paragraph(Text("Attribution: the basic perturbation lemma is due to Gugenheim–Lambe–Stasheff. This source reuses the repository FinitePerturbation inference and its LatticeOriginalAbsoluteZeroCohomology quotient pattern, also used by Joël Riou's Mathlib ShortComplex.moduleCatLeftHomologyData. Mathlib supplies geometric sums, Submodule.mapQ, quotient equality and induction, with attribution to Johannes Hölzl, Mario Carneiro, Kevin Buzzard and Yury Kudryashov under Apache 2.0.")),
            Describe.Lean(DescribeId.Create("finite-perturbation-cohomology-equiv"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/FinitePerturbationCohomology.cohomologyEquiv"),
                H("Finite projection and inclusion give inverse quotient maps"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For c,n≥1 and (c.h*c.delta)^n=0, this linear equivalence has source ker D/range(D into ker D) and target ker d_n/range(d_n into ker d_n). Each boundary submodule is the range of the differential with its codomain restricted using the proved square-zero identity. The chain identities P_n D=d_n P_n and D I_n=I_n d_n make the actual P_n and I_n descend by Submodule.mapQ; thus they act on these literal quotients.")),
                    Paragraph(Text("Quotient induction reduces the two inverse laws to cycles. For a D-cycle x, the homotopy identity gives D(H_n x)=x-I_n(P_n x), so the round trip differs from x by the actual boundary with preimage H_n x. On a transferred cycle u the other round trip is equal to u already in U by P_n I_n=id. Neither inverse proof requires d_n to vanish."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-perturbation-cohomology-equiv-mk"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/FinitePerturbationCohomology.cohomologyEquiv_mk"),
                H("Forward readout on an actual source cycle"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("With the same input, n≥1 and nilpotence law, every x∈V satisfying D x=0 is sent from [x] to [P_n x]=[p J_n x]. The target representative lies in ker d_n because d_n(P_n x)=P_n(D x)=0. This equality exposes the finite projection polynomial, including its n+1 opposite-order terms.")),
                    Paragraph(Text("The readout is definitional for the descended linear map. A source change x↦x+D y changes the displayed representative by d_n(P_n y), exactly the target boundary used to define the quotient; the representative formula therefore agrees with the quotient construction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-perturbation-cohomology-equiv-symm-mk"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/FinitePerturbationCohomology.cohomologyEquiv_symm_mk"),
                H("Inverse readout on a transferred cycle"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a genuine transferred cycle u∈U with d_n u=0, the inverse equivalence sends [u] to [I_n u]=[K_n(i u)]. Its source-cycle proof is D(I_n u)=I_n(d_n u)=0. The expression uses the n-term inverse of 1+h delta, with the alternating signs fixed by inversePolynomial.")),
                    Paragraph(Text("The representative readout follows directly from the inverse quotient map. Replacing u by u+d_n v changes I_n u by D(I_n v). The two displayed readouts are consumed by quotient induction in the inverse laws, where H_n supplies the source boundary and P_n I_n supplies the exact target retract."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-perturbation-boundary-iff-transferred-boundary"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/FinitePerturbationCohomology.boundary_iff_transferred_boundary"),
                H("Exactness transfers with an explicit incoming primitive"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For x∈V with D x=0, under n≥1 and (h delta)^n=0, there exists y∈V with D y=x exactly when there exists u∈U with d_n u=P_n x. If x=D y, projection-chain compatibility gives the target witness P_n y.")),
                    Paragraph(Text("Conversely, from d_n u=P_n x the proof constructs y=I_n u+H_n x in the original module. Its differential is I_n(d_n u)+x-I_n(P_n x)=x. This retains the nonzero transferred differential and gives a literal preimage, with H_n x computed by the finite polynomial K_n applied to h x."))), DescribeRole.Theorem))));
}
