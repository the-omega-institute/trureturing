using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class LocallyNilpotentPerturbationCohomologyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pointwise inverse polynomials yield actual quotient inverses and incoming primitives.",
        H("Locally nilpotent perturbation on literal cohomology"), Blocks(
            Paragraph(Text("Over a commutative ring R, let c be the FinitePerturbation.Input on R-modules U,V: d0²=D²=0 for D=d0+delta, p i=id, d0 i=p d0=0, d0 h+h d0=id-i p and h²=h i=p h=0. Assume pointwise local nilpotence: for every x∈V some n satisfies (h delta)^n x=0. The global linear operator K=(1+h delta)⁻¹ agrees on that x with Σ_{j<n}(-h delta)^j x. Injectivity of 1+h delta uses a cutoff for x-y, and surjectivity uses a cutoff for the desired output. This constructs a linear inverse without a uniform exponent. The opposite inverse is J=1-delta K h. Set I=K i, P=p J, H=K h and d_U=p delta I.")),
            Paragraph(Text("Attribution: Gugenheim–Lambe–Stasheff's algebraic perturbation lemma is implemented by the existing finite and locally nilpotent suppliers. The literal quotient and generic descent follow FinitePerturbationCohomology, the repository LatticeOriginalAbsoluteZeroCohomology pattern and Joël Riou's Mathlib homology construction. Mathlib's units, linear maps, quotient equality and induction retain Johannes Hölzl, Mario Carneiro, Kevin Buzzard and Yury Kudryashov attribution, Apache 2.0. Batteries.OpenPrivate is due to Mario Carneiro and Microsoft Corporation, Apache 2.0.")),
            Describe.Lean(DescribeId.Create("local-perturbation-cohomology-equiv"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.cohomologyEquiv"),
                H("Global quotient equivalence from vectorwise finite inverses"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For c and the stated pointwise nilpotence hypothesis, the source is the actual ker D modulo range(D into ker D); the target is the same quotient construction for the actual transferred d_U. Its square-zero and chain laws are derived by locally_nilpotent_perturbation. Submodule.mapQ descends P and I because P D=d_U P and D I=I d_U carry actual images to actual images.")),
                    Paragraph(Text("On a source cycle x the round trip has difference x-I(P x)=D(H x), so H x is the boundary witness in the source quotient. On a target cycle u the retract P I=id gives equality before quotienting. Quotient induction proves both inverse laws on all classes. Evaluation of H x uses a finite cutoff for h x; evaluation of I u uses a cutoff for i u. A single exponent for the entire carrier is unnecessary."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("local-perturbation-cycle-primitive"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.cycle_primitive"),
                H("The homotopy gives the actual difference primitive"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a D-cycle x∈V, the asserted equality is D(H x)=x-I(P x). It evaluates D H+H D=id-I P at x and uses D x=0. Thus the discrepancy between x and its included projection is the differential of a specified vector in V.")),
                    Paragraph(Text("Here H x=K(h x). Choose n only for h x with (h delta)^n(h x)=0; the global inverse evaluates as the finite alternating polynomial on that vector. The equality does not say x itself is exact unless the included projected contribution is also removed. It is precisely the source inverse witness used in the cohomology equivalence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("local-perturbation-cohomology-equiv-mk"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.cohomologyEquiv_mk"),
                H("Projection of each literal cycle representative"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every x∈V with D x=0, the equivalence sends its actual quotient class to [P x] in ker d_U/range d_U. The target membership follows from d_U(P x)=P(D x)=0; the theorem reuses the representative readout of cohomologyProjection.")),
                    Paragraph(Text("The projected vector is p J x=p(x-delta K(h x)). A cutoff for h x evaluates the K term as a finite polynomial, while the globally defined J makes P linear on all V. Changing a lift by D y changes P x by d_U(P y), exactly the boundary required for quotient descent."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("local-perturbation-cohomology-equiv-symm-mk"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.cohomologyEquiv_symm_mk"),
                H("Corrected inclusion of each transferred cycle"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For u∈U with d_U u=0, the inverse equivalence sends [u] to [I u]. The corrected representative I u=K(i u) is a D-cycle by the inclusion-chain law. A cutoff for i u gives the concrete finite sum Σ_{j<n}(-h delta)^j(i u).")),
                    Paragraph(Text("This is the representative formula of cohomologyInclusion, which descends I using its actual chain identity. A target boundary d_U v lifts to D(I v). The formula therefore describes the inverse on the literal kernel/image quotients, including when d_U is nonzero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("local-perturbation-boundary-iff-transferred-boundary"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/LocallyNilpotentPerturbationCohomology.boundary_iff_transferred_boundary"),
                H("Transferred exactness produces an original-module preimage"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a D-cycle x, exactness D y=x in V is equivalent to d_U u=P x for some u∈U. The forward implication takes u=P y, using P D=d_U P. It compares genuine differential images on the full modules.")),
                    Paragraph(Text("For the reverse implication the constructed vector is I u+H x. The inclusion-chain law gives D(I u)=I(d_U u), and cycle_primitive gives D(H x)=x-I(P x); their sum is x. Both corrections can be evaluated by finite inverse polynomials with their own vector-dependent cutoffs. No zero-transfer premise is used."))), DescribeRole.Theorem))));
}
