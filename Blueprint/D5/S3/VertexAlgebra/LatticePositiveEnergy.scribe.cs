// Apache-2.0. Source-only canonical staging; official emission remains separate.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticePositiveEnergyDocument : IScribeDocumentDefinition
{
    // Prospective precise library note; registration is recorded in ScribeLibraryReferencePlan.json.
    // FromLiterature identifies construction context, not a verbatim source for the new native proofs.
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact integral half-norm identities and infinite-label oscillator counting on the actual lattice.",
        H("Actual Integral Energy and Finite Oscillator Sublevels"),
        Blocks(
            Paragraph(Text("D is ordinary LatticeGeneratingFieldLocality.LatticeData: any natural rank, including zero, with an "
                + "integral symmetric Gram matrix G and even diagonal. Charge(D)=Fin(rank(D))->Z; Index(D)=Fin(rank(D)) "
                + "x N; Exponent(D)=Index(D)->_0 N. The actual Carrier(D) is the finite-support charge sum of complex "
                + "multivariate polynomials in Index(D). A label is (alpha,d), and its actual basis vector is "
                + "single(alpha,monomial(d,1)). Write q_D(alpha)=B_D(alpha,alpha)/2 in Z, w(d)=sum_x (x.2+1)*d(x), and "
                + "E_D(alpha,d)=q_D(alpha)+w(d) in Z. Geometric positivity means exactly hD: "
                + "Matrix.PosDef(G.map(Int.cast:Z->R)); it is supplied only where stated. There is no positive-rank, "
                + "integral determinant-unit, unimodularity or assumed finite-grade premise.")),
            Paragraph(Text("Every declaration described here is publicly named in D5.S3.VertexAlgebra.LatticePositiveEnergy, "
                + "including declarations whose source module has a different file name. Definition bindings expose the "
                + "actual data or constructed equivalences; the substantive completion consists of the proved "
                + "positivity, finiteness, decomposition and actual-operator theorems.")),
            Paragraph(Text("The five lower-matrix/cocycle helpers are exact consumed bodies from the public "
                + "LatticeTwistedGroundRealization.SignQuotient generation source, SHA256 "
                + "f7032c03d6edd67435d766c9e0c503774dd50561742e3c6e95f722b657f47781. They are used in two_chargeEnergy "
                + "and subsequent positivity, not unused scaffolding. The finite oscillator encoding adapts the "
                + "source-only advisory probe and PolynomialFockLZeroSpectrum; no historical probe object is claimed.")),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-lowermatrix"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.lowerMatrix"),
                H("Integral lower Gram matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The strict lower triangle of G is completed with the integral halfDiagonal on its diagonal. This is "
                        + "the consumed realized-cocycle helper, with its proof source retained exactly."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-lower-matrix-formula"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.lower_matrix_formula"),
                H("Cocycle as a matrix contraction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For all charges alpha,beta, lowerCocycleExponent(D,alpha,beta) is sum_i sum_j alpha_i "
                        + "lowerMatrix(D)_(ij) beta_j. No positivity is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-lower-matrix-symmetrization"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.lower_matrix_symmetrization"),
                H("Integral symmetrization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("lowerMatrix(D)+transpose(lowerMatrix(D))=G. Symmetry and even diagonal are fields of D, not "
                        + "additional assumptions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-integral-cocycle-symmetrization"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.integral_cocycle_symmetrization"),
                H("Cocycle recovers the bilinear form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For all charges alpha,beta, c(alpha,beta)+c(beta,alpha)=B_D(alpha,beta). This identity is consumed "
                        + "in the exact integral half-norm proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-integral-cocycle-square"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.integral_cocycle_square"),
                H("Exact integral half-norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("c(alpha,alpha)=B_D(alpha,alpha)/2 in Z, for every ordinary D and charge alpha. Division is integral, "
                        + "and the preceding symmetrization establishes exact divisibility."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-exponent"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.Exponent"),
                H("Actual oscillator exponent type"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Exponent(D) is the finitely supported natural exponent function on Fin(rank(D)) x N. The index type "
                        + "is infinite when rank is positive."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-label"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.Label"),
                H("Actual all-charge monomial labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Label(D)=Charge(D) x Exponent(D). This type indexes the entire actual carrier basis, without a "
                        + "finite-variable truncation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-chargeenergy"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy"),
                H("Integral charge energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("chargeEnergy(D,alpha) is B_D(alpha,alpha)/2 in Z. The following cocycle and doubling identities "
                        + "prove this is the exact half-norm."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-chargeenergy-cocycle"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy_cocycle"),
                H("Charge energy is realized cocycle square"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("q_D(alpha)=lowerCocycleExponent(D,alpha,alpha), for every charge alpha and ordinary D, including "
                        + "rank zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-two-chargeenergy"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.two_chargeEnergy"),
                H("No lost half-norm remainder"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("2*q_D(alpha)=B_D(alpha,alpha) in Z. Evenness is proved from the consumed realized integral cocycle, "
                        + "not a divisibility axiom."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-bilinear-even"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.bilinear_even"),
                H("All integral charge squares are even"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Even(B_D(alpha,alpha)) for every charge alpha follows from the exact doubling identity. No "
                        + "positivity or unimodularity is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-chargeenergy-zero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy_zero"),
                H("Zero charge has zero energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("q_D(0)=0 unconditionally for every ordinary D."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-bilinear-positive"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.bilinear_positive"),
                H("Real Gram positivity controls integral charges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Under hD and alpha!=0, 0<B_D(alpha,alpha) in Z. The real positive-definite quadratic form is "
                        + "evaluated on the real cast of the integral charge."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-chargeenergy-nonneg"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy_nonneg"),
                H("Derived nonnegative integral charge energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Under hD, q_D(alpha)>=0 for all charges. The proof handles alpha=0 separately and uses positive "
                        + "square plus exact doubling for nonzero alpha."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-chargeenergy-eq-zero-iff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.chargeEnergy_eq_zero_iff"),
                H("Only the zero charge has zero energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Under hD, q_D(alpha)=0 iff alpha=0. This conclusion includes arbitrary finite rank and rank zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-oscillatorenergy"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.oscillatorEnergy"),
                H("Frequency-weighted oscillator energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("w(d)=Finsupp.weight(fun (i,k)=>k+1,d) in N. The polynomial variable (i,k) represents positive "
                        + "frequency k+1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-energy"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.energy"),
                H("Full integral lattice energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("E_D(alpha,d)=q_D(alpha)+(w(d):Z). This grades all charge sectors of the actual carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-oscillatorlefinite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.oscillatorLeFinite"),
                H("Finite sublevels despite infinite labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every D and N:N, {d:Exponent(D) | w(d)<=N} is finite, without hD. An occupied frequency obeys "
                        + "k+1<=N; every exponent is <=N. Restriction injects this sublevel into (Fin(rank(D)) x "
                        + "Fin(N))->Fin(N+1). N=0 and rank zero are included. No finite Index(D) instance is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-oscillatorenergy-eq-zero-iff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.oscillatorEnergy_eq_zero_iff"),
                H("Zero oscillator energy is the constant monomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every ordinary D, w(d)=0 iff d=0, because every frequency weight is positive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-energy-nonneg"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.energy_nonneg"),
                H("Full energy is nonnegative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Under hD, E_D(alpha,d)>=0 for every label, by nonnegative charge energy and natural oscillator "
                        + "weight."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticepositiveenergy-energy-eq-zero-iff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticePositiveEnergy.energy_eq_zero_iff"),
                H("Unique zero-energy label"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Under hD, E_D(alpha,d)=0 iff (alpha,d)=(0,0). Both nonnegative summands must vanish."))),
                DescribeRole.Theorem),
            Paragraph(Text("Bakalov-Kac, Twisted Modules over Lattice Vertex Algebras, arXiv math/0402315v1 (19 February 2004): "
                + "section 4.1, printed/PDF page 8, equations (4.3)-(4.5), gives the charge/Fock carrier; page 9, "
                + "Theorem 4.1 and (4.16), gives the dual-basis conformal vector; page 4, Definition 2.2 and "
                + "(2.23)-(2.24), gives the conformal grading convention. These are construction and convention "
                + "locators, not proofs of the new coercivity and counting results.")),
            Paragraph(Text("Borcherds, Vertex algebras, Kac-Moody algebras, and the Monster, PNAS 83 (1986), 3068-3071: the "
                + "author-hosted retypesetting, section 2, printed/PDF page 2, specifies deg(e^alpha)=B(alpha,alpha)/2 "
                + "and the frequency-weighted oscillator degree. Its SHA256 is "
                + "822e39a2ec7bd33ad81193b06b7a66ae89abcec43c4cb7974d4bc513c3fce5b5. It has no equation numbers there; "
                + "no correspondence to a particular original journal page is asserted.")),
            Paragraph(Text("Dong-Li-Mason, Regularity of rational vertex operator algebras, arXiv q-alg/9508018v1 (24 August "
                + "1995), printed/PDF page 3, Definition 2.1, supplies the ordinary-module finite-dimensional "
                + "eigenspace and lower-truncation convention. Those properties are derived here from hD, rather than "
                + "assumed. Its regularity theorem is not proved by this unit.")),
            Paragraph(Text("Lean 4.33.0 and the declared Mathlib pin db584cd6d46c92f209a44c0f1c829460d327499d supply the actual "
                + "imported finite-support, basis, compactness and matrix APIs. Mathlib adaptations retain Apache-2.0 "
                + "and the original authorship. Exact producer References, SourceInputs, SourceAdaptation, "
                + "MathlibLocators and source/object/import hashes are delivered with this staging; the pin is "
                + "inherited from sealed toolchain evidence and was not established by a fresh Git inspection.")),
            Paragraph(Text("This unit supplies the actual lattice carrier with a positive finite energy grading and identifies "
                + "it with the actual Sugawara L_0 eigenspaces under the explicit inverse pair. It does not construct a "
                + "PCT involution, Hermitian form, analytic Hilbert completion, twisted vertex algebra, Monster "
                + "realization, fusion category, anomaly, string theory or AdS/CFT. The complete supplier Virasoro "
                + "theorem is a separate result and is not replaced by these modules.")))));
}
