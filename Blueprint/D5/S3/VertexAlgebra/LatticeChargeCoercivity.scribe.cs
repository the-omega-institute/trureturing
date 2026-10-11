// Apache-2.0.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeChargeCoercivityDocument : IScribeDocumentDefinition
{
    // FromLiterature identifies construction context, not a verbatim source for the new native proofs.
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real Gram positivity derives bounded charge boxes and finite all-integer full energy fibers.",
        H("Geometric Coercivity and Finite Full Energy Fibers"),
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
            Paragraph(Text("The compact sphere lies in EuclideanSpace R (Fin(rank(D))). The empty-sphere case is proved rather "
                + "than excluded. Mathlib IsCompact.exists_isMinOn, isCompact_sphere and EuclideanSpace.real_norm_sq_eq "
                + "supply compact minimization and the L2 identity; the actual lattice coercivity and "
                + "integer-coordinate bounds are proved in this source.")),
            Describe.Lean(
                DescribeId.Create("latticechargecoercivity-realquadratic"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeChargeCoercivity.realQuadratic"),
                H("Quadratic form on Euclidean L2 space"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Q_D(x)=sum_i sum_j x_i (G_ij:R) x_j on EuclideanSpace R (Fin(rank(D))). The norm used below is the "
                        + "L2 norm, not the supremum norm on ordinary functions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticechargecoercivity-realquadratic-continuous"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeChargeCoercivity.realQuadratic_continuous"),
                H("Continuity of the actual quadratic form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Q_D is continuous by finite sums and products. No hD is needed for continuity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticechargecoercivity-realquadratic-zero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeChargeCoercivity.realQuadratic_zero"),
                H("Quadratic form at zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Q_D(0)=0 for every ordinary D."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticechargecoercivity-realquadratic-smul"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeChargeCoercivity.realQuadratic_smul"),
                H("Quadratic scaling"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every real t and Euclidean x, Q_D(t*x)=t^2 Q_D(x), without hD."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticechargecoercivity-realquadratic-positive"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeChargeCoercivity.realQuadratic_positive"),
                H("Positive real quadratic form"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Under hD, Q_D(x)>0 whenever x!=0. This uses the real Gram form on the Euclidean carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticechargecoercivity-quadratic-coercive"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeChargeCoercivity.quadratic_coercive"),
                H("Compact-sphere coercivity with rank zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Under hD there exists c:R with c>0 such that c*sum_i x_i^2<=Q_D(x) for every Euclidean x. On a "
                        + "nonempty compact unit sphere the continuous positive form has a positive minimum; nonzero x is "
                        + "normalized. If the sphere is empty, every x is zero and c=1 works. Thus rank zero is internal to the "
                        + "theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticechargecoercivity-realquadratic-charge"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeChargeCoercivity.realQuadratic_charge"),
                H("Real quadratic value equals twice charge energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every charge alpha, Q_D(WithLp.toLp(2,fun i=>(alpha_i:R)))=2*(q_D(alpha):R). This exact cast "
                        + "identity is unconditional."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticechargecoercivity-charge-sublevel-box"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeChargeCoercivity.charge_sublevel_box"),
                H("Derived bounded integer charge box"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Under hD, for every N:N there exists B:N such that q_D(alpha)<=N implies alpha_i in [-B,B] for all "
                        + "i. Coercivity gives a uniform coordinate-square bound; an Archimedean natural B is chosen from it. "
                        + "No charge bound or finiteness is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticechargecoercivity-chargesublevel-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeChargeCoercivity.chargeSublevel_finite"),
                H("Finite charge sublevels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Under hD and for every N:N, the set of all charges with q_D(alpha)<=N is finite. It is a subset of "
                        + "the derived finite product of integer intervals."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticechargecoercivity-energyfiber"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeChargeCoercivity.EnergyFiber"),
                H("The entire integer energy fiber"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("EnergyFiber(D,n)={a:Label(D) // E_D(a)=n}, with n:Z, so negative as well as nonnegative fibers are "
                        + "represented."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticechargecoercivity-energyfiber-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeChargeCoercivity.energyFiber_finite"),
                H("Finite full energy fibers for every integer"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Under hD, EnergyFiber(D,n) is finite for every n:Z. A label of energy n injects into the product of "
                        + "the charge and oscillator sublevels bounded by n.toNat. This proves finiteness on the full actual "
                        + "label set, not a preselected finite-dimensional sector."))),
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
                + "and the original authorship.")),
            Paragraph(Text("This unit supplies the actual lattice carrier with a positive finite energy grading and identifies "
                + "it with the actual Sugawara L_0 eigenspaces under the explicit inverse pair. It does not construct a "
                + "PCT involution, Hermitian form, analytic Hilbert completion, twisted vertex algebra, Monster "
                + "realization, fusion category, anomaly, string theory or AdS/CFT. The complete supplier Virasoro "
                + "theorem is a separate result and is not replaced by these modules.")))));
}
