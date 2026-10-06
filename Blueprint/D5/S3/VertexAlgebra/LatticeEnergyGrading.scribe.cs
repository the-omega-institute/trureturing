// Apache-2.0.
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeEnergyGradingDocument : IScribeDocumentDefinition
{
    // FromLiterature identifies construction context, not a verbatim source for the new native proofs.
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact actual coefficient grades have full fiber bases and finite nonhomogeneous projections.",
        H("Actual Finite Grades, Vacuum and Internal Direct Sum"),
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
            Paragraph(Text("Basis, coefficient support, projections and the internal direct sum are constructed for every "
                + "ordinary D, without hD. hD is needed only for finite-dimensionality, exact finite cardinal "
                + "dimensions, negative vanishing, and zero-grade vacuum normalization. The entire Carrier(D) is "
                + "usually infinite-dimensional when rank is positive; finiteness is asserted for each grade.")),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-carriercoeffequiv"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.carrierCoeffEquiv"),
                H("Actual carrier coefficient equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Carrier(D) is linearly equivalent over C to Label(D)->_0 C. Polynomial monomial-basis coordinates in "
                        + "each finite-support charge sector are uncurried. No positivity or finiteness of grades is required."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-carriercoeffequiv-apply"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.carrierCoeffEquiv_apply"),
                H("Exact coefficient evaluation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every actual state v and label (alpha,d), carrierCoeffEquiv(D,v)(alpha,d)=coeff(d,v(alpha)). "
                        + "This is the actual polynomial coefficient, not an abstract eigenbasis assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-carrierbasis"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.carrierBasis"),
                H("Basis of the entire actual carrier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The actual carrier basis is obtained from carrierCoeffEquiv and is indexed by every charge/exponent "
                        + "label."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-carrierbasis-apply"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.carrierBasis_apply"),
                H("Actual basis vector formula"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("carrierBasis(D,(alpha,d))=single(alpha,monomial(d,1)), exactly on the actual carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-grade"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.grade"),
                H("Integer coefficient-support grade"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("grade(D,n) is the inverse image under actual coefficient coordinates of Finsupp.supported at {a | "
                        + "E_D(a)=n}. It is a C-submodule of Carrier(D), for each n:Z."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-mem-grade-iff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.mem_grade_iff"),
                H("Exact grade membership for arbitrary states"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("v belongs to grade(D,n) iff for every label a with E_D(a)!=n, coeff(a.2,v(a.1))=0. v is any actual "
                        + "state, including nonhomogeneous finite sums."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-gradecoeffequiv"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeCoeffEquiv"),
                H("Full fiber coefficient equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("grade(D,n) is linearly equivalent over C to EnergyFiber(D,n)->_0 C. This uses the entire fiber and "
                        + "needs neither positivity nor finiteness."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-gradebasis"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeBasis"),
                H("Basis indexed by the whole energy fiber"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The basis of grade(D,n) is indexed by EnergyFiber(D,n), with no finite-fiber premise. hD later "
                        + "proves that this basis index type is finite."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-gradebasis-coe"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeBasis_coe"),
                H("Grade basis is the actual carrier basis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For each a:EnergyFiber(D,n), the image of gradeBasis(D,n,a) in Carrier(D) equals "
                        + "carrierBasis(D,a.val)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-grade-eq-span"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.grade_eq_span"),
                H("Grade is the actual energy-basis span"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("grade(D,n)=span_C(carrierBasis(D) image {a | E_D(a)=n}), unconditionally for every ordinary D."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-grade-finitedimensional"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.grade_finiteDimensional"),
                H("Derived finite-dimensional actual grades"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Under hD, grade(D,n) is finite-dimensional over C for every integer n. The proof uses the "
                        + "constructed grade basis and the derived finite full fiber; finite-dimensionality is not a "
                        + "hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-grade-finrank"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.grade_finrank"),
                H("Exact integer-grade dimension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Under hD, finrank_C(grade(D,n))=Nat.card(EnergyFiber(D,n)) for every n:Z, including negative n and "
                        + "rank zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-grade-finrank-nat"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.grade_finrank_nat"),
                H("Natural-energy specialization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Under hD and N:N, finrank_C(grade(D,(N:Z)))=Nat.card(EnergyFiber(D,(N:Z))). This is a specialization "
                        + "of the all-integer dimension theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-grade-negative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.grade_negative"),
                H("Negative actual grades vanish"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Under hD and n<0, grade(D,n)=bottom, derived from full energy nonnegativity and exact coefficient "
                        + "separation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-grade-zero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.grade_zero"),
                H("Zero grade is exactly the actual vacuum line"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Under hD, grade(D,0)=span_C{vacuum(D)}. The only energy-zero label is (0,0), whose actual basis "
                        + "vector is single(0,1)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-vacuum-nonzero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.vacuum_nonzero"),
                H("Actual vacuum is nonzero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("vacuum(D)!=0 for every ordinary D. This does not require positivity, a conformal inverse, or "
                        + "positive rank."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-vacuumgradeequiv"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.vacuumGradeEquiv"),
                H("Scalar parametrization of zero grade"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Under hD, the constructed linear equivalence C ~= grade(D,0) is scalar multiplication of the actual "
                        + "vacuum, transported through grade_zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-energyfiber-negative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.energyFiber_negative"),
                H("Negative full fibers are empty"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Under hD and n<0, EnergyFiber(D,n) is empty. This assertion concerns every actual charge/exponent "
                        + "label."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-rank-zero-label"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.rank_zero_label"),
                H("Rank-zero label type has one element"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Assuming only D.rank=0, every label equals (0,0). No positivity or inverse-Gram equation is needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-rank-zero-carrier"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.rank_zero_carrier"),
                H("Rank-zero carrier is the vacuum span"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Assuming only D.rank=0, span_C{vacuum(D)}=top on the entire actual Carrier(D), by the exact carrier "
                        + "basis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-rankzerovacuumequiv"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.rankZeroVacuumEquiv"),
                H("Rank-zero actual carrier is one vacuum line"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Assuming only D.rank=0, the actual carrier is linearly equivalent to C by scalar multiplication of "
                        + "vacuum. The general finite-rank theorems above do not reduce to this boundary case."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-gradeprojection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeProjection"),
                H("Actual coefficient-filter projection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("gradeProjection(D,n) is the actual linear endomorphism obtained by keeping just coefficients at "
                        + "energy n and transporting back to Carrier(D)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-gradeprojection-coeff"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeProjection_coeff"),
                H("Projection acts on exact coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("At label a, the coefficient of gradeProjection(D,n,v) is the original coefficient if E_D(a)=n, and "
                        + "zero otherwise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-gradeprojection-mem"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeProjection_mem"),
                H("Projection lands in its actual grade"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("gradeProjection(D,n,v) belongs to grade(D,n) for any integer n and actual v."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-gradeprojection-on-grade"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeProjection_on_grade"),
                H("Projection fixes its own grade"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("If v belongs to grade(D,n), gradeProjection(D,n,v)=v."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-gradeprojection-other-grade"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeProjection_other_grade"),
                H("Projection kills distinct grades"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("If m!=n and v belongs to grade(D,n), gradeProjection(D,m,v)=0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-gradeprojection-idempotent"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeProjection_idempotent"),
                H("Projection is idempotent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("gradeProjection(D,n)*gradeProjection(D,n)=gradeProjection(D,n) as actual linear endomorphisms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-gradeprojection-disjoint"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeProjection_disjoint"),
                H("Distinct projections compose to zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For m!=n, gradeProjection(D,m)*gradeProjection(D,n)=0 as actual linear endomorphisms."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-stateenergies"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.stateEnergies"),
                H("Finite energies of a nonhomogeneous actual state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("stateEnergies(D,v) is the finite image under E_D of the support of carrierCoeffEquiv(D,v). No "
                        + "homogeneity or positivity is assumed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-gradeprojection-outside"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.gradeProjection_outside"),
                H("Only finitely many projections survive"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("If n is outside stateEnergies(D,v), gradeProjection(D,n,v)=0, for any actual v including mixed "
                        + "charges and mixed energies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-sum-gradeprojections"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.sum_gradeProjections"),
                H("Finite reconstruction of every actual state"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("sum over n in stateEnergies(D,v) of gradeProjection(D,n,v) equals v. This proves a finite "
                        + "nonhomogeneous decomposition on the actual carrier, without hD."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-grades-independent"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.grades_independent"),
                H("Independence against all other grades"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The family grade(D) is iSup-independent: each grade meets the supremum of all the other grades "
                        + "trivially. This is stronger than only pairwise disjointness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-grades-isup"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.grades_iSup"),
                H("All grades span the actual carrier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("The supremum over all integer grades is top, by finite projection reconstruction for arbitrary "
                        + "actual states."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-grades-internal"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.grades_internal"),
                H("Genuine actual internal direct sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("DirectSum.IsInternal(grade(D)) holds: the canonical sum of subtype inclusions from the "
                        + "integer-indexed direct sum is bijective. No hD is needed for internality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticeenergygrading-carrierenergydecomposition"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeEnergyGrading.carrierEnergyDecomposition"),
                H("Constructed canonical decomposition equivalence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Carrier(D) ~= direct sum over n:Z of grade(D,n) as C-linear spaces. This equivalence is the inverse "
                        + "of the canonical sum of actual subtype inclusions, using the proved internality."))),
                DescribeRole.Definition),
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
