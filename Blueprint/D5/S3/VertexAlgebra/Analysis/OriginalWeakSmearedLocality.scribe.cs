using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Analysis;

internal sealed class OriginalWeakSmearedLocalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original weak smeared locality on one smooth domain",
        H("Original weak smeared locality on one smooth domain"),
        Blocks(
            Paragraph(Text("Mathlib supplies completion, normed operators, Fourier analysis, integer binomial identities and unconditional sum machinery under Apache 2.0. The additional arguments here concern the stated original objects and relations. No literature novelty or physical realization is asserted.")),
            Describe.Lean(DescribeId.Create("originalweaksmearedlocality-smearComposition-eq-reverse-of-disjoint-tsupport"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Analysis/OriginalWeakSmearedLocality.smearComposition_eq_reverse_of_disjoint_tsupport"),
                H("Commutation in every bounded Sobolev layer"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every original Model M, arbitrary original charges a,b, Tests f,g with disjoint closed quotient-circle supports, and every natural k, the literal bounded compositions coincide from H_(r+s+k) to H_k, r=order(a), s=order(b). Their actual double commutator series has polynomial growth, the transferred algebraic locality exponent N=(-bilinear(a,b)).toNat, and absolute convergence. Applying the finite contact theorem gives equality with no extra regularity or charge restriction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalweaksmearedlocality-smearFamily-comp-eq-of-disjoint-tsupport"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Analysis/OriginalWeakSmearedLocality.smearFamily_comp_eq_of_disjoint_tsupport"),
                H("Commutation on the same compatible smooth families"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The existing endomorphisms smearFamily(a,f) and smearFamily(b,g) of M.Smooth commute. Their kth components are the literal bounded compositions evaluated at the same family component of order r+s+k. Only equality transport of natural orders identifies s+(r+k) and r+(s+k) with this order."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalweaksmearedlocality-field-comp-eq-of-disjoint-tsupport"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Analysis/OriginalWeakSmearedLocality.field_comp_eq_of_disjoint_tsupport"),
                H("Literal field products on the same smoothDomain"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every u in the existing M.smoothDomain, field(a,f)(field(b,g)u)=field(b,g)(field(a,f)u). Domain membership on both sides is precisely the invariance witness extracted from original_smooth_fields for the corresponding charge and Test. The existing domainEquiv and evaluation identify the field products with the equal Smooth-family compositions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalweaksmearedlocality-original-smooth-fields-commute"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Analysis/OriginalWeakSmearedLocality.original_smooth_fields_commute"),
                H("Original charged weak smeared locality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every original positive lattice Model M, arbitrary charges a,b and genuine global smooth periodic Tests f,g with disjoint closed quotient-circle supports: every natural k has the bounded composition equality H_(r+s+k)->H_k; the existing Smooth endomorphism compositions are equal; and every u in the same smoothDomain has literal field-product equality. For every y in M.Hilbert the corresponding pairings with y are equal. For every v in that same smoothDomain, inner(opposite(a,f)v,field(b,g)u)=inner(opposite(b,g)v,field(a,f)u). The opposite identity uses the proved formal-adjoint direction and conjugate symmetry; opposite(a,f) remains the original eta(a)*field(-a,conjugate(f)). The original Model retains arbitrary finite rank, its positive real Gram matrix, complex inverse, both inverse equations, and original Carrier and Hm. Zero charges, rank zero, negative modes and N=0 are included. Strong closure commutation, adjoint equality and self-adjointness are outside this statement."))), DescribeRole.Theorem)),
        []));
}
