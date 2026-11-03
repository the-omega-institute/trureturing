using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalFourMReductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original lattice twisted-sector coefficient reduction, preserving the original carriers and operators.",
        H("OriginalFourMReduction"),
        Blocks(
            Paragraph(Text("Audit remains incomplete for the 24 new public theorems in OriginalFourMInputs, OriginalFourMCoefficients, OriginalFourMChargeCoset and OriginalFourMReduction: declared_validated=0, with no new Reg mirrors or faithful four-slot attempts supplied. Source-owner disposition https://github.com/the-omega-institute/trureturing/issues/25603 lists every exact source, statement and type identity, the absent dependent-family realization/readout bridge and whole-family intervention/sensitivity evidence. This linked-issue exception permits delivery under CLAUDE 3.9 and supplies no validation. Universal identityK remains unproved.")),
            Describe.Lean(DescribeId.Create("originalfourmreduction-homogeneous-jacobi-iff-identityk"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalFourMReduction.homogeneous_jacobi_iff_identityK"),
                H("Quantified original tensor reduction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For any three compatible original homogeneous odd polynomials and all integer m,n,r, quantify the original vector Jacobi law over every actual ground x,y,z. Quantify the detector polynomial S before applying coset_ground_elimination to all four ground variables, including its ground detector. This is equivalent to identityK for every S, with no permanent output-weight premise."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalfourmreduction-original-jacobi-iff-identityk"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalFourMReduction.original_jacobi_iff_identityK"),
                H("All-state original Jacobi if and only if the explicit coset law"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The vector side quantifies every u,v,w in the full original paritySpace(-1). The explicit K side quantifies natural weights H,K,L, all compatible original homogeneous odd P,Q,R, every detector polynomial S and, inside identityK, every mod-two charge. All m,n,r are arbitrary integers. The original three j families are statewise finite; their product and balance form a trilinear residual. Accepted finite input expansion, not detector induction or a vacuum argument, extends the law to every input. This is a reduction only: universal K, crossing, Monster/moonshine, full VOA/CFT, BRST/string and AdS/CFT remain unproved."))
                ), DescribeRole.Theorem)
        ), []));
}
