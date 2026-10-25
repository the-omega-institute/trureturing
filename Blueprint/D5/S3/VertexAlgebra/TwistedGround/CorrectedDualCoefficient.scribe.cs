using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;
internal sealed class CorrectedDualCoefficientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/CorrectedDualCoefficient.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Corrected Source with Two Twisted Inputs", H("Original Corrected Source with Two Twisted Inputs"), Blocks(
            Paragraph(Text("The original Carrier remains the source. For two actual twisted tensor inputs x,y, define K_L(e)(x,y)(a)=B((correctedField D hu a).coeff e x,y). This is a full algebraic dual coefficient, with the operator acting on the first input; no ground symmetry is used to identify it with a right orientation.")),
            Paragraph(Text("The existing corrected singleton coefficient proof in ChargedResidue.LatticeHalfFockChargedResidue and its addition and scalar laws are reused through their canonical public names in the original owner. Only their visibility changes; their statements and proof bodies are unchanged.")),
            Paragraph(Text("For every charge and each nonzero ground u, the charged adjoint consumer supplies an x with nonzero K_L(-N)(x,1 tensor u) on the original generator single a 1. The charged_ground_leading is an existing theorem, not a premise supplied by this module. This does not prove a full corrected-source adjoint, restricted-dual state, intertwining field, mixed Jacobi, fusion rule, Monster realization or complete string/AdS construction.")),
            Paragraph(Text("Information-escape registration remains unfinished: the faithful compiled Reg mirrors currently report declared_unresolved. The source-reconstruction diagnostics and missing binding certificates are recorded at https://github.com/the-omega-institute/trureturing/issues/21134 under the repository linked-issue exception. Compilation does not assert a validated registration.")),
            Describe.Lean(DescribeId.Create("corrected-dual-coefficient"),
                DeclarationHandle.Create(Prefix + "correctedDualCoefficient"),
                H("correctedDualCoefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The left-oriented full algebraic dual on the original Carrier, bilinear in two actual twisted inputs."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("corrected-dual-coefficient-nonzero-second-ground"),
                DeclarationHandle.Create(Prefix + "correctedDualCoefficient_nonzero_second_ground"),
                H("correctedDualCoefficient nonzero second ground"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A nonzero original-source generator coordinate exists at exponent -bilinear D a a for every charge and every nonzero actual ground second input. The proof consumes the native tensor adjoint chain and reuses the original singleton identification."))),
                DescribeRole.Theorem))));
}
