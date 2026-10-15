using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeOppositeDerivativeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite opposite coefficients satisfy the actual state-translation derivative identity.",
        H("Translation of Actual Opposite Coefficients"),
        Blocks(
            Paragraph(Text("D is unrestricted integral even lattice data. H satisfies both inverse-Gram equations. "
                + "The state a has actual integer grade h, which need not be nonnegative. Translation is the original operator T=L(-1). "
                + "Every sum uses the actual L1 iterates and the native finite oscillator bound; no opposite family is treated as a native creative field.")),
            Describe.Lean(DescribeId.Create("actual-one-pow-translation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeOppositeDerivative.one_pow_translation_succ"),
                H("Exact powers on a translated homogeneous state"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("L1^(j+1)(T a)=T L1^(j+1)a+(j+1)(2h-j)L1^j a. "
                    + "The actual Virasoro commutator [L1,T]=2L0 and the actual grade h-j give the recurrence. "
                    + "Complex and integer differences retain their signs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-opposite-translation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeOppositeDerivative.opposite_translation"),
                H("Actual opposite derivative coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("O_(T a)(n)=-n O_a(n-1), where T a is assigned grade h+1. "
                    + "A single finite cutoff covers a and T a. The true state derivative law is applied to every actual descendant, "
                    + "then the factorial-normalized successor terms are reindexed. The last descendant term vanishes by actual local nilpotence. "
                    + "This identity is the derivative interface for every negative-current opposite insertion."))), DescribeRole.Theorem))));
}
