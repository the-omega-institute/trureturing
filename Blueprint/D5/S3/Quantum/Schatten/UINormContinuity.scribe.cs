using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Schatten;

internal sealed class UINormContinuityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Schatten/UINormContinuity";
    private static LibraryNoteRef Background => LibraryNoteRef.Create("D5/L/Eigenstructure/bhatia1997matrixanalysis");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuity and balanced scalar optimization.",
        H("Continuity and balanced scalar optimization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zhangli-uinormcontinuity-continuous-n"),
                DeclarationHandle.Create(Module + ".continuous_N"),
                H("Continuity of a matrix norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Background),
                Blocks(Paragraph(Text("Every UINorm on complex n by n matrices is continuous in the usual finite-dimensional topology. Subadditivity and absolute homogeneity give convexity, and an everywhere finite convex function on this finite-dimensional real vector space is continuous."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zhangli-uinormcontinuity-sq-le-mul-of-balanced-bounds"),
                DeclarationHandle.Create(Module + ".sq_le_mul_of_balanced_bounds"),
                H("Optimization over a positive scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonnegative real m, f and g, if 2m≤tf+t⁻¹g for every positive real t, then m²≤fg. When m and f are positive, t=m/f suffices; if f=0, a positive scale rules out m>0. Thus the conclusion also includes vanishing factors."))),
                DescribeRole.Theorem))));
}
