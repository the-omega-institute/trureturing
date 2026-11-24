using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMVLargeDegreeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/RefinedBMVLargeDegree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The refined BMV lower bounds with three copies of the second factor",
        H("The refined BMV lower bounds with three copies of the second factor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-large-degree-product"),
                DeclarationHandle.Create(Module + "product_bound_all"),
                H("Product trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural number p at least three, the mean trace of the words with p copies of A and " +
                    "three of B is at least the trace of the cube of A^(p/3) B. The complex PSD factors may be singular " +
                    "and have arbitrary spectra in any finite dimension. Hägele's Lemma 3 and Sections 3 and 4 supply " +
                    "the composition average and cubic walk expansion. The degrees from three to ten use the proved finite cases. " +
                    "For larger degrees, the proof assembles the strict mixed derivative sign of the " +
                    "original logarithmic kernel from the left and right strips and the three central gap ranges. " +
                    "The two endpoint limits complete the rectangle inequalities for the finite interval Gram decomposition. " +
                    "Continuity of the unnormalized sample matrices covers zero centers. The centered walks and the Schur product theorem " +
                    "then give the product bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-large-degree-exponential"),
                DeclarationHandle.Create(Module + "exponential_bound_all"),
                H("Exponential trace comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For Hermitian H and K and every natural number p at least three, the word mean at exp H and " +
                    "exp K is at least the trace of exp(pH + 3K). The dyadic trace-power comparison in Hägele's Lemma 2 " +
                    "relates the product and exponential inequalities."))),
                DescribeRole.Theorem))));
}
