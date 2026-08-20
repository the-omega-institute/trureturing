using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class CompleteContextTomographyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete complementary context family spans every traceless Hermitian matrix.",
        H("Complete Context Tomography"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-context-tomography"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/CompleteContextTomography."
                        + "complete_context_tomography"),
                H("Complete context tomography"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A context family consists of d+1 canonical normalized rank-one "
                            + "projective contexts in dimension d. Its public overlap law says "
                            + "that projectors in one context have Kronecker trace overlap, while "
                            + "projectors in distinct contexts have constant inverse-dimension "
                            + "overlap.")),
                    Paragraph(Text(
                        "The identity and all projector differences form a basis of the full "
                            + "complex matrix space. The proof derives independence from the "
                            + "overlap law, counts the vectors against the matrix finrank, and "
                            + "then specializes the resulting coordinates to real centered "
                            + "coefficients for Hermitian traceless matrices.")),
                    Paragraph(Text(
                        "The displayed theorem keeps all three source consequences public: "
                            + "unique centered diagonal decomposition, zero common invisible "
                            + "traceless residual, and uniqueness of a matrix from every context "
                            + "probability. No completeness or reconstruction property is assumed "
                            + "as a hidden premise."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula TheoremFormula()
    {
        Formula family = Apply("ContextFamily", F.Id("C"), F.Id("d"));
        Formula overlap = Apply("ComplementaryOverlap", F.Id("C"), F.Id("d"));
        Formula centered = Apply("UniqueCenteredDiagonalDecomposition", F.Id("C"), F.Id("d"));
        Formula residual = Apply("ZeroInvisibleTracelessResidual", F.Id("C"), F.Id("d"));
        Formula probabilities = Apply("ProbabilityUniqueness", F.Id("C"), F.Id("d"));
        return Disp(Seq(
            family, Sp, Land, Sp, overlap, Sp, Rightarrow, RowBreak,
            centered, Sp, Land, Sp, RowBreak,
            residual, Sp, Land, Sp, RowBreak,
            probabilities, Dot));
    }
}
