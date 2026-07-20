using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Scale;

internal sealed class FibonacciEigenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S1/Scale/FibonacciEigen",
            "The Fibonacci substitution has two golden eigenpairs and an exact contracting error."),
        H("Fibonacci Substitution Spectrum"),
        Blocks(
            new DocumentBlock.Describe(
                DescribeId.Create("golden-eigenpairs-and-contracting-error"),
                DescribeKind.Theorem,
                H("Golden eigenpairs and contracting error"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S1/Scale/FibonacciEigen.fibonacci_substitution_spec")),
                DescribeProvenance.LiteratureAttested(
                    LibraryNoteRef.Create("D5/L/koshy2001fibonacci")),
                Blocks(Paragraph(Text(
                    "The explicit substitution matrix has nonzero expanding and contracting eigenvectors, and the same theorem gives the exact signed Fibonacci error for every natural index."))),
                LatexStatement.Create(@"$$\forall n \in \mathbb{N},\ \operatorname{expandingEigenvector}\neq 0 \land \operatorname{fibonacciSubstitution}\operatorname{expandingEigenvector}=\varphi\operatorname{expandingEigenvector} \land \operatorname{contractingEigenvector}\neq 0 \land \operatorname{fibonacciSubstitution}\operatorname{contractingEigenvector}=\operatorname{contractingEigenvalue}\operatorname{contractingEigenvector} \land (F_{n}\varphi-F_{n+1})=-\operatorname{contractingEigenvalue}^{n}$$")))));
}
