using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class PositiveGraftShortWordsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/PositiveGraftShortWords.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative Fibonacci coefficients give short forward graft words.",
        H("Positive Fibonacci Graft Words"),
        Blocks(
            Definition("offset", "A positive representative",
                "offset(H,c) is zero for c=0, H+1 for c=1, and c otherwise."),
            Definition("horizon", "The common step horizon",
                "horizon(H) is the least k>=1 with H<=F(k+4)."),
            Definition("graftBound", "The graft budget",
                "graftBound(K)=1+(K+2)/2, using natural-number division."),
            Definition("graftCoefficients", "Eliminating the auxiliary unit weight",
                "For occupied indices s, write epsilon(i)=1 if i belongs to s and zero otherwise. "
                + "The coefficients are d(0)=epsilon(3)+1-epsilon(2), "
                + "d(1)=epsilon(4)+epsilon(2), and d(j)=epsilon(j+3) for j>=2."),
            Definition("blockWord", "A chronological block word",
                "blockWord(d,0) consists of d(0) true letters. "
                + "blockWord(d,k+1) prepends d(k+1) true letters and one false letter "
                + "to blockWord(d,k). True grafts (1,0); false applies the Fibonacci step."))));

    private static DocumentBlock Definition(string selector, string title, string prose) =>
        Describe.Lean(DescribeId.Create("positive-graft-" + selector.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
