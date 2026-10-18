using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.CriticalPoints;

internal sealed class TangZhangConstantRootsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/CriticalPoints/TangZhangConstantRoots.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coincident nonzero polynomial roots attain the Tang–Zhang real-order coefficient.",
        H("The constant-root equality direction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tang-zhang-constant-root-moment"),
                DeclarationHandle.Create(Prefix + "constant_roots_moment"),
                H("The exact constant-root moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every n≥1, nonzero complex a and real p, the sum of norm(w)^(−p) over roots of the derivative of P(Z)=Z(Z−a)^n equals c(n,p) times the sum of norm(a)^(−p) over Fin n, where c(n,p)=((n+1)^p+n−1)/n. The derivative has the root a with multiplicity n−1 and the root a/(n+1), including the case n=1."))),
                DescribeRole.Theorem))));
}
