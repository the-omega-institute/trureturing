using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KarpZhangReciprocal;

internal sealed class CoeffDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/karpzhang2023pochhammer");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scores and curvature of reciprocal Pochhammer coefficients.",
        H("Coefficient calculus"), Blocks(
            Entry("karp-zhang-reciprocal-coefficient", "c", "Reciprocal coefficients",
                "For every natural n and real t, c(n,t) is the evaluation of ascPochhammer at 2t divided by the product of its evaluation at t and n factorial. For t positive this is the coefficient (2t)n/((t)n n!) in the reciprocal series of Conjecture 5.2, page 12.", DescribeRole.Definition),
            Entry("karp-zhang-reciprocal-ratio", "lambda", "Adjacent degree ratio",
                "For every natural j and real t, lambda(j,t) equals (2t+j)/(t+j).", DescribeRole.Definition),
            Entry("karp-zhang-reciprocal-score-increment", "eta", "Score increment",
                "For every natural j and real t, eta(j,t) equals j/((2t+j)(t+j)). In particular the increment at j=0 is zero.", DescribeRole.Definition),
            Entry("karp-zhang-reciprocal-score", "psi", "Finite score sum",
                "For every natural n and real t, psi(n,t) is the sum of eta(j,t) over 0 <= j < n. The zero index contributes zero, so this equals the sum over 1 <= j < n.", DescribeRole.Definition),
            Entry("karp-zhang-reciprocal-curvature", "chi", "Finite curvature sum",
                "For every natural n and real t, chi(n,t) is the sum over 0 <= j < n of j(4t+3j)/((2t+j)^2(t+j)^2).", DescribeRole.Definition),
            Entry("karp-zhang-reciprocal-coefficient-calculus", "coefficient_calculus", "Uniform score and curvature estimates",
                "For every natural n and positive real t, c(n,t) and lambda(n,t) are positive; c(n+1,t)/c(n,t) equals lambda(n,t)/(n+1); the derivative of c(n,t) is c(n,t)psi(n,t), the derivative of log(c(n,t)) is psi(n,t), and the derivative of psi(n,t) is -chi(n,t). Curvature is nonnegative and at least n times eta(n-1,t) squared. The function j -> lambda(j,t) is antitone. Natural subtraction makes the n=0 curvature estimate meaningful, with both sides zero.", DescribeRole.Theorem)),
        H("The curvature comparison"), Blocks(Paragraph(Text(
            "At each j <= N, compare the positive denominator (2t+j)^2(t+j)^2 with the terminal denominator (2t+N)^2(t+N)^2. Retaining 3j squared from the numerator and summing gives chi(N+1,t) at least (N+1)N squared divided by the terminal denominator. This is the estimate controlling adjacent score differences in the convolution Hessian.")))));

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KarpZhangReciprocal/Coeff." + name),
            H(title), StatementSource.WithoutFormula(),
            name == "c" ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
