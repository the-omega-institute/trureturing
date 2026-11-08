using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class SingularSchurResidualRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Completion/SingularSchurResidualRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The singular block with zero old corner and unit cross entry has a nonnegative naive residual but is not positive semidefinite.",
        H("Singular Schur residual is insufficient"),
        Blocks(
            Paragraph(Text(
                "Indices are Fin 2 and scalars are complex. The matrix bad is the explicit block "
                    + "[[0,1],[1,1]], and witness is the vector (1,-1). Matrix.PosSemidef requires "
                    + "every complex quadratic form to have nonnegative real part.")),
            Describe.Lean(
                DescribeId.Create("bad"), DeclarationHandle.Create(Prefix + "bad"),
                H("The singular two by two block"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The old corner is the zero 1 by 1 block, the cross entry is one, and the new "
                        + "diagonal entry is one. It is the concrete boundary matrix from the C129 "
                        + "Schur-complement warning."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Positive semidefiniteness of the displayed block"),
                StatementSource.FromAuthor(Disp(At(Qualified("Matrix", "PosSemidef"), F.Id("bad")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is exactly the tempting conclusion obtained by retaining only the scalar "
                        + "residual q minus b star G pseudoinverse b; the range condition is omitted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The singular block is not positive semidefinite"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(F.Id("claim"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The vector (1,-1) has quadratic value -1 for bad. The kernel positivity "
                        + "obligation would therefore imply 0 <= -1, which is impossible. "
                        + "This records why the range condition b in Ran G must accompany the "
                        + "nonnegative Schur residual at singular boundaries."))),
                DescribeRole.Theorem))));

    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula At(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
