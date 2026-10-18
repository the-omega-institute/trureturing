using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.CriticalPoints;

internal sealed class SchurFrobeniusInequalityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Zeros/CriticalPoints/SchurFrobeniusInequality";
    private static Formula Pow(Formula value) => new Formula.Power(value, D(2));
    private static Formula EigenSum => Seq(Sum, Underscore, Grp(F.Id("k")), Sp,
        Pow(new Formula.Absolute(Seq(Mu, Underscore, Grp(F.Id("k"))))));
    private static Formula FrobeniusSum => Seq(Sum, Underscore, Grp(F.Id("i")), Sp,
        Sum, Underscore, Grp(F.Id("j")), Sp,
        Pow(new Formula.Absolute(Seq(F.Id("A"), Underscore, Grp(F.Id("ij"))))));
    private static Formula Adjoint => new Formula.Power(F.Id("A"), Star);
    private static Formula Statement => Seq(
        EigenSum, Leq, Sp, FrobeniusSum, Comma, Sp,
        Open, EigenSum, Eq, FrobeniusSum, Close, Sp, Iff, Sp,
        F.Id("A"), Adjoint, Eq, Adjoint, F.Id("A"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The squared moduli of a complex matrix's eigenvalues sum to at most its "
        + "squared Frobenius norm, with equality exactly for normal matrices.",
        H("Schur–Frobenius inequality and equality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("schur-frobenius-normality"),
                DeclarationHandle.Create(Module + ".schur_frobenius"),
                H("Eigenvalue energy and matrix energy"),
                StatementSource.FromAuthor(Disp(Statement)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural n and every complex n by n matrix A, let the "
                        + "mu values be the roots of its characteristic polynomial, counted "
                        + "with multiplicity. Their squared absolute values sum to at most "
                        + "the sum of squared absolute values of all matrix entries. "
                        + "Equality holds if and only if A commutes with its conjugate transpose. "
                        + "The statement includes dimension zero.")),
                    Paragraph(Text(
                        "Unitary triangularization preserves the characteristic polynomial "
                        + "and Frobenius norm. The diagonal contributes the eigenvalue sum; "
                        + "the remaining squares are nonnegative. Equality forces every "
                        + "off-diagonal entry to vanish. A normal triangular matrix is diagonal, "
                        + "giving the converse. This is a formal proof of the classical matrix inequality."))),
                DescribeRole.Theorem))));
}
