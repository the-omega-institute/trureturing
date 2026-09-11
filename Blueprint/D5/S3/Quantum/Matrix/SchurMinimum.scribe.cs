using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class SchurMinimumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Schur quadratic form is the attained minimum over the internal block.",
        H("Attained Schur Minimum"),
        Blocks(Describe.Lean(
            DescribeId.Create("schur-quadratic-minimum"),
            DeclarationHandle.Create("D5/S3/Quantum/Matrix/SchurMinimum.schur_quadratic_is_least"),
            H("Boundary quadratic minimum"),
            StatementSource.FromAuthor(MinimumFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For a finite Hermitian block matrix with positive definite internal block C, "
                + "the set of energies at a fixed boundary vector has the stated least element. "
                + "It is attained at the negative inverse-block response. The proof applies "
                + "Mathlib's Schur decomposition and positive-semidefinite quadratic inequality. "
                + "This is a repository API wrapper of those upstream results."))),
            DescribeRole.Theorem))));

    private static Formula MinimumFormula()
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula a = F.Id("A");
        Formula b = F.Id("B");
        Formula c = F.Id("C");
        Formula adjointB = Seq(b, Caret, Grp(Star));
        Formula schur = Seq(Open, a, Minus, b,
            Seq(c, Caret, Grp(Minus, D(1))), adjointB, Close);
        Formula pair = Seq(Begin, Grp(F.Id("pmatrix")), x, RowBreak, y,
            End, Grp(F.Id("pmatrix")));
        Formula block = Seq(Begin, Grp(F.Id("pmatrix")), a, Amp, b, RowBreak,
            adjointB, Amp, c, End, Grp(F.Id("pmatrix")));
        Formula energy = Seq(pair, Caret, Grp(Star), block, pair);
        Formula minimum = Seq(x, Caret, Grp(Star), schur, x);
        return Disp(Seq(Operatorname, Grp(F.Id("IsLeast")), Open,
            OpenBrace, energy, Sp, Mid, Sp, y, Sp, InMacro, Sp,
            Seq(Mathbb, Grp(F.Id("C")), Caret, Grp(F.Id("n"))),
            CloseBrace, Comma, Sp, minimum, Close));
    }
}
