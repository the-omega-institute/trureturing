using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class PolynomialSignatureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite polynomial-sign formulas characterize actual symmetric matrix signatures.",
        H("Polynomial Sign Formulas for Matrix Signatures"),
        Blocks(Describe.Lean(
            DescribeId.Create("polynomial-matrix-signature-compiler"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/PolynomialSignature.compile_iff_signature"),
            H("Exact signature compiler"),
            StatementSource.FromAuthor(Disp(Seq(
                F.Id("holds"), Open, F.Id("x"), Comma,
                F.Id("compile"), Open, F.Id("n"), Comma, F.Id("A"), Comma, F.Id("z"), Close, Close,
                Sp, Iff, Sp,
                F.Id("sigPos"), Open, F.Id("Q"), Close, Minus,
                F.Id("sigNeg"), Open, F.Id("Q"), Close, Eq, F.Id("z")))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let sigma be any type of variables, n any natural dimension, A an n by n matrix of multivariate polynomials over the reals in those variables, z any integer, and x any real assignment to sigma. Assume only that the evaluated matrix A(x) is symmetric at this same x. Then holds(x,compile(n,A,z)) is equivalent to the actual signature of Q(v) = sum over i,j of v(i) A(x)(i,j) v(j) being z. The signature is its positive index minus its negative index.")),
                Paragraph(Text("A formula is a finite list of clauses, and a clause is a finite list of pairs consisting of a polynomial and a negative, zero, or positive sign. A formula holds when some clause has every sign condition satisfied at x. Empty disjunctions are false and empty conjunctions are true. All polynomials remain in the original sigma coordinates; no auxiliary real variables or semantic decision oracle occur.")),
                Paragraph(Text("At dimension zero the formula tests z = 0. At positive dimension one branch checks that every entry is zero and z = 0. A positive or negative diagonal entry selects a one-coordinate polynomial residual and shifts z by minus or plus one. When all diagonal entries vanish, a nonzero off-diagonal entry selects a two-coordinate residual without shifting z. Finite conjunction and disjunction distribute these branches into the output formula.")),
                Paragraph(Text("Polynomial evaluation commutes with both residual constructions. Two-step induction on dimension therefore identifies the formula with the recursive pivot relation. The characterization of that relation by the actual quadratic-form signature proves the equivalence. Every pivot condition is checked at the same assignment as its residual.")),
                Paragraph(Text("No nonsingularity, fixed rank, fixed degree, global polynomial symmetry, or nonvanishing pivot is assumed. Singular matrices, zero diagonals with nonzero off-diagonal entries, and every rank or degree drop under specialization are included. The construction gives finite mathematical syntax and its meaning; it makes no complexity claim or executable decision procedure for arbitrary real inputs."))),
            DescribeRole.Theorem))));
}
