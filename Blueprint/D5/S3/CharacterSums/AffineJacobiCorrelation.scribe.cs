using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class AffineJacobiCorrelationDocument : IScribeDocumentDefinition
{
    private static readonly Formula Naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete and incomplete correlations of two Jacobi symbols along an affine progression",
        H("Jacobi correlations along an affine progression"),
        Blocks(
            Paragraph(Text("For natural numbers b and m, let C(p,r,A,L) be the sum of (p/d)(r/d) over "
                + "d = b + m(A+i) with 0 ≤ i < L. Mathlib defines the Jacobi symbol at every natural denominator, "
                + "including even denominators and zero. At zero its value is one, so b = m = 0 gives C = L. "
                + "Under H(p,r) the denominators are positive and odd. In the formula, T = pr. The condition H(p,r) means "
                + "that b is 3 modulo 4, 4 divides m, and p and r are distinct odd primes, both coprime to m.")),
            Describe.Lean(DescribeId.Create("affine-jacobi-correlation"),
                DeclarationHandle.Create("D5/S3/CharacterSums/AffineJacobiCorrelation.affine_jacobi_correlation"),
                H("Cancellation on complete blocks of progression indices"),
                StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("All denominators d are 3 modulo 4 under H(p,r). Quadratic reciprocity "
                        + "turns the two factors into quadratic characters modulo p and r, each multiplied "
                        + "by a sign independent of the index.")),
                    Paragraph(Text("Addition of A, multiplication by the unit m, and addition of b all "
                        + "permute the residues modulo pr. The Chinese remainder theorem identifies these "
                        + "residues with pairs modulo p and r. Summing over the second coordinate gives zero "
                        + "because its quadratic character is nontrivial.")),
                    Paragraph(Text("Every complete block of pr consecutive indices therefore contributes zero. "
                        + "Each remaining summand has absolute value at most one. On the diagonal the "
                        + "summands are squares in {0,1} for every b and m."))), DescribeRole.Theorem))));

    private static Formula Claim()
    {
        var p = F.Id("p");
        var r = F.Id("r");
        var a = F.Id("A");
        var length = F.Id("L");
        var period = F.Id("T");
        var diag = Call("C", p, p, a, length);
        var diagonal = And(Le(F.D(0), diag), Le(diag, length));
        var full = new Formula.Relation(Call("C", p, r, a, period), FormulaRelationOperator.Equal, F.D(0));
        var tail = Le(Call("abs", Call("C", p, r, a, length)), Call("mod", length, period));
        var offDiagonal = new Formula.Logic(Call("H", p, r), FormulaLogicOperator.Implies, And(full, tail));
        return F.Disp(All("p", All("r", All("A", All("L", And(diagonal, offDiagonal))))));
    }

    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Naturals, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
}
