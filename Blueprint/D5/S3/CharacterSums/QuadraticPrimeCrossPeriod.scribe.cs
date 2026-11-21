using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class QuadraticPrimeCrossPeriodDocument : IScribeDocumentDefinition
{
    private static readonly Formula Naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic prime correlations on intervals in the class three modulo eight",
        H("Cancellation of products of two Jacobi symbols"),
        Blocks(
            Paragraph(Text("Let C(p,r,A,L) be the sum of the products (p/n)(r/n) of Jacobi symbols "
                + "over the integers A ≤ n < A + L with n congruent to 3 modulo 8. "
                + "In the formula T denotes 8pr, and distinctOddPrimes(p,r) means that p and r are distinct odd primes.")),
            Describe.Lean(DescribeId.Create("prime-cross-period"),
                DeclarationHandle.Create("D5/S3/CharacterSums/QuadraticPrimeCrossPeriod.quadratic_prime_cross_period"),
                H("Complete-period cancellation and the interval remainder"),
                StatementSource.FromAuthor(Claim()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("On the selected residue class n is 3 modulo 4. Quadratic reciprocity "
                        + "therefore turns (p/n) and (r/n) into quadratic characters modulo p and r, "
                        + "with a sign that is fixed for each prime.")),
                    Paragraph(Text("For distinct odd primes, the Chinese remainder theorem splits residues modulo 8pr "
                        + "into independent residues modulo 8, p and r. Any interval of length 8pr runs through "
                        + "all these residues. After fixing the first two coordinates, summing the nontrivial "
                        + "quadratic character over the field with r elements gives zero.")),
                    Paragraph(Text("Delete complete periods from the interval. Each remaining product has absolute "
                        + "value at most one, so the remainder length bounds its sum. When the two arguments coincide, "
                        + "each retained summand is a square equal to zero or one."))), DescribeRole.Theorem))));

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
        var offDiagonal = new Formula.Logic(Call("distinctOddPrimes", p, r), FormulaLogicOperator.Implies, And(full, tail));
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
