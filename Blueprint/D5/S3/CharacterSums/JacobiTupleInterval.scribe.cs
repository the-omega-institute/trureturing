using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class JacobiTupleIntervalDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/CharacterSums/JacobiTupleInterval.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Incomplete tuple averages and complete power moments for Jacobi symbols",
        H("Jacobi products on an affine progression"),
        Blocks(
            Paragraph(Text("Fix a finite set P of odd primes and let Q be their product. Fix natural b and m "
                + "with b congruent to 3 modulo 4 and m divisible by 4. For every index i let d(i) = b + mi. "
                + "All sums over interval indices start at a natural A and have a natural length L.")),
            Describe.Lean(DescribeId.Create("tuple-discrepancy"), DeclarationHandle.Create(Module + "tuple_interval_mean"),
                H("Discrepancy for tuples with repeated primes"),
                StatementSource.FromAuthor(Compare(Call("abs", F.Seq(Call("S", F.Id("A"), F.Id("L")), F.Minus,
                    F.Id("L"), F.Sp, F.Id("M"))), FormulaRelationOperator.LessThanOrEqual, F.Seq(F.D(2), F.Sp, F.Id("U")))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For a tuple f of any natural length with entries in P, take the product of "
                        + "the Jacobi symbols (f(j)/d(i)) at each index i. S(A,L) sums those products over A ≤ i < A+L, "
                        + "M = S(0,Q)/Q is the complete average, and U is the product of the entries with multiplicity.")),
                    Paragraph(Text("Let R be the product of the distinct entries of the tuple. Reciprocity shows that "
                        + "R is a period, also when a prime divides the stride. Since R divides Q, both complete "
                        + "averages coincide. Removing complete blocks from the interval leaves two terms, each bounded "
                        + "in absolute value by L modulo R. The product R is at most U."))), DescribeRole.Theorem),
            Paragraph(Text("For the power-moment identity also assume that m is coprime to every prime in P. "
                + "Choose arbitrary real coefficients a(p) and a natural exponent e. For p in P write χ(p,z) "
                + "for the quadratic character of the field modulo p, multiplied by −1 if p is 3 modulo 4 "
                + "and by 1 otherwise.")),
            Describe.Lean(DescribeId.Create("complete-power-moment"), DeclarationHandle.Create(Module + "affine_complete_crt"),
                H("Complete power moments over independent residue coordinates"),
                StatementSource.FromAuthor(Compare(Call("B", F.Id("A"), F.Id("e")),
                    FormulaRelationOperator.Equal, Call("G",F.Id("e")))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("B(A,e) sums the e-th power of the weighted sum of (p/d(i)) over a block of Q indices "
                        + "beginning at A. G(e) sums the e-th power of the weighted sum of χ(p,z(p)) over all tuples "
                        + "of residue coordinates z, with one independent field coordinate modulo each prime p.")),
                    Paragraph(Text("The affine map sending an index to its denominator permutes residues modulo Q. "
                        + "The Chinese remainder theorem transports this permutation to the product of the prime fields. "
                        + "Reciprocity identifies each summand after that change of variables."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed-character-law"), DeclarationHandle.Create(Module + "coordinate_laws"),
                H("Values and mean of one signed coordinate"),
                StatementSource.FromAuthor(F.Disp(new Formula.Logic(
                    new Formula.Relation(Call("range",F.Id("c")), FormulaRelationOperator.SubsetOf,
                        F.Seq(F.OpenBrace,F.Minus,F.D(1),F.Comma,F.D(0),F.Comma,F.D(1),F.CloseBrace)),
                    FormulaLogicOperator.And, new Formula.Relation(Call("sum",F.Id("c")),FormulaRelationOperator.Equal,F.D(0))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Here c denotes the signed character for the fixed odd prime p. The range and sum are taken over its entire field. "
                        + "The Jacobi symbol takes values −1, 0, 1. The quadratic character on an odd prime field "
                        + "has zero sum, and multiplication by its fixed reciprocity sign preserves both properties."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Compare(Formula left, FormulaRelationOperator op, Formula right) =>
        F.Disp(new Formula.Relation(left, op, right));
}
