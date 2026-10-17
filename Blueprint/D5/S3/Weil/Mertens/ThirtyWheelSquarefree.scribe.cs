using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class ThirtyWheelSquarefreeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal count and first-moment bounds for squarefree integers coprime to thirty.",
        H("Squarefree Integers in the Thirty-Wheel"),
        Blocks(
            Paragraph(Text(
                "For each natural X, good(X) is exactly the finite set of integers d in [7,X] "
                + "such that gcd(d,30)=1 and d is squarefree. Write K=Nat.sqrt(X), the integer "
                + "square root. All arithmetic in the following inequalities takes place in "
                + "the rationals; subtraction is signed, including at X=0.")),
            Describe.Lean(
                DescribeId.Create("thirty-wheel-squarefree-count-weight"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/ThirtyWheelSquarefree.count_weight_lower_bound"),
                H("Count and total weight at every cutoff"),
                StatementSource.FromAuthor(Claim()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let U(Y) count the positive integers at most Y coprime to thirty and "
                        + "let J(Y) be their sum. Write Y=30m+r with 0<=r<30, and let u(r),s(r) "
                        + "be the count and sum of the members of {1,7,11,13,17,19,23,29} at "
                        + "most r. Exact block summation gives U(Y)=8m+u(r) and "
                        + "J(Y)=120m^2+30m*u(r)+s(r). The thirty residue cases give "
                        + "-10<=15u(r)-4r<=14, 15s(r)-2r^2+10r>=0 and "
                        + "2r^2+16r-15s(r)>=0. Consequently "
                        + "(4Y-10)/15<=U(Y)<=(4Y+14)/15 and "
                        + "(2Y^2-10Y)/15<=J(Y)<=(2Y^2+16Y)/15.")),
                    Paragraph(Text(
                        "Every integer at least seven coprime to thirty has a representation "
                        + "b+30t with b in {7,11,13,17,19,23,29,31} and t natural. For a>0, "
                        + "1/(a+30)^2 <= 1/(30a)-1/(30(a+30)). Finite telescoping bounds "
                        + "each progression by 1/b^2+1/(b+30)^2+1/(30(b+30)). The sum of "
                        + "these eight rational quantities is strictly less than 1/18. "
                        + "Thus the finite sum of 1/k^2 over 7<=k<=K coprime to thirty is "
                        + "less than 1/18 for every K, including K=0.")),
                    Paragraph(Text(
                        "Mathlib's Nat.squarefree_iff_prime_squarefree supplies a prime-square "
                        + "divisor of each nonsquarefree positive integer d. If d is coprime "
                        + "to thirty, this prime is also coprime to thirty and is at least "
                        + "seven. Its square dividing d<=X implies that the prime is at most K. "
                        + "Enlarge the primes to all k in [7,K] coprime to thirty. The unit "
                        + "multiples of k^2 are exactly k^2*t for unit t<=X/(k^2). "
                        + "The same nonnegative finite union bound therefore bounds the "
                        + "discarded count B by the sum of U(X/(k^2)), and the discarded "
                        + "weight E by the sum of k^2*J(X/(k^2)). Natural quotients are used.")),
                    Paragraph(Text(
                        "For X>=1, the number of these k is U(K)-1<=(4K-1)/15. "
                        + "The wheel bounds, quotient inequalities and reciprocal telescope "
                        + "give B<=2X/135+56K/225-14/225 and "
                        + "E<=X^2/135+64XK/225-16X/225. Removing exactly the bad units "
                        + "and the unit 1 gives U(X)=1+card(good(X))+B and "
                        + "J(X)=1+sum(good(X))+E. Combining these identities proves both "
                        + "bounds. At X=0 the good set is empty and both rational lower "
                        + "bounds are negative. The empty index sets for K<7 and the first "
                        + "square divisor 49 require no additional premise.")),
                    Paragraph(Text(
                        "These finite arithmetic estimates do not construct Mobius octets or "
                        + "their bounded-variation consumer. They assert no global residual "
                        + "sign, signed MAIN, Robin inequality for every n>5040, or RH."))),
                DescribeRole.Theorem))));

    private static Formula Claim()
    {
        var x = F.Id("X");
        var k = Call("NatSqrt", x);
        var gx = Call("good", x);
        var count = Call("card", gx);
        var weight = Seq(F.Sum, Underscore,
            Grp(Seq(F.Id("d"), Sp, InMacro, Sp, gx)), Sp, F.Id("d"));
        var countLower = new Formula.Fraction(
            Subtract(Subtract(Multiply(Num(170), x), Multiply(Num(168), k)), Num(1083)), Num(675));
        var weightLower = new Formula.Fraction(
            Subtract(Subtract(Subtract(Multiply(Num(85), new Formula.Power(x, Num(2))),
                Multiply(Multiply(Num(192), x), k)), Multiply(Num(402), x)), Num(675)), Num(675));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("X"),
            new Formula.NamedConstant(FormulaIdentifier.Create("Nat")),
            new Formula.Logic(
                new Formula.Relation(countLower, FormulaRelationOperator.LessThanOrEqual, count),
                FormulaLogicOperator.And,
                new Formula.Relation(weightLower, FormulaRelationOperator.LessThanOrEqual, weight))));
    }
}
