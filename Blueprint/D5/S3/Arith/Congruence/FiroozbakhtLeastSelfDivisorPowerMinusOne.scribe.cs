using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class FiroozbakhtLeastSelfDivisorPowerMinusOneDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/firoozbakht2004a092028");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least self-divisor exponent in OEIS A092028 is the least prime factor of n minus one.",
        H("The Least Self-Divisor Exponent"),
        Blocks(
            Node("a", "The A092028 sequence", DefinitionFormula(),
                "In the natural numbers, `sInf` selects the least element of the set, and `sInf` "
                + "of the empty set is zero. For n greater "
                + "than two, the defining set is nonempty. Every subtraction in the formula "
                + "is truncated natural-number subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("firoozbakht_a092028", "Firoozbakht's second conjecture", TheoremFormula(),
                "The upper bound uses p=minFac(n-1), since p divides n-1 and therefore p divides "
                + "n^p-1. For the lower bound, take q=minFac(m). The multiplicative order of n "
                + "modulo q divides both m and q-1; minimality of q makes those integers coprime, "
                + "so the order is one and q divides n-1. Firoozbakht's first conjecture follows "
                + "because minFac(n-1) is prime when n is greater than two.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a092028-least-self-divisor-power-minus-one"),
                    ResolutionKind.Proved)),
            Paragraph(Text("Application: Harvey P. Dale's A014865 recurrence. Let t be any "
                + "integer-valued sequence with t(1)=1 and, for every integer j at least two, "
                + "t(j)=15t(j-1)+j. Its values at nonpositive indices are unrestricted. "
                + "Define the natural-valued sequence s by the following recurrence.")),
            Paragraph(Math(DaleRecurrenceFormula())),
            Paragraph(Text("For every positive natural k, induction using the original recurrence "
                + "at j=k+1 gives t(k)=s(k), with the natural value cast to the integers. "
                + "Every positive integer n is the cast of the positive natural k=n.toNat. "
                + "Consequently n divides t(n) in the integers exactly when k divides s(k) "
                + "in the naturals; this is the natural-cast divisibility equivalence "
                + "Int.natCast_dvd_natCast. Thus the encoding includes every original positive "
                + "index, and places no extra condition on that index. At index one, s(1)=1, "
                + "so the qualifying class is nonempty.")),
            Paragraph(Text("The order-one recurrence with coefficient 15 has a unique solution "
                + "for a fixed initial value, by LinearRecurrence.eq_iff_eqOn_range_order. "
                + "The sequences 196s(k)+14k+15 and 15^(k+1) both satisfy it and both start "
                + "at 15. Hence the following identity holds even at k=0.")),
            Paragraph(Math(DaleClosedFormFormula())),
            Paragraph(Text("For a positive qualifying k, choose q in the naturals with s(k)=kq. "
                + "Rearranging the identity gives the next equation and therefore "
                + "k divides 15(15^k-1). In the original integer notation the closed form is "
                + "196t(n)=15^(n+1)-14n-15 for every positive n.")),
            Paragraph(Math(DaleIdentityFormula())),
            Paragraph(Text("Oddness follows from the existing two-adic LTE theorem "
                + "padicValNat.pow_two_sub_one at x=15 and an even positive exponent k. "
                + "Its hypotheses hold: 1<15, two does not divide 15, k is nonzero, and k "
                + "is even in the contradiction case. The theorem gives "
                + "v2(15^k-1)+1=v2(16)+v2(14)+v2(k)=5+v2(k). "
                + "The power difference is positive because k>0; 1+14q is positive and odd. "
                + "Thus all factors used with padicValNat.mul are nonzero. The displayed "
                + "identity would equate valuations v2(k)+4 and v2(k)+1, a contradiction. "
                + "This proves oddness rather than assuming it.")),
            Paragraph(Text("For k>1, if neither three nor five divides k, then gcd(k,15)=1. "
                + "Cancellation yields k divides 15^k-1. Put p=minFac(k), a prime divisor "
                + "of k. In ZMod p the residue of 15 has kth power one and is nonzero. "
                + "By orderOf_dvd_of_pow_eq_one and ZMod.orderOf_dvd_card_sub_one its order "
                + "d divides both k and p-1. Nat.coprime_of_lt_minFac gives gcd(k,p-1)=1, "
                + "so d=1. Then orderOf_eq_one_iff and the natural-cast congruence bridge "
                + "give p divides 14. Oddness excludes p=2, hence p=7 and seven divides k. "
                + "The other branches give divisibility by three or five directly; the "
                + "disjunction is inclusive.")),
            Paragraph(Text("This order argument is the local divisibility step in "
                + "minFac_sub_one_le_of_dvd_pow_sub_one. That private declaration concludes "
                + "only minFac(N-1) <= m; neither that bound nor the public A092028 equality "
                + "alone states minFac(m) divides N-1. The application above uses the "
                + "finite-field order argument itself, with N=15 and m=k, and the named "
                + "Mathlib order and coprimality facts. The same argument appears in the "
                + "solution to Problem 3 of Parvardi's Lifting The Exponent Lemma, version 6; "
                + "its Theorem 4 in section 4 (page 4) gives the two-adic identity used above, "
                + "and the solution to Problem 3 is in section 6 (page 7): "
                + "https://s3.amazonaws.com/aops-cdn.artofproblemsolving.com/resources/articles/lifting-the-exponent.pdf.")),
            Paragraph(Text("If a qualifying k>7 were prime, every divisor three, five or seven "
                + "supplied by the alternative would have to equal k. Each equality contradicts "
                + "k>7. Thus k>1 and k is not prime, the usual composite condition. "
                + "Transporting the three conclusions along the positive-index correspondence "
                + "gives the following statement for the original sequence t.")),
            Paragraph(Math(DaleSourceClausesFormula())),
            Paragraph(Text("Here Prime(toNat(n)) is primality of the positive natural represented "
                + "by n. The hypotheses on t are exactly its initial value and recurrence "
                + "above, and all divisibilities in this last formula are integer divisibilities. "
                + "No conclusion is asserted for indices outside the qualifying class. "
                + "The recurrence and thresholds are those of OEIS A014865, revision 18, "
                + "whose entry authors are N. J. A. Sloane and Olivier Gérard and whose "
                + "conjectural clauses are attributed to Harvey P. Dale: "
                + "https://oeis.org/A014865/internal. "
                + "These are applications of recurrence uniqueness, LTE and finite-field "
                + "order facts; they imply no claim about the current literature status "
                + "or originality of the historical clauses.")))));

    private static Formula DaleRecurrenceFormula()
    {
        var k = F.Id("k");
        var next = Add(k, Num(1));
        return Disp(And(Equal(Call("s", Num(0)), Num(0)),
            Universal("k", Equal(Call("s", next),
                Add(Multiply(Num(15), Call("s", k)), next)))));
    }

    private static Formula DaleClosedFormFormula()
    {
        var k = F.Id("k");
        return Disp(Universal("k", Equal(
            Add(Add(Multiply(Num(196), Call("s", k)), Multiply(Num(14), k)), Num(15)),
            Power(Num(15), Add(k, Num(1))))));
    }

    private static Formula DaleIdentityFormula()
    {
        var k = F.Id("k");
        var q = F.Id("q");
        return Disp(Universal("k", Universal("q", Imply(
            And(Relation(Num(0), FormulaRelationOperator.LessThan, k),
                Equal(Call("s", k), Multiply(k, q))),
            Equal(Multiply(Num(15), Parenthesized(Subtract(Power(Num(15), k), Num(1)))),
                Multiply(Multiply(Num(14), k),
                    Parenthesized(Add(Num(1), Multiply(Num(14), q)))))))));
    }

    private static Formula DaleSourceClausesFormula()
    {
        var n = F.Id("n");
        var qualifies = And(Relation(Num(0), FormulaRelationOperator.LessThan, n),
            Relation(n, FormulaRelationOperator.Divides, Call("t", n)));
        var composite = Imply(Relation(Num(7), FormulaRelationOperator.LessThan, n),
            And(Relation(Num(1), FormulaRelationOperator.LessThan, n),
                Seq(Neg, Sp, Call("Prime", Call("toNat", n)))));
        var alternative = Imply(Relation(Num(1), FormulaRelationOperator.LessThan, n),
            Or(Relation(Num(3), FormulaRelationOperator.Divides, n),
                Or(Relation(Num(5), FormulaRelationOperator.Divides, n),
                    Relation(Num(7), FormulaRelationOperator.Divides, n))));
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"),
            new Formula.Integers(), Imply(qualifies,
                And(Call("Odd", n), And(composite, alternative)))));
    }

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imply(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a092028-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula DefinitionFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var greaterThanOne = Relation(D(1), FormulaRelationOperator.LessThan, m);
        var divides = Relation(m, FormulaRelationOperator.Divides,
            Subtract(Power(n, m), D(1)));
        var conditions = new Formula.Logic(
            Parenthesized(greaterThanOne), FormulaLogicOperator.And, Parenthesized(divides));
        var witnesses = Seq(OpenBrace, m, Sp, InMacro, Sp, Naturals(), Sp, Mid, Sp,
            conditions, CloseBrace);
        return Disp(Universal("n", Equal(Call("a", n), Call("sInf", witnesses))));
    }

    private static Formula TheoremFormula()
    {
        var n = F.Id("n");
        var hypothesis = Relation(D(2), FormulaRelationOperator.LessThan, n);
        var conclusion = Equal(Call("a", n), Call("minFac", Subtract(n, D(1))));
        return Disp(Universal("n", new Formula.Logic(
            Parenthesized(hypothesis), FormulaLogicOperator.Implies,
            Parenthesized(conclusion))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Universal(string variable, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), Naturals(), body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Relation(Formula left, FormulaRelationOperator relation, Formula right) =>
        new Formula.Relation(left, relation, right);
    private static Formula Equal(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
