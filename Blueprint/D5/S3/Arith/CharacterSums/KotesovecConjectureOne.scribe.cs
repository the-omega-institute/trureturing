using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class KotesovecConjectureOneDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CharacterSums/KotesovecConjectureOne.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/kotesovec2024a368959");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive modulus with nonzero complete monomial sums at every degree at least two is powerful.",
        H("Kotěšovec's first monomial-sum conjecture"),
        Blocks(
            Node("monomialSum", "Complete monomial sum", MonomialDefinition(), true,
                "OEIS A368959, NAME: \"Numbers m such that Sum_{k=0..m-1} exp(2*Pi*i*k^s/m) <> 0 for all s>=2.\" The exponent k^s is computed in the natural numbers before its cast to the complex numbers; the range contains exactly m terms.", true),
            Node("InA368959", "Membership in A368959", MembershipDefinition(), true,
                "OEIS A368959, NAME: \"Numbers m such that Sum_{k=0..m-1} exp(2*Pi*i*k^s/m) <> 0 for all s>=2.\" The positive-integer domain follows the entry's offset. Both m and s range over the natural numbers.", true),
            Node("InA338325", "Biquadratefree powerful numbers", FamilyDefinition(), true,
                "OEIS A338325, NAME: \"Biquadratefree powerful numbers: numbers whose exponents in their prime factorization are either 2 or 3.\" The exponent restriction applies to every prime factor of the positive integer m.", true),
            Node("claimOne", "The first conjecture", Equal(V("claimOne"), Parenthesized(ClaimBody())), true,
                "OEIS A368959, COMMENTS: \"Conjecture 1: This is a subset of A001694.\" A001694 denotes the powerful numbers. Powerful is the existing predicate from PowerfulNumber: a nonzero natural number whose every prime divisor has its square dividing the number.", true),
            Node("powerSum", "Additive-character monomial sum", PowerSumDefinition(), true,
                "The sum over a finite commutative ring evaluates an additive character on the s-th power of each ring element. The standard additive character of ZMod m recovers monomialSum."),
            Node("Good", "Nonvanishing for every injective character", GoodDefinition(), true,
                "Good n means that every injective complex additive character of ZMod n has nonzero power sums in every natural degree s at least two."),
            Node("good_prime_square", "Prime squares", PrimeGood(2), false,
                "For every prime p, every injective character modulo p squared has nonzero monomial sums at all degrees at least two. At these degrees p has no power-map preimage, whereas zero has a preimage."),
            Node("good_prime_cube", "Prime cubes", PrimeGood(3), false,
                "For degrees at least three the missing-preimage argument applies. Odd quadratic sums have nonzero squared norm. Modulo eight at degree two, the fibers over one and five have sizes four and zero."),
            Node("good_mul", "Coprime products", ProductGood(), false,
                "Chinese remaindering factors each power sum into two character sums. The restrictions of an injective character remain injective, so nonvanishing passes to coprime products. This supplies the products in the second conjecture."),
            Node("good_to_membership", "The standard additive character", ToMembership(), false,
                "Specializing the injective character to ZMod.stdAddChar converts Good n to membership in A368959. This converts the family and the four extra moduli in the second conjecture."),
            Node("family_inclusion", "The biquadratefree powerful family", FamilyInclusion(), false,
                "Every positive integer with prime-factorization exponents two or three is a product of coprime prime squares and cubes. Nonvanishing for these factors proves membership in A368959."),
            Node("good_243", "The modulus 243", Call("Good", D(2,4,3)), false,
                "For degree three the fibers over zero and eighty-one have sizes twenty-seven and zero; for degree four they have sizes twenty-seven and fifty-four. Quadratic nonvanishing handles degree two and the missing-preimage argument handles all degrees at least five."),
            Node("good_2401", "The modulus 2401", Call("Good", D(2,4,0,1)), false,
                "For degree three the fibers over zero and three hundred forty-three have sizes forty-nine and one hundred forty-seven. Quadratic nonvanishing handles degree two and the missing-preimage argument handles all degrees at least four."),
            Node("result", "Every A368959 term is powerful", ClaimBody(), false,
                "If a prime p divides m only once, Chinese remaindering isolates a prime-modulus factor. At degree p, Fermat's identity turns this factor into the sum of a nontrivial additive character, which is zero. Thus every prime divisor of a modulus in A368959 occurs at least twice."))));

    private static DocumentBlock Node(string name, string title, Formula formula, bool definition,
        string prose, bool literature = false) => Describe.Lean(
            DescribeId.Create("kotesovec-one-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula NatType() => Seq(Mathbb, Grp(V("N")));
    private static Formula ComplexType() => Seq(Mathbb, Grp(V("C")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Rightarrow, Sp, Parenthesized(b));
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula LtOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeOf(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula SumOver(string name, Formula type, Formula value) =>
        Seq(new Formula.Subscript(F.Sum, Seq(V(name), Colon, Sp, type)), Sp, value);
    private static Formula Membership(Formula m) => Call("InA368959", m);
    private static Formula Family(Formula m) => Call("InA338325", m);
    private static Formula ClaimBody() => All("m", NatType(),
        Imp(Membership(V("m")), Call("Powerful", V("m"))));
    private static Formula MonomialDefinition()
    {
        var m = V("m"); var s = V("s"); var k = V("k");
        var exponent = new Formula.Fraction(
            Mul(Mul(Mul(D(2), Qualified("Real", "pi")), Qualified("Complex", "I")),
                Cast(Cast(Pow(k, s), NatType()), ComplexType())), Cast(m, ComplexType()));
        var sum = Seq(new Formula.Subscript(F.Sum,
            Seq(k, Sp, InMacro, Sp, Apply(Qualified("Finset", "range"), m))), Sp,
            Apply(Qualified("Complex", "exp"), exponent));
        return All("m", NatType(), All("s", NatType(), Equal(Call("monomialSum", m, s), sum)));
    }
    private static Formula MembershipDefinition() => All("m", NatType(),
        Equal(Membership(V("m")), Parenthesized(And(LtOf(D(0), V("m")),
            All("s", NatType(), Imp(LeOf(D(2), V("s")), Ne(Call("monomialSum", V("m"), V("s")), D(0))))))));
    private static Formula FamilyDefinition()
    {
        var m = V("m"); var p = V("p");
        var exponents = Or(Equal(Apply(Qualified("Nat", "factorization"), m, p), D(2)),
            Equal(Apply(Qualified("Nat", "factorization"), m, p), D(3)));
        return All("m", NatType(), Equal(Family(m), Parenthesized(And(LtOf(D(0), m),
            All("p", NatType(), Imp(Seq(p, Sp, InMacro, Sp, Apply(Qualified("Nat", "primeFactors"), m)), exponents))))));
    }
    private static Formula PowerSumDefinition() => All("R", V("Type"),
        Instance(Call("CommRing", V("R")), Instance(Call("Fintype", V("R")),
            All("psi", Call("AddChar", V("R"), ComplexType()), All("s", NatType(),
                Equal(Call("powerSum", V("psi"), V("s")), SumOver("x", V("R"), Apply(V("psi"), Pow(V("x"), V("s"))))))))));
    private static Formula GoodDefinition() => All("n", NatType(), Instance(Call("NeZero", V("n")),
        Equal(Call("Good", V("n")), Parenthesized(All("psi", Call("AddChar", Call("ZMod", V("n")), ComplexType()),
            Imp(Apply(Qualified("Function", "Injective"), V("psi")), All("s", NatType(),
                Imp(LeOf(D(2), V("s")), Ne(Call("powerSum", V("psi"), V("s")), D(0))))))))));
    private static Formula PrimeGood(byte exponent) => All("p", NatType(),
        Imp(Apply(Qualified("Nat", "Prime"), V("p")),
            Instance(Call("NeZero", Pow(V("p"), D(exponent))), Call("Good", Pow(V("p"), D(exponent))))));
    private static Formula ProductGood() => All("r", NatType(), All("t", NatType(),
        Instance(Call("NeZero", V("r")), Instance(Call("NeZero", V("t")),
            Imp(Apply(Qualified("Nat", "Coprime"), V("r"), V("t")),
                Imp(Call("Good", V("r")), Imp(Call("Good", V("t")), Call("Good", Mul(V("r"), V("t"))))))))));
    private static Formula ToMembership() => All("n", NatType(), Instance(Call("NeZero", V("n")),
        Imp(Call("Good", V("n")), Membership(V("n")))));
    private static Formula FamilyInclusion() => All("m", NatType(), Imp(Family(V("m")), Membership(V("m"))));
}
