using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimitiveRoot;

internal sealed class PrimitiveRootCharacterExpansionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/PrimitiveRoot/CharacterExpansion.";
    private static readonly LibraryNoteRef Cohen =
        LibraryNoteRef.Create("D5/L/ArithUnits/cohen2015grosswald");
    private static readonly LibraryNoteRef McGown =
        LibraryNoteRef.Create("D5/L/ArithUnits/mcgown2016grosswald");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Character expansion of the elementary free sieve",
        H("Character expansion of the elementary free sieve"), Blocks(
            Describe.Lean(DescribeId.Create("primitive-root-sieve-theta"),
                DeclarationHandle.Create(Prefix + "theta"), H("The local density product"),
                StatementSource.FromAuthor(Disp(Eq(Call("theta", V("e")),
                    Prod("q", Call("primeFactors", V("e")),
                        Sub(D(1), Div(D(1), V("q"))))))),
                AssessedProvenance.FromLiterature(Cohen), Blocks(Paragraph(Text(
                    "The product runs over the distinct prime divisors of e. Each factor " +
                    "is positive, including the empty product at e=1."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("primitive-root-signed-coefficient-nonnegative"),
                DeclarationHandle.Create(Prefix + "errorCoefficient_nonneg"),
                H("The reciprocal-sum criterion for signed coefficient bounds"),
                StatementSource.FromAuthor(Disp(All("e", Nat(),
                    All("T", Call("Finset", Nat()),
                        Iff(Le(Sum("t", V("T"), Div(D(1), V("t"))),
                                Div(Call("card", V("T")), D(2))),
                            And(Le(Sub(PowerCount(), Call("delta", V("T"))),
                                    Call("K", V("e"), V("T"))),
                                Le(D(0), Call("K", V("e"), V("T"))))))))),
                AssessedProvenance.FromRepo(McGown), Blocks(Paragraph(Text(
                    "The reciprocal sum over T is at most card(T)/2 exactly when " +
                    "2^omega(e)-delta(T)<=K(e,T) and K(e,T)>=0, for every margin. " +
                    "It suffices that each member of T is at least two, allowing composites. " +
                    "In particular, the hypothesis holds for every set of primes. " +
                    "Nonnegativity alone does not identify K with the absolute error mass."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primitive-root-sieve-theta-positive"),
                DeclarationHandle.Create(Prefix + "theta_pos"), H("Positive local density"),
                StatementSource.FromAuthor(Disp(All("e", Nat(),
                    Lt(D(0), Call("theta", V("e")))))),
                AssessedProvenance.FromRepo(Cohen), Blocks(Paragraph(Text(
                    "Each prime divisor q is greater than one, so 1-1/q is positive. " +
                    "Their finite product is positive, also for e=0 and e=1."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primitive-root-sieve-delta"),
                DeclarationHandle.Create(Prefix + "delta"), H("The remaining-prime margin"),
                StatementSource.FromAuthor(Disp(Eq(Call("delta", V("T")),
                    Sub(D(1), Sum("t", V("T"), Div(D(1), V("t"))))))),
                AssessedProvenance.FromLiterature(McGown), Blocks(Paragraph(Text(
                    "The margin may be positive, zero or negative."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("primitive-root-sieve-error-coefficient"),
                DeclarationHandle.Create(Prefix + "errorCoefficient"),
                H("The combined error coefficient"),
                StatementSource.FromAuthor(Disp(Eq(Call("K", V("e"), V("T")),
                    Add(Mul(Call("delta", V("T")), Sub(PowerCount(), D(1))),
                        Mul(Add(Sub(Call("card", V("T")), D(1)),
                            Call("delta", V("T"))), PowerCount()))))),
                AssessedProvenance.FromLiterature(McGown), Blocks(Paragraph(Text(
                    "Here omega(e) is the number of distinct prime divisors of e. " +
                    "The cardinality of T is interpreted as a real number before " +
                    "subtracting one. " +
                    "This coefficient is nonnegative for every set of sieve primes. " +
                    "For delta>=0 it bounds the total nonprincipal coefficient mass divided " +
                    "by theta(e) when T is disjoint from the prime support of e. " +
                    "K_abs=K exactly when delta>=0 or e has no prime factors."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("primitive-root-sieve-absolute-coefficient"),
                DeclarationHandle.Create(Prefix + "errorCoefficientAbs"),
                H("Absolute coefficient mass for every margin"),
                StatementSource.FromAuthor(Disp(Eq(Call("Kabs", V("e"), V("T")),
                    Add(Mul(Call("abs", Call("delta", V("T"))), Sub(PowerCount(), D(1))),
                        Mul(Add(Sub(Call("card", V("T")), D(1)),
                            Call("delta", V("T"))), PowerCount()))))),
                AssessedProvenance.FromRepo(McGown), Blocks(Paragraph(Text(
                    "The first coefficient uses the absolute margin. The remaining " +
                    "coefficient is the sum of 1-1/t over T. No sign of delta is required."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("primitive-root-sieve-coefficient-agreement"),
                DeclarationHandle.Create(Prefix + "errorCoefficientAbs_eq"),
                H("The complete coefficient agreement criterion"),
                StatementSource.FromAuthor(Disp(All("e", Nat(),
                    All("T", Call("Finset", Nat()), Iff(
                        Eq(Call("Kabs", V("e"), V("T")), Call("K", V("e"), V("T"))),
                        Agreement(V("e"), V("T"))))))),
                AssessedProvenance.FromRepo(McGown), Blocks(Paragraph(Text(
                    "K_abs-K=(abs(delta)-delta)(2^omega(e)-1). Thus equality holds " +
                    "exactly when delta is nonnegative or e has no prime factors."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primitive-root-elementary-sieve-error-bound"),
                DeclarationHandle.Create(Prefix + "weighted_sieve_error_bound"),
                H("A two-sided elementary sieve estimate for every margin"),
                StatementSource.FromAuthor(Disp(WeightStatement(true))),
                AssessedProvenance.FromRepo(McGown), Blocks(Paragraph(Text(
                    "Under the support and character bounds of the signed estimate, " +
                    "the elementary sieve weight differs from theta(e)delta(T) times " +
                    "the total unit weight by at most theta(e)K_abs(e,T)M. " +
                    "The weight is any real function and delta may have either sign."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primitive-root-unit-character-sum"),
                DeclarationHandle.Create(Prefix + "sum_units_character"),
                H("Character sums are supported on units"),
                StatementSource.FromAuthor(Disp(All("p", Nat(), Imp(Not(Eq(V("p"), D(0))),
                    All("W", new Formula.TypeArrow(Call("ZMod", V("p")), Complex()),
                        All("chi", Call("DirichletCharacter", Complex(), V("p")),
                            Eq(CharacterSum(), Sum("a", Call("Units", V("p")),
                                Mul(Call("W", V("a")), Call("chi", V("a"))))))))))),
                AssessedProvenance.FromRepo(Cohen), Blocks(Paragraph(Text(
                    "For any nonzero modulus p, every Dirichlet character is zero on nonunits. " +
                    "Restriction to the unit " +
                    "group therefore preserves a character sum with an arbitrary complex weight. " +
                    "In particular, the principal character contributes the total unit weight, " +
                    "rather than the total weight over all residue classes."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primitive-root-controlled-bound-nonnegative"),
                DeclarationHandle.Create(Prefix + "bound_nonneg"),
                H("An inhabited controlled character family forces a nonnegative bound"),
                StatementSource.FromAuthor(Disp(BoundNonnegativeStatement())),
                AssessedProvenance.FromRepo(McGown), Blocks(Paragraph(Text(
                    "Put d=gcd(t,p-1). Since p is prime, d is positive and divides p-1, " +
                    "so a character of order d exists, including the principal " +
                    "character when d=1. " +
                    "If the absolute real part of the W-weighted sum is at most M for " +
                    "every character of this exact order, choose one such character. Its " +
                    "absolute real sum is nonnegative, so M is nonnegative. No bounds for " +
                    "characters of other orders are required."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primitive-root-elementary-sieve-lower-bound"),
                DeclarationHandle.Create(Prefix + "weighted_sieve_lower_bound"),
                H("A two-sided estimate for elementary sieve weight"),
                StatementSource.FromAuthor(Disp(WeightStatement())),
                AssessedProvenance.FromRepo(McGown), Blocks(Paragraph(Text(
                    "Let p be prime. Every prime divisor of e divides p-1. Every member t of T " +
                    "is prime, divides p-1 and is absent from the prime support of e. " +
                    "Write R for the radical of e. " +
                    "For each nonprincipal character of order dividing R or tR with t in T, " +
                    "assume the absolute real part of its W-weighted sum is at most M. " +
                    "If delta(T)>=0 or e has no prime factors, the elementary sieve " +
                    "weight differs " +
                    "from the theta-delta " +
                    "main term by at most theta(e)K(e,T)M in either direction. " +
                    "This expansion does not need a cover condition or any sign condition on W.")),
                    Paragraph(Text(
                    "For a prime q dividing p-1, the characters trivial on the q-th power " +
                    "subgroup form a group of cardinality q. Orthogonality makes their sum q " +
                    "on that subgroup and zero elsewhere. Removing the principal character " +
                    "gives the local q-free expansion. Multiplying local factors gives the " +
                    "e-free indicator with principal coefficient theta(e). The remaining " +
                    "normalized coefficient mass is 2^omega(e)-1. Distinct prime orders are " +
                    "coprime, so every error character is nonprincipal; its order divides R.")),
                    Paragraph(Text(
                    "The exclusion terms for t in T use characters of order dividing tR. " +
                    "Because t is absent from the prime support of e, their products " +
                    "are nonprincipal. " +
                    "Their normalized mass is (1-1/t)2^omega(e). Together with the delta(T) " +
                    "multiple of the e-free error, these masses sum to K(e,T). Every " +
                    "coefficient is real, so the estimate needs only real parts. The " +
                    "coefficient agreement criterion converts the absolute coefficient to K; " +
                    "the e-free error vanishes when e has no prime factors."))),
                DescribeRole.Theorem))));

    private static Formula Agreement(Formula e, Formula t) =>
        Or(Le(D(0), Call("delta", t)), Eq(Call("primeFactors", e), Call("empty")));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula PowerCount() => Call("pow", D(2), Call("omega", V("e")));
    private static Formula Radical() => Prod("q", Call("primeFactors", V("e")), V("q"));
    private static Formula CharacterSum() => Sum("a", Call("Residues", V("p")),
        Mul(Call("W", V("a")), Call("chi", V("a"))));
    private static Formula CharacterBound()
    {
        var order = Call("orderOf", V("chi"));
        var support = Or(Call("dvd", order, Radical()),
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("t"), Nat(),
                And(Mem(V("t"), V("T")), Call("dvd", order, Mul(V("t"), Radical())))));
        return All("chi", Call("DirichletCharacter", Complex(), V("p")),
            Imp(Not(Eq(V("chi"), D(1))), Imp(support,
                Le(Call("abs", Call("re", CharacterSum())), V("M")))));
    }
    private static Formula BoundNonnegativeStatement()
    {
        var p = V("p");
        var d = Call("gcd", V("t"), Sub(p, D(1)));
        var bound = All("chi", Call("DirichletCharacter", Complex(), p),
            Imp(Eq(Call("orderOf", V("chi")), d),
                Le(Call("abs", Call("re", CharacterSum())), V("M"))));
        return All("p", Nat(), Imp(Call("Prime", p),
            All("W", new Formula.TypeArrow(Call("ZMod", p), Complex()),
                All("M", Real(), All("t", Nat(), Imp(bound, Le(D(0), V("M"))))))));
    }
    private static Formula WeightStatement(bool absolute = false)
    {
        var p = V("p"); var e = V("e"); var t = V("t"); var a = V("a"); var q = V("q");
        var support = All("q", Nat(), Imp(Mem(q, Call("primeFactors", e)),
            Call("dvd", q, Sub(p, D(1)))));
        var sieveSupport = All("t", Nat(), Imp(Mem(t, V("T")),
            And(Call("Prime", t), And(Call("dvd", t, Sub(p, D(1))),
                Not(Mem(t, Call("primeFactors", e)))))));
        var eFree = All("q", Nat(), Imp(Mem(q, Call("primeFactors", e)),
            Not(Mem(a, Call("powerSubgroup", Call("Units", p), q)))));
        var count = Call("card", Seq(OpenBrace, t, Sp, InMacro, Sp, V("T"), Sp, Mid, Sp,
            Mem(a, Call("powerSubgroup", Call("Units", p), t)), CloseBrace));
        var main = Mul(Mul(Call("theta", e), Call("delta", V("T"))),
            Sum("a", Call("Units", p), Call("W", a)));
        var error = Mul(Mul(Call("theta", e),
            Call(absolute ? "Kabs" : "K", e, V("T"))), V("M"));
        var total = Sum("a", Call("Units", p),
            Mul(Mul(Call("W", a), Call("if", eFree, D(1), D(0))), Sub(D(1), count)));
        var estimate = Le(Call("abs", Sub(total, main)), error);
        var conclusion = absolute ? estimate : Imp(Agreement(e, V("T")), estimate);
        return All("p", Nat(), Imp(Call("Prime", p),
            All("W", new Formula.TypeArrow(Call("ZMod", p), Real()),
                All("e", Nat(), Imp(support, All("T", Call("Finset", Nat()),
                    Imp(sieveSupport, All("M", Real(), Imp(CharacterBound(), conclusion)))))))));

    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex() => Seq(Mathbb, Grp(V("C")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Sum(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(V(name), Sp, InMacro, Sp, set)), Sp, Grp(body));
    private static Formula Prod(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(F.Prod, Seq(V(name), Sp, InMacro, Sp, set)), Sp, Grp(body));
}
