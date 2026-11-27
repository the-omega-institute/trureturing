using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Codes;

internal sealed class BinaryEAShorteningDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Codes/BinaryEAShortening.";
    private static readonly Formula HSpace = V("H");
    private static readonly Formula U = V("U");
    private static readonly Formula I = V("I");
    private static readonly Formula J = V("J");
    private static readonly Formula G = V("G");
    private static readonly Formula N = V("n");
    private static readonly Formula i = V("i");
    private static readonly Formula j = V("j");
    private static readonly Formula x = V("x");
    private static readonly Formula y = V("y");
    private static readonly Formula u = V("u");
    private static readonly Formula h = V("h");
    private static readonly Formula Field = Call("ZMod", D(2));
    private static readonly Formula Nat = Seq(Mathbb, Grp(V("N")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Surjective radical projections allow binary symplectic shortening. The spread and six-site Gram arguments rule out a rank-two radical site at length seven. A conditional count rules out a rank-two radical site at length eight under the two-site rank bound.",
        H("Rank-two shortening for binary symplectic codes"),
        Blocks(
            Entry("shorten_of_radical_surjective", "Shortening on a set of radical sites", Shortening(),
                "The site map reads the position and momentum bits. The map π sends a word to all its symbols on I, and shortened(I,S) is the subspace of S whose symbols on I vanish. Subtract a word of H with the same symbols on I to get a representative of each class. Orthogonality to H preserves the pairing, and surjectivity gives the two dimension drops."),
            Entry("five_site_gram_zero", "The Gram of a five-site spread", Spread(),
                "Each coordinate kernel has at least three nonzero words. The five kernels have disjoint nonzero parts, so those parts exhaust the fifteen nonzero words. At a site the binary pairing equals one plus the zero indicators of x, y, and x+y. For distinct nonzero x and y the five constants and the three zero indicators sum to zero in the binary field."),
            Entry("length_seven_no_surjective_radical_pair", "Exclusion of two rank-two shortenings at length seven", SevenPair(),
                "The shortened radical is zero and the shortened code has dimension four on five surviving sites. Its pairing vanishes by the spread argument, so the original code is isotropic by the radical lifts. An isotropic subspace in the nondegenerate length-seven ambient space has dimension at most seven."),
            Entry("seven_surviving_sites_no_rank_one_radical", "Exclusion with seven surviving sites and a rank-one radical projection bound", SevenSurviving(),
                "Fix an occupied radical site, where the kernel in H consists of zero and a single nonzero word h. Outside H, words vanishing there and at distinct second sites belong to disjoint sets. Rank-nullity and the cardinality of each pair kernel force h to be supported on at most two sites. A triple containing that support and the fixed site is injective on H and then on U. Its restriction on U is surjective by dimension, which contradicts orthogonality to h."),
            Entry("length_seven_rank_two_shortens_to_rank_one", "The remaining length-seven case after one shortening", SevenResidual(),
                "A rank-two radical site leaves dimensions two and six and a bound of two zeros outside the shortened radical. Any second surjective radical site would lift to a surjective joint projection on the two original sites, contradicting the length-seven spread obstruction."),
            Entry("length_eight_no_rank_two_site", "Exclusion of a rank-two radical site at length eight", Eight(),
                "Surjectivity at a second site of the shortened radical would lift to joint rank four on the corresponding original pair. The rank bound of three therefore leaves at most rank one at each of the seven surviving sites, where the conditional count gives the contradiction."))));

    private static Formula V(string value) => F.Id(value);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula App(Formula function, Formula arg) => new Formula.Apply(function, [arg]);
    private static Formula Word(Formula n)
    {
        var bits = new Formula.TypeArrow(Fin(n), Field);
        return Paren(Seq(Paren(bits), Sp, Times, Sp, Paren(bits)));
    }
    private static Formula Space(Formula n) => Call("Submodule", Field, Word(n));
    private static Formula Sites(Formula n) => Call("Finset", Fin(n));
    private static Formula Paren(Formula body) => Seq(Open, body, Close);
    private static Formula All(Formula v, Formula t, Formula b) =>
        Seq(Forall, Sp, Paren(Seq(v, Colon, Sp, t)), Comma, Sp, b);
    private static Formula Ex(Formula v, Formula t, Formula b) =>
        Seq(Exists, Sp, Paren(Seq(v, Colon, Sp, t)), Comma, Sp, b);
    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(Paren(premise), FormulaLogicOperator.Implies, conclusion);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Paren(left), FormulaLogicOperator.And, Paren(right));
    private static Formula Assumptions(Formula conclusion, params Formula[] premises)
    {
        for (int index = premises.Length - 1; index >= 0; --index)
            conclusion = Implies(premises[index], conclusion);
        return conclusion;
    }
    private static Formula In(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Card(Formula a) => Call("card", a);
    private static Formula Dim(Formula a) => Call("finrank", Field, a);
    private static Formula Short(Formula s) => Call("shortened", I, s);
    private static Formula Pairing(Formula n, Formula a, Formula b) => Call("spForm", n, a, b);
    private static Formula Local(Formula site, Formula word) => App(Call("site", site), word);
    private static Formula On(Formula map, Formula space) => Call("domRestrict", map, space);
    private static Formula Proj(Formula sites) => Call("restrictSites", sites);
    private static Formula Surj(Formula map) => Call("Surjective", map);
    private static Formula Not(Formula a) => new Formula.Not(Paren(a));
    private static Formula Comp(Formula s) => new Formula.Power(s, V("c"));
    private static Formula Singleton(Formula a) => Seq(OpenBrace, a, CloseBrace);
    private static Formula Pair(Formula a, Formula b) => Seq(OpenBrace, a, Comma, Sp, b, CloseBrace);
    private static Formula Zeros(Formula sites, Formula word) => Card(Call("zeroSites", sites, word));
    private static Formula Bound(Formula n, Formula sites, Formula upper, Formula lower, byte k) =>
        All(x, Word(n), Assumptions(Le(Zeros(sites, x), D(k)), In(x, upper), Not(In(x, lower))));
    private static Formula Orth(Formula n) => All(h, Word(n), Implies(In(h, HSpace),
        All(u, Word(n), Implies(In(u, U), Equal(Pairing(n, h, u), D(0))))));
    private static Formula FiniteSpaces(Formula n, Formula body) =>
        All(HSpace, Space(n), All(U, Space(n), body));
    private static Formula Standard(Formula n, Formula body) => FiniteSpaces(n,
        Assumptions(body, Le(HSpace, U), Equal(Dim(HSpace), D(4)), Equal(Dim(U), D(8)),
            Orth(n), Bound(n, V("univ"), U, HSpace, 3)));

    private static Formula Shortening()
    {
        Formula Drop(Formula s) =>
            Equal(Seq(Dim(Short(s)), Sp, Plus, Sp, D(2), Sp, Times, Sp, Card(I)), Dim(s));
        var representative = All(x, Word(N), Implies(In(x, U), Ex(y, Word(N),
            And(In(y, Short(U)), And(In(Sub(x, y), HSpace),
                All(u, Word(N), Implies(In(u, U), Equal(Pairing(N, y, u), Pairing(N, x, u)))))))));
        return All(N, Nat, All(I, Sites(N), FiniteSpaces(N,
            Assumptions(And(Drop(HSpace), And(Drop(U), representative)),
                Le(HSpace, U), Orth(N), Surj(On(Proj(I), HSpace))))));
    }

    private static Formula Spread()
    {
        Formula At(Formula w, string c) => App(Seq(Paren(w), Dot, V(c)), i);
        var sum = Seq(new Formula.Subscript(Sum, In(i, J)), Sp,
            Paren(Seq(At(x, "fst"), Sp, Cdot, Sp, At(y, "snd"), Sp, Plus, Sp,
                At(x, "snd"), Sp, Cdot, Sp, At(y, "fst"))));
        var bound = All(x, Word(N), Assumptions(Le(Zeros(J, x), D(1)), In(x, G), Ne(x, D(0))));
        var gramZero = All(x, Word(N), Implies(In(x, G),
            All(y, Word(N), Implies(In(y, G), Equal(sum, D(0))))));
        return All(N, Nat, All(J, Sites(N), All(G, Space(N),
            Assumptions(gramZero, Equal(Card(J), D(5)), Equal(Dim(G), D(4)), bound))));
    }

    private static Formula SevenPair() => Standard(D(7), All(I, Sites(D(7)),
        Assumptions(V("False"), Equal(Card(I), D(2)), Surj(On(Proj(I), HSpace)))));

    private static Formula SevenSurviving()
    {
        var support = All(h, Word(N), Implies(In(h, HSpace),
            All(i, Fin(N), Implies(Not(In(i, J)), Equal(Local(i, h), D(0))))));
        var rank = All(i, Fin(N), Implies(In(i, J), Not(Surj(On(Call("site", i), HSpace)))));
        return All(N, Nat, All(J, Sites(N), FiniteSpaces(N,
            Assumptions(V("False"), Le(HSpace, U), Equal(Card(J), D(7)),
                Equal(Dim(HSpace), D(2)), Equal(Dim(U), D(6)), Orth(N), support, rank,
                Bound(N, J, U, HSpace, 2)))));
    }

    private static Formula SevenResidual()
    {
        var rank = All(j, Fin(D(7)), Implies(In(j, Comp(I)),
            Not(Surj(On(Call("site", j), Short(HSpace))))));
        var body = And(Equal(Dim(Short(HSpace)), D(2)), And(Equal(Dim(Short(U)), D(6)),
            And(rank, Bound(D(7), Comp(I), Short(U), Short(HSpace), 2))));
        var letBody = Seq(Mathrm, Grp(V("let")), Sp, I, Sp, Colon, Eq, Sp, Singleton(i),
            Sp, Comma, Sp, body);
        return Standard(D(7), All(i, Fin(D(7)), Implies(Surj(On(Call("site", i), HSpace)), letBody)));
    }

    private static Formula Eight()
    {
        var rank = All(j, Fin(D(8)), Implies(Ne(j, i),
            Le(Dim(Call("range", On(Proj(Pair(i, j)), HSpace))), D(3))));
        return Standard(D(8), All(i, Fin(D(8)),
            Assumptions(V("False"), Surj(On(Call("site", i), HSpace)), rank)));
    }

    private static DocumentBlock Entry(string name, string title, Formula statement, string proof) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(proof))), DescribeRole.Theorem);
}
