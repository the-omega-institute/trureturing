using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class NarayanCatenarySpectrumMembershipDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/NarayanCatenarySpectrumMembership.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/narayan2026deltaset");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A factorization fiber on the original arithmetic generators realizes Narayan's catenary degree.",
        H("Narayan's catenary spectrum membership"),
        Blocks(
            Node("generators", "The original generating tuple", GeneratorFormula(),
                "The coordinates have indices zero through k. Coordinate zero represents a, and coordinate i greater than zero represents ah + id. The element ah is represented by h copies of a.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsAtom", "Atoms of an additive submonoid", AtomFormula(),
                "An atom is a nonzero monoid element that cannot be split as a sum of two nonzero monoid elements.",
                DescribeRole.Definition),
            Node("distance", "Residual factorization distance", DistanceFormula(),
                "Subtract the pointwise minimum from both vectors and take the larger residual coordinate sum.",
                DescribeRole.Definition),
            Node("Chain", "Bounded-distance chains", ChainFormula(),
                "The reflexive transitive closure uses edges of distance at most B. Every vertex has the same weighted value n.",
                DescribeRole.Definition),
            Node("catenarySpectrum", "The elementwise catenary spectrum", SpectrumFormula(),
                "Each represented value contributes the least threshold at which its entire factorization fiber is connected.",
                DescribeRole.Definition),
            Node("ceilParameter", "The ceiling parameter", CeilingFormula(),
                "With k greater than one and less than a, the denominator and numerator are positive.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("witness", "The element attaining the threshold", WitnessFormula(),
                "For ceiling parameter t, the value is ah(t + 1) + d(a + t).",
                DescribeRole.Definition),
            Node("Low", "The low-index-weight class", ClassFormula(false),
                "The weighted sum of the positive indices is t. The zero coordinate is h times the deficit from t + 1 in the positive-index count, plus d.",
                DescribeRole.Definition),
            Node("High", "The high-index-weight class", ClassFormula(true),
                "The weighted sum of the positive indices is a + t, the positive-index count is t + 1, and the zero coordinate vanishes.",
                DescribeRole.Definition),
            Node("WitnessCheckpoint", "The atom tuple and the two fiber classes", FiberFormula(),
                "The tuple is injective and its range is exactly the atoms of a cofinite monoid. Coprimality reduces the index weight modulo a to t. The generator bounds then allow only weights t and a + t. "
                    + "The low representative is (h + d)e₀ + te₁. The high representative is teₖ + e₂₊ᵨ, where ρ is the remainder of a − 2 upon division by k − 1. Coincident indices add with multiplicity. "
                    + "The high class uses neither coordinate zero nor one. Any shared copies contribute at most t − Y to the common part, where Y is the low vector's positive-index count. Its length is N + (h − 1)(t − Y), so cancellation leaves distance at least N. Thus every chain below N stays in one class.",
                DescribeRole.Definition),
            Node("result", "Conjecture 18.2", ResultFormula(),
                "Narayan's Conjecture 18.2 on p. 22 asserts that the ceiling parameter plus h + d belongs to the catenary spectrum under the hypotheses in §3. "
                    + "The exchange of h copies of a and one copy of generator i for one copy each of generators 1 and i − 1 preserves value and reduces t − Y. Iteration joins the low class to its representative. At i = 2 the exchange adds two copies of generator 1. "
                    + "The high class is connected by edges of size at most t + 1. At N − 1 these two classes are exactly the components. At N the low representative is adjacent to every high vector, establishing the least connecting threshold. The proof includes k = 2, k = a − 1, a = 3 and h = 2.",
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance? provenance = null, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("narayan-catenary-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance ?? AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula A => F.Id("a");
    private static Formula Hh => F.Id("h");
    private static Formula Dd => F.Id("d");
    private static Formula K => F.Id("k");
    private static Formula G => F.Id("g");
    private static Formula N => F.Id("N");
    private static Formula T => F.Id("t");
    private static Formula Value => F.Id("n");
    private static Formula B => F.Id("B");
    private static Formula Z => F.Id("z");
    private static Formula W => F.Id("w");
    private static Formula S => F.Id("S");
    private static Formula I => F.Id("i");
    private static Formula M => F.Id("m");
    private static Formula P => F.Id("p");
    private static Formula U => F.Id("u");
    private static Formula V => F.Id("v");

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => Apply(Named(name), args);
    private static Formula Apply(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Paren(Formula formula) => Seq(Open, formula, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Paren(left), FormulaLogicOperator.And, Paren(right));
    private static Formula Or(Formula left, Formula right) => new Formula.Logic(Paren(left), FormulaLogicOperator.Or, Paren(right));
    private static Formula ImpliesTo(Formula left, Formula right) => new Formula.Logic(Paren(left), FormulaLogicOperator.Implies, Paren(right));
    private static Formula Equivalent(Formula left, Formula right) => new Formula.Logic(Paren(left), FormulaLogicOperator.Iff, Paren(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula FinType(Formula p) => Call("Fin", p);
    private static Formula Vector(Formula p) => Paren(new Formula.TypeArrow(FinType(p), Nat()));
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, F.Id(name), Sp, Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Let(string name, Formula value, Formula body) =>
        Seq(Named("let"), Sp, F.Id(name), Sp, Colon, F.Eq, Sp, value, Comma, Sp, body);
    private static Formula SumOver(Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(I, Sp, Colon, Sp, type)), Sp, Paren(body));

    private static Formula GeneratorFormula() => Parameters(All("i", FinType(Add(K, D(1))),
        Eq(Call("generators", A, Hh, Dd, K, I),
            Call("ite", Eq(I, D(0)), A, Add(Mul(A, Hh), Mul(Call("val", I), Dd))))));

    private static Formula AtomFormula() =>
        All("S", Call("AddSubmonoid", Nat()), All("m", Nat(), Equivalent(Call("IsAtom", S, M),
            And(Member(M, S), And(new Formula.Relation(M, FormulaRelationOperator.NotEqual, D(0)),
                All("u", Nat(), ImpliesTo(Member(U, S), All("v", Nat(), ImpliesTo(Member(V, S),
                    ImpliesTo(Eq(Add(U, V), M), Or(Eq(U, D(0)), Eq(V, D(0)))))))))))));

    private static Formula Residual(Formula vector) =>
        SumOver(FinType(P), Sub(Apply(vector, I), Call("min", Apply(Z, I), Apply(W, I))));

    private static Formula DistanceFormula() => All("p", Nat(), All("z", Vector(P), All("w", Vector(P),
        Eq(Call("distance", Z, W), Call("max", Residual(Z), Residual(W))))));

    private static Formula Fiber() => Call("Z", G, Value);
    private static Formula ChainAt(Formula threshold, Formula z, Formula w) => Call("Chain", G, Value, threshold, z, w);
    private static Formula BothInFiber(Formula body) => All("z", Fiber(), All("w", Fiber(), body));
    private static Formula LeastThreshold() => Call("IsLeast",
        SetOf("B", Nat(), BothInFiber(ChainAt(B, Z, W))), N);

    private static Formula ChainFormula()
    {
        var edge = Seq(Paren(Seq(U, Sp, Colon, Sp, Fiber())), Sp,
            Paren(Seq(V, Sp, Colon, Sp, Fiber())), Sp, Mapsto, Sp,
            Le(Call("distance", Call("val", U), Call("val", V)), B));
        return All("p", Nat(), All("g", Vector(P), All("n", Nat(), All("B", Nat(),
            BothInFiber(Equivalent(ChainAt(B, Z, W),
                Apply(Seq(Named("Relation"), Dot, Named("ReflTransGen")), edge, Z, W)))))));
    }

    private static Formula SpectrumFormula() => All("p", Nat(), All("g", Vector(P),
        Eq(Call("catenarySpectrum", G), SetOf("N", Nat(), Ex("n", Nat(),
            And(Call("Nonempty", Fiber()), LeastThreshold()))))));

    private static Formula CeilingFormula() => All("a", Nat(), All("k", Nat(),
        Eq(Call("ceilParameter", A, K), Call("ceilDiv", Sub(A, K), Sub(K, D(1))))));

    private static Formula WitnessFormula() => Parameters(Let("t", Call("ceilParameter", A, K),
        Eq(Call("witness", A, Hh, Dd, K), Add(Mul(A, Mul(Hh, Add(T, D(1)))), Mul(Add(A, T), Dd)))));

    private static Formula ClassFormula(bool high)
    {
        var count = SumOver(FinType(K), Apply(Z, Call("succ", I)));
        var weight = SumOver(FinType(K), Mul(Apply(Z, Call("succ", I)), Add(Call("val", I), D(1))));
        var zero = Apply(Z, D(0));
        var body = high
            ? Equivalent(Call("High", A, T, Z), And(Eq(weight, Add(A, T)), And(Eq(count, Add(T, D(1))), Eq(zero, D(0)))))
            : Equivalent(Call("Low", Hh, Dd, T, Z),
                And(Eq(weight, T), Eq(zero, Add(Mul(Hh, Sub(Add(T, D(1)), count)), Dd))));
        return All("k", Nat(), high
            ? All("a", Nat(), All("t", Nat(), All("z", Vector(Add(K, D(1))), body)))
            : All("h", Nat(), All("d", Nat(), All("t", Nat(), All("z", Vector(Add(K, D(1))), body)))));
    }

    private static Formula Lo(Formula z) => Call("Low", Hh, Dd, T, z);
    private static Formula Hi(Formula z) => Call("High", A, T, z);
    private static Formula MemberValue(Formula z) => Call("val", z);

    private static Formula FiberBody()
    {
        var vector = Vector(Add(K, D(1)));
        var cross = All("z", vector, All("w", vector,
            ImpliesTo(Lo(Z), ImpliesTo(Hi(W), Le(N, Call("distance", Z, W))))));
        var separated = All("B", Nat(), ImpliesTo(Lt(B, N), BothInFiber(
            ImpliesTo(Lo(MemberValue(Z)), ImpliesTo(Hi(MemberValue(W)), new Formula.Not(ChainAt(B, Z, W)))))));
        return Let("S", Call("closure", Call("range", G)),
            And(Call("Injective", G), And(Call("Finite", Call("compl", S)),
            And(All("m", Nat(), Equivalent(Call("IsAtom", S, M), Member(M, Call("range", G)))),
            And(Member(Value, S), And(All("z", vector, Equivalent(Member(Z, Fiber()), Or(Lo(Z), Hi(Z)))),
            And(All("z", vector, new Formula.Not(And(Lo(Z), Hi(Z)))),
            And(Ex("z", Fiber(), Lo(MemberValue(Z))), And(Ex("w", Fiber(), Hi(MemberValue(W))),
            And(cross, separated))))))))));
    }

    private static Formula FiberFormula() => Parameters(WithFiberLets(
        Equivalent(Call("WitnessCheckpoint", A, Hh, Dd, K), FiberBody())));

    private static Formula ResultFormula()
    {
        var predecessor = BothInFiber(Equivalent(ChainAt(Sub(N, D(1)), Z, W),
            Or(And(Lo(MemberValue(Z)), Lo(MemberValue(W))), And(Hi(MemberValue(Z)), Hi(MemberValue(W))))));
        var conclusion = WithFiberLets(And(FiberBody(),
            And(predecessor, And(LeastThreshold(), Member(N, Call("catenarySpectrum", G))))));
        return Parameters(ImpliesTo(Lt(D(0), Dd), ImpliesTo(Call("Coprime", A, Dd),
            ImpliesTo(Lt(D(1), K), ImpliesTo(Lt(K, A), ImpliesTo(Lt(D(1), Hh), conclusion))))));
    }

    private static Formula WithFiberLets(Formula body) =>
        Let("g", Call("generators", A, Hh, Dd, K), Let("t", Call("ceilParameter", A, K),
            Let("n", Call("witness", A, Hh, Dd, K), Let("N", Add(Add(T, Hh), Dd), body))));

    private static Formula Parameters(Formula body) =>
        All("a", Nat(), All("h", Nat(), All("d", Nat(), All("k", Nat(), body))));
}
