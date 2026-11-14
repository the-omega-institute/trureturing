using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class AlloucheReflectionComplexitySupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Complexity/AlloucheReflectionComplexitySupport.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/allouche2025reflectioncomplexity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marked mirrors transfer bounded factor increments to reflection increments.",
        H("Reflection orbits and a marked bi-infinite mirror"),
        Blocks(
            Node("fiberSurplus", "Counting the surplus in finite fibers", FiberSurplus(),
                "Summing each nonempty fiber's cardinality minus one gives the domain cardinality minus the image cardinality. Both subtractions are natural subtraction.",
                AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("ReflectivelyEquivalent", "Reflection equivalence", ReflectionRelation(),
                "Definition 1, p. 3: “Two finite words u and v are reflectively equivalent if v = u or v = uᴿ.” The alphabet is arbitrary, and Fin.rev reverses the zero-based positions of a word of length n.",
                AssessedProvenance.FromLiterature(Source)),
            Node("reflectionComplexity", "Counting classes of actual factors", ReflectionCount(),
                "Definition 3, p. 3: “Let x be a sequence. The reflection complexity function rₓ : ℕ₀ → ℕ of x maps every n ≥ 0 to the number of distinct length-n factors of x, up to equivalence by ∼ᵣ.” The quotient is taken over the occurring factors themselves, without assuming reversal closure. The empty factor contributes one class. Example 4 counts the Thue–Morse length-two classes represented by 00, 11 and either of 01 and 10, giving three.",
                AssessedProvenance.FromLiterature(Source)),
            Node("mirrorWord", "A single marker between two mirror images", MirrorWord(),
                "The new letter is Option.none. At every nonzero integer position, Option.some carries the source letter indexed by the natural absolute value minus one. Natural subtraction is truncated; the subtraction is evaluated only away from the marker.",
                AssessedProvenance.FromRepo()),
            Node("intFactor", "Factors at integer starts", IntegerFactor(),
                "A factor at i reads the bi-infinite word at i plus each finite position, with that position coerced to the integers.",
                AssessedProvenance.FromRepo()),
            Node("intFactorSet", "The bi-infinite factor set", IntegerFactorSet(),
                "The finite set contains exactly those functions on Fin n that occur at some integer start.",
                AssessedProvenance.FromRepo()),
            Node("mirrorFactorLinear", "Linear growth survives the marked mirror", MirrorLinear(),
                "A length-n factor avoiding the marker is a source factor or its reversal. Factors containing the marker have n distinct marker positions. Thus the exact mirror count is the size of the reversal-symmetrized factor set plus n, including n = 0. A source bound C times (n + 1) therefore gives mirror coefficient 2 times C plus 1.",
                AssessedProvenance.FromRepo(), DescribeRole.Theorem),
            Node("reflectionBoundOfMirrorBound", "Bounded mirror increments bound reflection increments", Transfer(),
                "Write q for reflection complexity, u for the reversal-symmetrized factor count and P for its palindromic count. Counting reflection orbits gives 2q = u + P. A sliding factor walk visits all reflection classes; deleting the distinct palindromic loops preserves connectivity and gives q(n) + P(n + 1) ≤ q(n + 1) + 1. Combining these counts with the exact mirror formula bounds the integer absolute difference by D + 1.",
                AssessedProvenance.FromRepo(), DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        AssessedProvenance provenance, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create("acls-support-" + name.Replace('.', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname,
        Grp(Seq([.. name.Split('.').SelectMany((part, index) =>
            index == 0 ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) })])));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula x, Formula type, Formula body) =>
        Seq(Exists, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Or(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Or, Parenthesized(y));
    private static Formula Arrow(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.Implies, Parenthesized(y));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Lam(Formula x, Formula type, Formula body) =>
        Parenthesized(Seq(x, Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula Cast(Formula x) => Parenthesized(Seq(x, Colon, Sp, Ints()));
    private static Formula FiniteAlphabet(Formula a, Formula body) => All(a, Named("Type"),
        Seq(OpenBracket, Call("Fintype", a), CloseBracket, Sp, body));
    private static Formula FactorCount(Formula x, Formula n) => Call("Finset.card", Call("wordFactorSet", x, n));
    private static Formula MirrorCount(Formula x, Formula n) =>
        Call("Finset.card", Call("intFactorSet", Call("mirrorWord", x), n));
    private static Formula Difference(Formula x, Formula n) => Call("Int.natAbs",
        Sub(Cast(Call("reflectionComplexity", x, Add(n, D(1)))), Cast(Call("reflectionComplexity", x, n))));

    private static Formula FiberSurplus()
    {
        Formula xType = F.Id("X"), yType = F.Id("Y"), a = F.Id("a"), f = F.Id("f");
        Formula x = F.Id("x"), y = F.Id("y");
        Formula image = Call("Finset.image", f, a);
        Formula fiber = Call("Finset.filter", Lam(x, xType,
            Equal(new Formula.Apply(f, [x]), y)), a);
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(y, Sp, InMacro, Sp, image)), Sp,
            Call("Nat.sub", Call("Finset.card", fiber), D(1)));
        return All(xType, Named("Type"), All(yType, Named("Type"),
            Seq(OpenBracket, Call("DecidableEq", yType), CloseBracket, Sp,
                All(a, Call("Finset", xType), All(f, Fn(xType, yType),
                    Equal(sum, Call("Nat.sub", Call("Finset.card", a), Call("Finset.card", image))))))));
    }

    private static Formula ReflectionRelation()
    {
        Formula a = F.Id("A"), n = F.Id("n"), u = F.Id("u"), v = F.Id("v");
        Formula word = Fn(Call("Fin", n), a);
        return All(a, Named("Type"), All(n, Nats(), All(u, word, All(v, word,
            Equal(Call("ReflectivelyEquivalent", u, v),
                Or(Equal(v, u), Equal(v, Call("Function.comp", u, Named("Fin.rev")))))))));
    }

    private static Formula ReflectionCount()
    {
        Formula a = F.Id("A"), x = F.Id("x"), n = F.Id("n"), w = F.Id("w"), u = F.Id("u"), v = F.Id("v");
        Formula word = Fn(Call("Fin", n), a);
        Formula factors = Call("Subtype", Lam(w, word,
            new Formula.Relation(w, FormulaRelationOperator.MemberOf, Call("wordFactorSet", x, n))));
        Formula relation = Lam(u, factors, Lam(v, factors,
            Call("ReflectivelyEquivalent", Call("val", u), Call("val", v))));
        return FiniteAlphabet(a, All(x, Fn(Nats(), a), All(n, Nats(),
            Equal(Call("reflectionComplexity", x, n), Call("Nat.card", Call("Quot", relation))))));
    }

    private static Formula MirrorWord()
    {
        Formula a = F.Id("A"), x = F.Id("x"), i = F.Id("i");
        Formula value = Seq(Named("if"), Sp, Parenthesized(Equal(i, D(0))), Sp, Named("then"), Sp,
            Named("none"), Sp, Named("else"), Sp,
            Call("some", new Formula.Apply(x, [Call("Nat.sub", Call("Int.natAbs", i), D(1))])));
        return All(a, Named("Type"), All(x, Fn(Nats(), a), All(i, Ints(), Equal(Call("mirrorWord", x, i), value))));
    }

    private static Formula IntegerFactor()
    {
        Formula a = F.Id("A"), z = F.Id("z"), n = F.Id("n"), i = F.Id("i"), k = F.Id("k");
        return All(a, Named("Type"), All(z, Fn(Ints(), Call("Option", a)), All(n, Nats(), All(i, Ints(),
            Equal(Call("intFactor", z, n, i), Lam(k, Call("Fin", n),
                new Formula.Apply(z, [Add(i, Cast(Call("val", k)))])))))));
    }

    private static Formula IntegerFactorSet()
    {
        Formula a = F.Id("A"), z = F.Id("z"), n = F.Id("n"), w = F.Id("w"), i = F.Id("i");
        Formula word = Fn(Call("Fin", n), Call("Option", a));
        return FiniteAlphabet(a, All(z, Fn(Ints(), Call("Option", a)), All(n, Nats(),
            Equal(Call("intFactorSet", z, n), Call("Finset.filter",
                Lam(w, word, Some(i, Ints(), Equal(w, Call("intFactor", z, n, i)))), Named("Finset.univ"))))));
    }

    private static Formula MirrorLinear()
    {
        Formula a = F.Id("A"), x = F.Id("x"), c = F.Id("C"), n = F.Id("n"), k = F.Id("k");
        Formula premise = All(k, Nats(), Le(FactorCount(x, k), Mul(c, Add(k, D(1)))));
        return FiniteAlphabet(a, All(x, Fn(Nats(), a), All(c, Nats(), Arrow(premise,
            All(n, Nats(), Le(MirrorCount(x, n), Mul(Add(Mul(D(2), c), D(1)), Add(n, D(1)))))))));
    }

    private static Formula Transfer()
    {
        Formula a = F.Id("A"), x = F.Id("x"), d = F.Id("D"), b = F.Id("B"), n = F.Id("n"), k = F.Id("k");
        Formula premise = All(k, Nats(), Le(MirrorCount(x, Add(k, D(1))), Add(MirrorCount(x, k), d)));
        return FiniteAlphabet(a, All(x, Fn(Nats(), a), All(d, Nats(), Arrow(premise,
            Some(b, Nats(), All(n, Nats(), Le(Difference(x, n), b)))))));
    }
}
