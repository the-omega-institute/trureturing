using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class NarayanExpandedGeneratorDeltaRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/NarayanExpandedGeneratorDeltaRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/narayan2026deltaset");
    private const string Question =
        "Conjecture 18.3 (p. 22) states: “For Sₕ =⟨a,ah,ah+d,ah+2d,...ah+kd ⟩, Δ(Sₕ) = E(e,d)”. ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Expanded generators refute Narayan's delta-set formula by unit-length normalization.",
        H("Expanded generators and factorization lengths"),
        Blocks(
            Node("generators", "The expanded generating tuple", GeneratorFormula(),
                Question + "The index i : Fin (k + 2) retains a at zero and ah at one. All later coordinates are ah + (i.val − 1)d; no displayed generator is removed.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Z", "Coordinate factorizations", FactorizationFormula(),
                "Section 3 (p. 2) states: “Suppose the set of factorizations of n ∈ S is given by Z(n) = { (z₁, z₂, …, zₚ) ∈ ℕᵖ ∣ z₁ n₁ + z₂ n₂ + … + zₚ nₚ = n }”. "
                    + "The p coordinates are indexed from zero by Fin p and take nonnegative integer values, including zero as in the paper's subsequent inequalities. The sum is over every coordinate.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("L", "Length sets", LengthFormula(),
                "Section 3 (p. 3) states: “If z = (z₁, z₂, z₃, …, zₚ) is a factorization of n, then the length of z is given by |z| = z₁ + z₂ + z₃ + … + zₚ”. "
                    + "It continues: “The set of lengths of n is defined by L(n) = {|z| | z ∈ Z(n)} ⊂ ℕ”. "
                    + "Set.image applies the coordinate sum to all factorizations of n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("delta", "Positive consecutive length differences", DeltaFormula(),
                "Definition 3.1 (p. 3) states: “We define the delta set as Δ(Sₕ) = { l₂ − l₁ : l₂,l₁ ∈ L(s), L(s) ∩ (l₁,l₂) = ∅ }”. "
                    + "Here s ranges over all represented natural numbers and l₁ < l₂, so differences are positive and the endpoints are distinct. The final quantified clause excludes every intermediate length. Subtraction is natural-number subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("euclidStep", "Subtractive Euclidean step", StepFormula(),
                "Definition 3.2 (p. 3) states: “We define the subtractive Euclidean Algorithm in this way: Let x₀ and y₀ = (e,d)” and “Recursively define” the next pair as (xᵢ−yᵢ,yᵢ) if xᵢ>yᵢ, (xᵢ,yᵢ−xᵢ) if yᵢ>xᵢ, and “terminate” if xᵢ=yᵢ. "
                    + "The function ite selects its second argument when its first argument holds and its third otherwise. The equal pair is stationary; Prod.fst and Prod.snd are its coordinates.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("euclidState", "Euclidean states", StateFormula(),
                "Definition 3.2 (p. 3) starts with (x₀,y₀)=(e,d) and applies the displayed subtractive step recursively. Retaining the final diagonal pair repeats a state already visited and adds no positive coordinate value.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("E", "Values visited by the Euclidean algorithm", EuclidFormula(),
                "The abstract (p. 1) states: “Writing e=h−1 and letting E(e,d) denote the set of values arising from the subtractive Euclidean algorithm applied to e and d”. "
                    + "The set contains the positive coordinates of all states, including the initial and terminal states.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 18.3", Disp(Equal(Call("claim"), Parenthesized(ClaimBody()))),
                Question + "Section 3 (p. 2) assumes “gcd(a,d) =1, 1<k<a, h > 1” and sets “e =h−1.” All four parameters are positive natural numbers; Nat.Coprime expresses the stated greatest-common-divisor condition. The equality uses every coordinate of the expanded tuple.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The expanded-generator equality is false", Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "Take (a,h,d,k)=(3,2,2,2), whose expanded tuple is (3,6,8,10). For every positive a coprime to 2, the tuple (a,2a,2a+2,…,4a−2) has delta set {1}. "
                    + "Replacing 2a by two copies of a, and replacing two other occurrences according to their index sum, preserves value and increases length by one. Strong induction on value minus length reaches a terminal factorization. Coprimality makes that endpoint unique by its residue modulo a; induction on a rewrite trace supplies every intervening length. "
                    + "Thus no larger consecutive gap occurs. Lengths 1 and 2 both occur at value 2a. At a=3 this contradicts the initial Euclidean value 2 ∈ E(1,2). The equality for the tuple omitting ah and the catenary conjectures are separate assertions.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("narayan-delta-set"), ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("narayan-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => Apply(Named(name), args);
    private static Formula Apply(Formula function, params Formula[] args) =>
        args.Length == 0 ? function : new Formula.Apply(function, [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Named(owner), Dot, Named(name)) : Apply(Seq(Named(owner), Dot, Named(name)), args);
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Fun(string name, Formula type, Formula body) =>
        Seq(Named("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula FinType(Formula n) => Call("Fin", n);
    private static Formula Vector(Formula n) => new Formula.TypeArrow(FinType(n), Nat());
    private static Formula Pair(Formula x, Formula y) => Parenthesized(Seq(x, Comma, Sp, y));
    private static Formula PairType() => Seq(Nat(), Sp, Times, Sp, Nat());
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, F.Id(name), Sp, Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula SumOver(Formula p, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id("i"), Sp, Colon, Sp, FinType(p))), Sp, Parenthesized(body));

    private static Formula GeneratorFormula()
    {
        var a = F.Id("a"); var h = F.Id("h"); var d = F.Id("d"); var k = F.Id("k"); var i = F.Id("i");
        var value = Call("val", i);
        return Disp(All("a", Nat(), All("h", Nat(), All("d", Nat(), All("k", Nat(),
            All("i", FinType(Add(k, D(2))), Equal(Call("generators", a, h, d, k, i),
                Call("ite", Equal(value, D(0)), a, Add(Mul(a, h), Mul(Subtract(value, D(1)), d))))))))));
    }

    private static Formula FactorizationFormula()
    {
        var p = F.Id("p"); var g = F.Id("g"); var n = F.Id("n"); var z = F.Id("z"); var i = F.Id("i");
        return Disp(All("p", Nat(), All("g", Vector(p), All("n", Nat(),
            Equal(Call("Z", g, n), SetOf("z", Vector(p), Equal(SumOver(p, Mul(Apply(z, i), Apply(g, i))), n)))))));
    }

    private static Formula LengthFormula()
    {
        var p = F.Id("p"); var g = F.Id("g"); var n = F.Id("n");
        return Disp(All("p", Nat(), All("g", Vector(p), All("n", Nat(), Equal(Call("L", g, n),
            Qualified("Set", "image", Fun("z", Vector(p), SumOver(p, Apply(F.Id("z"), F.Id("i")))), Call("Z", g, n)))))));
    }

    private static Formula DeltaFormula()
    {
        var p = F.Id("p"); var g = F.Id("g"); var n = F.Id("n"); var q = F.Id("q");
        var lo = F.Id("lone"); var hi = F.Id("ltwo"); var l = F.Id("l");
        var lengths = Call("L", g, n);
        var gap = All("l", Nat(), Imp(Member(l, lengths), new Formula.Not(Parenthesized(And(Lt(lo, l), Lt(l, hi))))));
        var body = Ex("n", Nat(), Ex("lone", Nat(), Ex("ltwo", Nat(),
            And(Member(lo, lengths), And(Member(hi, lengths), And(Lt(lo, hi), And(Equal(q, Subtract(hi, lo)), gap)))))));
        return Disp(All("p", Nat(), All("g", Vector(p), Equal(Call("delta", g), SetOf("q", Nat(), body)))));
    }

    private static Formula StepFormula()
    {
        var s = F.Id("s"); var x = Qualified("Prod", "fst", s); var y = Qualified("Prod", "snd", s);
        return Disp(All("s", PairType(), Equal(Call("euclidStep", s), Call("ite", Lt(y, x),
            Pair(Subtract(x, y), y), Call("ite", Lt(x, y), Pair(x, Subtract(y, x)), s)))));
    }

    private static Formula StateFormula()
    {
        var e = F.Id("e"); var d = F.Id("d"); var i = F.Id("i");
        return Disp(All("e", Nat(), All("d", Nat(), And(Equal(Call("euclidState", e, d, D(0)), Pair(e, d)),
            All("i", Nat(), Equal(Call("euclidState", e, d, Add(i, D(1))), Call("euclidStep", Call("euclidState", e, d, i))))))));
    }

    private static Formula EuclidFormula()
    {
        var e = F.Id("e"); var d = F.Id("d"); var q = F.Id("q"); var state = Call("euclidState", e, d, F.Id("i"));
        return Disp(All("e", Nat(), All("d", Nat(), Equal(Call("E", e, d), SetOf("q", Nat(),
            And(Lt(D(0), q), Ex("i", Nat(), Or(Equal(Qualified("Prod", "fst", state), q), Equal(Qualified("Prod", "snd", state), q)))))))));
    }

    private static Formula ClaimBody()
    {
        var a = F.Id("a"); var h = F.Id("h"); var d = F.Id("d"); var k = F.Id("k");
        var equality = Equal(Call("delta", Call("generators", a, h, d, k)), Call("E", Subtract(h, D(1)), d));
        return All("a", Nat(), All("h", Nat(), All("d", Nat(), All("k", Nat(),
            Imp(Lt(D(0), a), Imp(Lt(D(0), h), Imp(Lt(D(0), d), Imp(Lt(D(0), k),
                Imp(Qualified("Nat", "Coprime", a, d), Imp(Lt(D(1), k), Imp(Lt(k, a), Imp(Lt(D(1), h), equality))))))))))));
    }
}
