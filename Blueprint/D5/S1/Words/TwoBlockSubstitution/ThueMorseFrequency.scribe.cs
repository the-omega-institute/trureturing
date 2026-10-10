using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.TwoBlockSubstitution;

internal sealed class ThueMorseFrequencyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/TwoBlockSubstitution/ThueMorseFrequency.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/dekking2022twoblock");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Thue-Morse two-block fixed point has one-letter frequency one half.",
        H("Thue-Morse two-block frequency"), Blocks(
            Node("kappaTM", "The two-block substitution", Table(),
                "Section 4 of v1, p. 5: “We consider the two-block substitution κTM defined by κTM(00) = 001, κTM(01) = 010, κTM(10) = 101, κTM(11) = 110.” The letters 0 and 1 are false and true. The vector notation ![a,b,c] denotes a function Fin 3 → Bool, with indices 0, 1 and 2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("tmFixed", "The fixed point with prefix 00", Fixed(),
                "Section 4 of v1, p. 5: “The fixed point x = x⁽⁰⁰⁾ = x₀x₁ . . . of the two-block morphism κTM with prefix 00 satisfies very similar recurrence relations: x₃ₙ = x₂ₙ, x₃ₙ₊₁ = x₂ₙ₊₁, x₃ₙ₊₂ = 1 − x₂ₙ₊₁.” Natural indices start at zero. The well-founded recursion evaluates the residue first. Nat.div is natural integer division and Nat.mod is its remainder; ite selects its then or else branch. The angle-bracket argument is the Fin 3 index with its bound proof suppressed. The recursion yields exactly the displayed source relations, including the initial cases.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Dekking–Keane Conjecture 4", Iff(Named("claim"), Limit()),
                "Conjecture 4 of v1, Section 4, p. 6: “The frequency of 1 in x⁽⁰⁰⁾ exists and equals ½.” The encoding counts true letters at indices n < N. Finset.filter selects those indices from Finset.range N, and Finset.card counts them. Both the cardinality and N are cast to ℝ before division; the quotient at N = 0 does not affect the limit. ArXiv v2 and the journal version change the substitution; this assertion uses the v1 table.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The frequency is one half", Named("claim"),
                "For signs 1 − 2xₙ, one substitution step maps a pair (u,v) to (u,v,−v). After k steps, its coefficient functional is periodic modulo 2ᵏ. Multiplication by 3 permutes those residues, and the adjacent correlation sums cancel. The squared coefficient energy is 3ᵏ⁻¹ for k ≥ 1. Finite Cauchy–Schwarz bounds each aligned block sum by √(2ᵏ3ᵏ⁻¹). Splitting a prefix into aligned blocks and a bounded remainder makes the signed mean tend to zero, giving the asserted frequency.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Table() => new Formula.Aligned([
        Seq(Named("kappaTM"), Colon, new Formula.TypeArrow(Named("Bool"),
            new Formula.TypeArrow(Named("Bool"), new Formula.TypeArrow(Call("Fin", D(3)), Named("Bool"))))),
        Eq(Call("kappaTM", Named("false"), Named("false")), Vector(false, false, true)),
        Eq(Call("kappaTM", Named("false"), Named("true")), Vector(false, true, false)),
        Eq(Call("kappaTM", Named("true"), Named("false")), Vector(true, false, true)),
        Eq(Call("kappaTM", Named("true"), Named("true")), Vector(true, true, false))]);

    private static Formula Fixed()
    {
        var n = F.Id("n");
        var m = Add(n, D(2));
        var q = Call("Nat.div", m, D(3));
        var r = Call("Nat.mod", m, D(3));
        var even = Call("tmFixed", Mul(D(2), q));
        var odd = Call("tmFixed", Add(Mul(D(2), q), D(1)));
        return new Formula.Aligned([
            Seq(Named("tmFixed"), Colon, new Formula.TypeArrow(Nat(), Named("Bool"))),
            Eq(Call("tmFixed", D(0)), Named("false")),
            Eq(Call("tmFixed", D(1)), Named("false")),
            All("n", Nat(), Eq(Call("tmFixed", m),
                Call("ite", Eq(r, D(0)), even, Call("kappaTM", even, odd, Seq(Langle, r, Rangle))))) ]);
    }

    private static Formula Limit()
    {
        var n = F.Id("n"); var N = F.Id("N");
        var predicate = Seq(Named("fun"), Sp, n, Colon, Nat(), Sp, Mapsto, Sp, Eq(Call("tmFixed", n), Named("true")));
        var count = Call("Finset.card", Call("Finset.filter", predicate, Call("Finset.range", N)));
        var ratio = new Formula.Fraction(Cast(count), Cast(N));
        var sequence = Seq(Named("fun"), Sp, N, Colon, Nat(), Sp, Mapsto, Sp, ratio);
        return Call("Filter.Tendsto", sequence, Qualified("Filter", "atTop"),
            Call("nhds", Parenthesized(Seq(new Formula.Fraction(D(1), D(2)), Colon, Real()))));
    }

    private static Formula Vector(bool a, bool b, bool c) => Seq(Bang, OpenBracket,
        Named(a ? "true" : "false"), Comma, Sp, Named(b ? "true" : "false"), Comma, Sp,
        Named(c ? "true" : "false"), CloseBracket);
    private static Formula Named(string name) => name switch
    {
        "Nat.div" => Qualified("Nat", "div"),
        "Nat.mod" => Qualified("Nat", "mod"),
        "Bool.not" => Qualified("Bool", "not"),
        "Finset.card" => Qualified("Finset", "card"),
        "Finset.filter" => Qualified("Finset", "filter"),
        "Finset.range" => Qualified("Finset", "range"),
        "Filter.Tendsto" => Qualified("Filter", "Tendsto"),
        _ => Seq(Operatorname, Grp(F.Id(name)))
    };
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, type, Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Colon, Real()));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
}
