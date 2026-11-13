using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class NathansonLatticeRootRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/NathansonLatticeRootRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/nathanson2026latticesumsets");

    private const string Question = "Problem 3 (p. 3) asks: “Let N(h,k) be the smallest positive integer such that ” "
        + "R_Z(h,k) = {|hA| : A ⊆ [0,N(h,k)] and |A| = k}. "
        + "“and let N_n(h,k) be the smallest positive integer such that ” "
        + "R_Z(h,k) = {|hA| : A ⊆ [0,N_n(h,k)]^n and |A| = k}. "
        + "“Prove or disprove the following inequality:” N_n(h,k) ≤ N(h,k)^(1/n). ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full two-fold triple range gives interval diameter three and square diameter two.",
        H("A counterexample to the exact lattice-root bound"),
        Blocks(
            Node("integerRange", "The complete integer range", IntegerRangeFormula(),
                "The source defines the h-fold sumset using “h not necessarily distinct elements of A” (p. 1). "
                + "Its range is R_X(h,k) = {|hA| : A ⊆ X and |A| = k}. Here X is the integers, "
                + "and Finset enumerates every finite k-element subset. The operation nsmulRec is repeated "
                + "pointwise addition, with the zero-fold sumset {0}; it permits repeated summands.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("cube", "The inclusive integer lattice cube", CubeFormula(),
                "Theorem 1 (pp. 1–2) equates the ordinary integer and lattice-point ranges. "
                + "The cube in Problem 3 therefore contains integer-coordinate points. A point is a function "
                + "Fin n → ℤ, and each coordinate belongs to the closed integer interval [0,D]. "
                + "Fintype.piFinset forms the Cartesian product of those intervals; Function.const supplies "
                + "the same coordinate interval at every index.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("intervalCovers", "Covering the whole range in an interval", CoverFormula(false),
                Question + "The diameter D must be positive. Equality of sets of cardinalities requires "
                + "every value in the complete integer range, with all endpoints included.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("cubeCovers", "Covering the same whole range in a cube", CoverFormula(true),
                Question + "The right side ranges over all k-element subsets of the integer lattice cube. "
                + "Both inclusions in this equality are required: witnessing two values alone does not establish it.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("N", "The least positive interval diameter", MinimumFormula(false),
                "Nat.find takes the least natural D satisfying intervalCovers. Its argument H proves that "
                + "such a D exists. Positivity is part of the predicate, so the minimum is a positive integer. "
                + "Nat.find_spec and Nat.find_min' give attainment and leastness. The value is independent "
                + "of the proof H by proof irrelevance.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("Nn", "The least positive lattice-cube diameter", MinimumFormula(true),
                "The same least-natural construction uses the entire common integer range and the "
                + "inclusive n-dimensional lattice cube. Its proof argument supplies existence on the "
                + "declared domain; there is no default diameter and no assumed global inhabitedness.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The full universal exact-root inequality", Disp(Eq(Call("claim"), Par(ClaimBody()))),
                Question + "All h,k ≥ 2 and all n ≥ 1 are quantified. The source's existence of the minima "
                + "is explicit in the existential proof arguments H and J. These are existence conclusions, "
                + "not additional hypotheses restricting h, k or n. The diameter values are cast to real "
                + "numbers and Real.rpow uses exponent 1/n, giving the exact nonnegative nth root. "
                + "There is no ceiling or relaxation of that inequality.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("range_two_three", "The entire triple range is five or six", Disp(Eq(Call("integerRange", D(2), D(3)), Values())),
                "Sort any integer triple as a < b < c. Its pair sums are 2a, a+b, a+c, 2b, b+c, 2c. "
                + "The strict inequalities exclude every collision except a+c = 2b, giving five or six "
                + "distinct values. The sets {0,1,2} and {0,1,3} attain five and six respectively. "
                + "Thus the equality concerns every integer triple, not just these two examples.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("interval_minimum", "The interval minimum is three", Disp(MinimumStatement(false)),
                "At D=3 the two displayed integer triples attain every value in the full range. Conversely "
                + "any positive D<3 lies at most at two. A three-element subset of [0,2] must equal {0,1,2}; "
                + "its pair-sum cardinality is five, so six is missing. This proves attainment and leastness.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("cube_minimum", "The square minimum is two", Disp(MinimumStatement(true)),
                "At D=2 the line {(0,0),(1,0),(2,0)} has five pair sums and the triangle "
                + "{(0,0),(1,0),(0,1)} has six. Exhausting every three-element subset of the finite lattice "
                + "square proves that no other cardinality occurs there. At D=1 the exhaustive check gives "
                + "six for every triple, so five is missing. Geometrically, a midpoint equality in a binary "
                + "coordinate forces both endpoints to equal the midpoint; the unit square admits no "
                + "three distinct points in arithmetic progression. Positivity leaves only D=1 below two.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "The original universal bound is false", Disp(new Formula.Not(Call("claim"))),
                "The covering diameters three and two construct both existence proofs. Leastness then "
                + "identifies the actual values N(2,3)=3 and N_2(2,3)=2, independently of which proofs "
                + "the universal proposition supplies. Its specialization would give 2 ≤ sqrt(3). "
                + "The nonnegative square root has square three, contradicting 2²=4>3. This negates "
                + "the complete universal proposition while proving existence of both minima at the "
                + "counterexample; no failure of existence is used.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("nathanson-2026-problem3-lattice-root-bound"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("nathansonlattice-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string s) => Seq(Operatorname, Grp(F.Id(s)));
    private static Formula App(Formula f, params Formula[] a) => a.Length == 0 ? f : new Formula.Apply(f, [.. a]);
    private static Formula Call(string s, params Formula[] a) => App(Named(s), a);
    private static Formula Q(string owner, string s, params Formula[] a) => App(Seq(Named(owner), Dot, Named(s)), a);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula f, Formula t) => Par(Seq(f, Sp, Colon, Sp, t));
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall, Sp, Typed(F.Id(s), t), Comma, Sp, b);
    private static Formula Ex(string s, Formula t, Formula b) => Seq(Exists, Sp, Typed(F.Id(s), t), Comma, Sp, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Int() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Points(Formula n) => new Formula.TypeArrow(Fin(n), Int());
    private static Formula Card(Formula a) => Q("Finset", "card", a);
    private static Formula Sums(Formula h, Formula a) => Call("nsmulRec", h, a);
    private static Formula Sub(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    private static Formula SetOf(string s, Formula t, Formula p) =>
        Seq(OpenBrace, F.Id(s), Sp, Colon, Sp, t, Sp, Mid, Sp, p, CloseBrace);
    private static Formula Values() => Seq(OpenBrace, D(5), Comma, Sp, D(6), CloseBrace);
    private static Formula Interval(Formula d) => Q("Finset", "Icc", Typed(D(0), Int()), Typed(d, Int()));
    private static Formula Cover(bool square, Formula h, Formula k, Formula n, Formula d) =>
        square ? Call("cubeCovers", h, k, n, d) : Call("intervalCovers", h, k, d);
    private static Formula Existence(bool square, Formula h, Formula k, Formula n) =>
        Ex("D", Nat(), Cover(square, h, k, n, F.Id("D")));
    private static Formula Minimum(bool square, Formula h, Formula k, Formula n, Formula p) =>
        square ? Call("Nn", h, k, n, p) : Call("N", h, k, p);

    private static Formula IntegerRangeFormula()
    {
        var h = F.Id("h"); var k = F.Id("k"); var a = F.Id("A"); var t = F.Id("t");
        var body = Ex("A", Call("Finset", Int()), And(Eq(Card(a), k), Eq(Card(Sums(h, a)), t)));
        return Disp(All("h", Nat(), All("k", Nat(), Eq(Call("integerRange", h, k), SetOf("t", Nat(), body)))));
    }

    private static Formula CubeFormula()
    {
        var n = F.Id("n"); var d = F.Id("D");
        var intervals = Q("Function", "const", Fin(n), Interval(d));
        return Disp(All("n", Nat(), All("D", Nat(), Eq(Call("cube", n, d), Q("Fintype", "piFinset", intervals)))));
    }

    private static Formula CoverFormula(bool square)
    {
        var h = F.Id("h"); var k = F.Id("k"); var n = F.Id("n");
        var d = F.Id("D"); var a = F.Id("A"); var t = F.Id("t");
        var bounded = square ? Call("cube", n, d) : Interval(d);
        var witnesses = Ex("A", Call("Finset", square ? Points(n) : Int()),
            And(Eq(Card(a), k), And(Sub(a, bounded), Eq(Card(Sums(h, a)), t))));
        var body = Eq(Cover(square, h, k, n, d),
            Par(And(Lt(D(0), d), Eq(Call("integerRange", h, k), SetOf("t", Nat(), witnesses)))));
        body = All("D", Nat(), body);
        if (square) body = All("n", Nat(), body);
        return Disp(All("h", Nat(), All("k", Nat(), body)));
    }

    private static Formula MinimumFormula(bool square)
    {
        var h = F.Id("h"); var k = F.Id("k"); var n = F.Id("n"); var p = F.Id("H");
        var body = All("H", Existence(square, h, k, n),
            Eq(Minimum(square, h, k, n, p), Q("Nat", "find", p)));
        if (square) body = All("n", Nat(), body);
        return Disp(All("h", Nat(), All("k", Nat(), body)));
    }

    private static Formula ClaimBody()
    {
        var h = F.Id("h"); var k = F.Id("k"); var n = F.Id("n");
        var root = new Formula.Power(Typed(Minimum(false, h, k, n, F.Id("H")), Real()),
            new Formula.Fraction(D(1), Typed(n, Real())));
        Formula body = Le(Typed(Minimum(true, h, k, n, F.Id("J")), Real()), root);
        body = Ex("H", Existence(false, h, k, n), Ex("J", Existence(true, h, k, n), body));
        body = Imp(Le(D(2), h), Imp(Le(D(2), k), Imp(Le(D(1), n), body)));
        return All("h", Nat(), All("k", Nat(), All("n", Nat(), body)));
    }

    private static Formula MinimumStatement(bool square)
    {
        var d = F.Id("D"); var m = square ? D(2) : D(3);
        return And(Cover(square, D(2), D(3), D(2), m),
            All("D", Nat(), Imp(Cover(square, D(2), D(3), D(2), d), Le(m, d))));
    }
}
