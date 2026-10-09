using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class AlternatingAdjacentSumGorensteinDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Geometry/AlternatingAdjacentSumGorenstein.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/jiangwenzhong2026alternating");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For s at least two, the alternating adjacent-sum polytope in dimension 2r is Gorenstein exactly when s = 3 and r = 1.",
        H("Gorenstein pairs for alternating adjacent-sum polytopes"),
        Blocks(
            Node("polytope", "The alternating adjacent-sum polytope", "P", PolytopeFormula(),
                "Section 1, equation (1), p. 2, reads: “For integers d ≥ 2 and s ≥ 1, define” followed by P_d^(s) = {x = (x₁,…,x_d) ∈ ℝ^d_{≥0} : x_i + x_{i+1} ≤ s + δ_i, 1 ≤ i ≤ d − 1}, and “where δ_i = 0 for i odd and δ_i = 1 for i even.” Coordinates in Fin d start at zero, so the capacity at i is s + ite((val(i) + 1) % 2 = 0, 1, 0). Here ite is Lean's conditional and % is natural-number remainder. The pair i,j with val(j) = val(i) + 1 gives exactly the paper's adjacent constraints. The formula also defines the set for other natural parameters; the theorem uses s ≥ 2 and d = 2r ≥ 2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("gorenstein", "Interior lattice points and translation", "IsGorenstein", GorensteinFormula(),
                "The proof of Theorem 1.9, p. 44, states: “We use the standard interior-lattice-point characterization of Gorenstein lattice polytopes; see, for example, [13, 7].” It gives int((n + 3)T₁^r) ∩ ℤ^(2r) = c_r + (nT₁^r ∩ ℤ^(2r)) for all n ≥ 0. Here the same characterization allows any positive natural index q and integral translation c. The ambient interior is Mathlib's interior in Fin d → ℝ. The operator smul is the real scalar action on sets, including the actual zero dilation. The pointwise casts of x and x − c embed the integral lattice in that real space. Parenthesized ascriptions to ℝ denote these canonical casts; no change of lattice or relative interior is used.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Question Q1 and its answer", "claim", ClaimFormula(),
                "Question Q1, §4, p. 48, reads: “Theorem 1.9, Proposition 3.21, and Corollary 3.24 show that s = 1 yields an infinite Gorenstein family, whereas every s ≥ 2 eventually fails. For s = 3, direct computation (Propositions 3.22 and 3.23) shows that only d = 2 is Gorenstein in even dimensions d ≤ 6; we conjecture this extends to all d ≥ 4. Characterize all (s, r) with s ≥ 2 for which P_{2r}^(s) is Gorenstein.” The natural parameter r is positive, and the displayed claim supplies the complete answer to the characterization question: precisely s = 3 and r = 1.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "The unique Gorenstein pair", "result", Disp(F.Id("claim")),
                "At n = 0 the translation identity makes the interior lattice point of qP unique. Positivity forces each coordinate of c to be at least one and qs ≥ 3. The all-ones point is interior, so uniqueness gives c = 1. If qs ≥ 4, the point (2,1,…,1) is a second interior lattice point. Thus qs = 3, and s ≥ 2 forces q = 1 and s = 3. In every dimension d ≥ 3, the integral point (1,4,3,1,…,1) belongs to the interior of 2P: its adjacent sums are 5, 7, 4, 2, …, below the alternating capacities 6, 8, 6, 8, …. After subtracting one, its second adjacent sum is 5, exceeding capacity 4. This contradicts the n = 1 translation identity. In dimension two, q = 1 and c = (1,1) give the required identity for every n, including n = 0. The classification concerns the stated lattice-translation characterization; no assertion about unimodality or real-rootedness is needed.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("alternating-adjacent-sum-" + id),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula EqTo(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LeTo(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula PlusOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula TimesOf(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Point(Formula d, Formula scalar) =>
        new Formula.TypeArrow(Call("Fin", d), scalar);
    private static Formula RealCast(Formula value) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, Reals()));
    private static Formula Member(Formula x, Formula set) => Seq(x, Sp, InMacro, Sp, set);
    private static Formula Scale(Formula t, Formula set) =>
        Call("smul", t, set);

    private static Formula PolytopeFormula()
    {
        Formula s = F.Id("s"), d = F.Id("d"), x = F.Id("x"), i = F.Id("i"), j = F.Id("j");
        Formula fi = Call("Fin", d);
        Formula adjacent = EqTo(Call("val", j), PlusOf(Call("val", i), D(1)));
        Formula parity = EqTo(new Formula.Modulo(PlusOf(Call("val", i), D(1)), D(2)), D(0));
        Formula capacity = PlusOf(RealCast(s), Call("ite", parity, D(1), D(0)));
        Formula condition = And(All("i", fi, LeTo(D(0), new Formula.Apply(x, [i]))),
            All("i", fi, All("j", fi, Imp(adjacent,
                LeTo(PlusOf(new Formula.Apply(x, [i]), new Formula.Apply(x, [j])), capacity)))));
        Formula set = Seq(OpenBrace, x, Sp, Colon, Sp, Parenthesized(Point(d, Reals())),
            Sp, Mid, Sp, condition, CloseBrace);
        return Disp(All("s", Nat(), All("d", Nat(), EqTo(Call("P", s, d), set))));
    }

    private static Formula GorensteinFormula()
    {
        Formula s = F.Id("s"), d = F.Id("d"), q = F.Id("q"), c = F.Id("c"),
            n = F.Id("n"), x = F.Id("x"), i = F.Id("i");
        Formula polytope = Call("P", s, d);
        Formula integralPoint = Point(d, Ints());
        Formula latticeX = Parenthesized(Seq(LambdaLower, Sp, i, Sp, Colon, Sp, Call("Fin", d),
            Sp, Mapsto, Sp, RealCast(new Formula.Apply(x, [i]))));
        Formula difference = new Formula.Binary(x, FormulaBinaryOperator.Subtract, c);
        Formula latticeDifference = Parenthesized(Seq(LambdaLower, Sp, i, Sp, Colon, Sp,
            Call("Fin", d), Sp, Mapsto, Sp,
            RealCast(new Formula.Apply(difference, [i]))));
        Formula equivalence = IffTo(
            Member(latticeX, Call("interior", Scale(RealCast(PlusOf(n, q)), polytope))),
            Member(latticeDifference, Scale(RealCast(n), polytope)));
        Formula body = Some("q", Nat(), And(LeTo(D(1), q), Some("c", integralPoint,
            All("n", Nat(), All("x", integralPoint, equivalence)))));
        return Disp(All("s", Nat(), All("d", Nat(), IffTo(Call("IsGorenstein", s, d), body))));
    }

    private static Formula ClaimFormula()
    {
        Formula s = F.Id("s"), r = F.Id("r");
        Formula body = All("s", Nat(), All("r", Nat(), Imp(LeTo(D(2), s), Imp(LeTo(D(1), r),
            IffTo(Call("IsGorenstein", s, TimesOf(D(2), r)),
                And(EqTo(s, D(3)), EqTo(r, D(1))))))));
        return Disp(IffTo(F.Id("claim"), body));
    }
}
