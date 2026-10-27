using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Lattices;

internal sealed class BadicaJaccardArbitraryLatticesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Lattices/BadicaJaccardArbitraryLattices.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/badica2026jaccardlattices");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reciprocal supermodularity gives the Jaccard triangle inequality on every lattice.",
        H("The generalized Jaccard triangle inequality on arbitrary lattices"),
        Blocks(
            Node("strictly-positive", "Strictly positive valuations", "IsStrictlyPositive",
                Scope(Equal(Call("IsStrictlyPositive", F.Id("f")), Parenthesized(Positive()))),
                "Definition 3(i), p. 3: ‘If f(X) > 0 for all X ∈ L, then f is strictly positive.’",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("supermodular", "Supermodular valuations", "IsSupermodular", ModularFormula(false),
                "Definition 3(v), p. 3: ‘f is supermodular if and only if: f(X) + f(Y) ≤ f(X ∨ Y) + f(X ∧ Y) ∀X, Y ∈ L’. The symbols ⊔ and ⊓ denote the lattice join and meet.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("submodular", "Submodular valuations", "IsSubmodular", ModularFormula(true),
                "Definition 3(iii), p. 3: ‘f is submodular if and only if: f(X) + f(Y) ≥ f(X ∨ Y) + f(X ∧ Y) ∀X, Y ∈ L’. The displayed inequality places the join and meet terms on the left.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("log-submodular", "Log-submodular valuations", "IsLogSubmodular", LogFormula(),
                "Definition 3(iv), p. 3: ‘If f is strictly positive and log ∘ f is submodular, then f is log-submodular.’ Strict positivity means ‘If f(X) > 0 for all X ∈ L, then f is strictly positive.’ It is expressed by ∀ X, 0 < f X; Real.log is the real logarithm.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("jaccard-distance", "The generalized Jaccard distance", "jaccardDist", DistanceFormula(),
                "Equation (17), p. 5: ‘d_{f,J}(A, B) = 1 − f(A ∧ B)/f(A ∨ B)’. The quotient is real division. The formula is defined for every f; the triangle theorems assume strict positivity.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The second question in Section 8", "claim", ClaimFormula(false),
                "Section 8, p. 12: ‘While we established metricity for supermodular and log-submodular valuations, the proof relies on the lattice being both relatively complemented and distributive. It is still unknown whether the standard generalized Jaccard formula holds up to the triangle inequality for these valuations on arbitrary lattices that lack those two specific traits.’ Here L is an arbitrary lattice, at every universe level, f maps L to ℝ, and A, B, C range over L. Strict positivity, Monotone f, supermodularity and log-submodularity are the hypotheses. No distributivity or complementation is assumed.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim-sufficiency", "The fourth question in Section 8", "claimSufficiency", ClaimFormula(true),
                "Section 8, p. 12: ‘The reverse of this statement remains untested: if f and 1/f are supermodular, is that enough on its own to guarantee the triangle inequality? Also, it is unclear if the stricter log-submodularity constraint used in Theorem 2 is actually required, or if it can be loosened to match the more basic necessary conditions established later in the paper.’ The quantified statement includes strict positivity and Monotone f, as in Theorem 4; the reciprocal is the pointwise function X ↦ (f X)⁻¹.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result-sufficiency", "The necessary conditions suffice", "resultSufficiency", ClaimBody(true),
                "Supermodularity at A ⊓ B and B ⊓ C bounds the sum of their values by f B + f (A ⊓ C). Supermodularity of the reciprocal at A ⊔ B and B ⊔ C bounds the sum of the reciprocal values by 1 / f B + 1 / f (A ⊔ C). Monotonicity also bounds each meet value by f B and each reciprocal join value by 1 / f B. Ordering the two reciprocal weights and splitting at f (A ⊓ C) ≤ f B gives the scalar estimate needed for the triangle inequality. No distributive law or complement enters this argument.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "Log-submodularity also suffices on every lattice", "result", ClaimBody(false),
                "For positive values, log-submodularity gives f (X ⊔ Y) · f (X ⊓ Y) ≤ f X · f Y. Combined with supermodularity, this implies supermodularity of the reciprocal function. The preceding theorem therefore proves the triangle inequality under the hypotheses of the second question. Only the triangle inequality is asserted; separation, a MetricSpace instance and the symmetric-difference question remain outside these statements.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("badica-2026-jaccard-arbitrary-lattices"),
                    ResolutionKind.Proved))
        ), []));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(F.Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Scope(Formula body) => All("L", F.Id("Type"),
        Seq(OpenBracket, Call("Lattice", F.Id("L")), CloseBracket, Comma, Sp,
            All("f", new Formula.TypeArrow(F.Id("L"), Real()), body)));
    private static Formula Positive() => All("X", F.Id("L"), Less(D(0), Call("f", F.Id("X"))));
    private static Formula ModularFormula(bool submodular)
    {
        var x = F.Id("X"); var y = F.Id("Y");
        var sum = Add(Call("f", x), Call("f", y));
        var latticeSum = Add(Call("f", Join(x, y)), Call("f", Meet(x, y)));
        var body = All("X", F.Id("L"), All("Y", F.Id("L"),
            submodular ? LessEqual(latticeSum, sum) : LessEqual(sum, latticeSum)));
        return Scope(Equal(Call(submodular ? "IsSubmodular" : "IsSupermodular", F.Id("f")), Parenthesized(body)));
    }
    private static Formula LogFormula() => Scope(Equal(Call("IsLogSubmodular", F.Id("f")),
        Parenthesized(new Formula.Logic(Call("IsStrictlyPositive", F.Id("f")), FormulaLogicOperator.And,
            Call("IsSubmodular", Seq(Qualified("Real", "log"), Sp, Circ, Sp, F.Id("f")))))));
    private static Formula DistanceFormula() => Scope(All("A", F.Id("L"), All("B", F.Id("L"),
        Equal(Call("jaccardDist", F.Id("f"), F.Id("A"), F.Id("B")),
            new Formula.Binary(D(1), FormulaBinaryOperator.Subtract,
                new Formula.Fraction(Call("f", Meet(F.Id("A"), F.Id("B"))),
                    Call("f", Join(F.Id("A"), F.Id("B")))))))));
    private static Formula ClaimFormula(bool sufficiency) => Equal(
        F.Id(sufficiency ? "claimSufficiency" : "claim"), Parenthesized(ClaimBody(sufficiency)));
    private static Formula ClaimBody(bool sufficiency)
    {
        var f = F.Id("f"); var a = F.Id("A"); var b = F.Id("B"); var c = F.Id("C");
        var lastHypothesis = sufficiency
            ? Call("IsSupermodular", Seq(LambdaLower, Sp, Cast(F.Id("X"), F.Id("L")), Sp,
                Mapsto, Sp, new Formula.Power(Parenthesized(Call("f", F.Id("X"))), new Formula.Negate(D(1)))))
            : Call("IsLogSubmodular", f);
        var triangle = All("A", F.Id("L"), All("B", F.Id("L"), All("C", F.Id("L"),
            LessEqual(Call("jaccardDist", f, a, c),
                Add(Call("jaccardDist", f, a, b), Call("jaccardDist", f, b, c))))));
        return Scope(Implies(Call("IsStrictlyPositive", f), Implies(Call("Monotone", f),
            Implies(Call("IsSupermodular", f), Implies(lastHypothesis, triangle)))));
    }
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LessEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Join(Formula a, Formula b) =>
        new Formula.Apply(Qualified("SemilatticeSup", "sup"), [a, b]);
    private static Formula Meet(Formula a, Formula b) =>
        new Formula.Apply(Qualified("SemilatticeInf", "inf"), [a, b]);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
