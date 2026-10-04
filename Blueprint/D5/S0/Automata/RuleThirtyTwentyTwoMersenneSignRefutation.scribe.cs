using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class RuleThirtyTwentyTwoMersenneSignRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Automata/RuleThirtyTwentyTwoMersenneSignRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Rewriting/chanlopezmartinruiz2026rule30");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refutes the Rule 30/22 Mersenne sign pattern at row 767.",
        H("A non-Mersenne exception to the Rule 30/22 sign pattern"),
        Blocks(
            Node("row", "Single-seed evolution", RowFormula(),
                "The whole integer lattice evolves synchronously from one active cell at the origin. "
                    + "The arguments of g are the left neighbour, centre and right neighbour, in that order. "
                    + "The value true means an active cell; decide converts a proposition to Bool. "
                    + "Section 3, p. 4, fixes the configuration evolved \"from the single-seed initial condition η_0 = δ_0\".",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("g30", "Rule 30", RuleFormula("g30", false),
                "Proposition 1, p. 3: \"Rule 30, with ANF g30 = a ⊕ b ⊕ c ⊕ bc, is left-permutive but lacks S3 symmetry.\" "
                    + "Here xor is Bool XOR and and is Bool AND, so they implement addition and multiplication over F2. "
                    + "Boolean exclusive-or is nested to the left as displayed, with the conjunction of the centre and right bits as its final argument.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("g22", "Rule 22", RuleFormula("g22", true),
                "Equation (1), p. 3: \"g22(a, b, c) = a ⊕ b ⊕ c ⊕ abc.\" "
                    + "Boolean exclusive-or and conjunction are nested to the left as displayed.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("supportCard", "Full-row support cardinality", SupportFormula(),
                "Definition 2, p. 4: \"The support set at time m is the full-row support S_m = {r ∈ Z : η_m(r) = 1}\". "
                    + "The same page specifies: \"All cardinality statements below refer to the full-row set S_m\". "
                    + "This counts every active integer site, including negative sites and the origin, rather than the right-half support. "
                    + "The operator ncard is Set.ncard. Both rules send the all-false neighbourhood to false; "
                    + "induction bounds their support by the finite interval [-m,m].",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("eps", "The symmetry-breaking deviation", EpsFormula(),
                "Equation (11), p. 10: \"ϵ(m) = |S_m^(30)| − |S_m^(22)|\". "
                    + "The formula casts each natural cardinality to the integers before subtraction, preserving negative values. "
                    + "The function eps is the paper's ϵ and uses the two full-row supports.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The sign-pattern question", ClaimFormula(),
                "Remark 3, p. 11: \"A direct computation for m ≤ 256 shows that ϵ(m) ≤ 0 precisely at the Mersenne indices m = 2^k − 1, "
                    + "with ϵ = 0 for k ≤ 3 and ϵ < 0 for 4 ≤ k ≤ 8.\" Section 9, p. 15, asks: "
                    + "\"Is the sign pattern of Remark 3 exact for all k?\" "
                    + "The proposition extends the 'precisely' biconditional to every natural row index m at least one. "
                    + "The exponent k is a natural number at least one, and the subtraction in 2^k - 1 is natural subtraction. "
                    + "The separate assertion of strict negativity at every Mersenne index with k at least four is not part of this proposition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The sign pattern is false", F.Disp(F.Seq(F.Neg, F.Sp, Id("claim"))),
                "At row 767, Rule 30 has 763 active cells and Rule 22 has 768, so eps(767) = -5. "
                    + "But 767 is not a Mersenne index: 512 < 768 < 1024 excludes 768 being a power of two. "
                    + "For a quiescent rule, a light-cone induction proves that the row vanishes outside [-m,m]. "
                    + "A second induction identifies row g m r with bit r+m of the m-fold bitwise step starting at 1, with negative bit positions set to false. "
                    + "The map i ↦ (i : Z)-m identifies the active bits below 2m+1 with the full-row support and preserves cardinality. "
                    + "For Rule 30 the encoded step is the exclusive-or of b shifted left by two bits with the bitwise union of b shifted left by one bit and b. "
                    + "For Rule 22 it is the exclusive-or of b shifted left by two bits, b shifted left by one bit, b, and their three-way bitwise intersection. "
                    + "Evaluating these exact recurrences and counting the 1535 possible bits gives the two cardinalities. "
                    + "This disproves the only-if direction. It does not determine the signs at all Mersenne indices or the recurrence of other exceptions.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chan-lopez-martin-ruiz-2026-rule30-sign-pattern"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string declaration, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("rule30-rule22-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Naturals() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Booleans() => Id("Bool");
    private static Formula RuleType() => Parenthesized(new Formula.TypeArrow(Booleans(),
        new Formula.TypeArrow(Booleans(), new Formula.TypeArrow(Booleans(), Booleans()))));
    private static Formula Parenthesized(Formula value) => F.Seq(F.Open, value, F.Close);
    private static Formula QualifiedCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(F.Seq(F.Id(owner), F.Dot, F.Id(name)), [.. args]);
    private static Formula AsInt(Formula value) =>
        Parenthesized(F.Seq(value, F.Colon, new Formula.Integers()));
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula RowFormula()
    {
        Formula g = Id("g"), m = Id("m"), r = Id("r");
        var start = All("g", RuleType(), All("r", new Formula.Integers(),
            Equal(Call("row", g, Num(0), r), Call("decide", Equal(r, Num(0))))));
        var step = All("g", RuleType(), All("m", Naturals(), All("r", new Formula.Integers(),
            Equal(Call("row", g, Add(m, Num(1)), r),
                new Formula.Apply(g, [Call("row", g, m, Subtract(r, Num(1))),
                    Call("row", g, m, r), Call("row", g, m, Add(r, Num(1)))])))));
        return F.Disp(new Formula.Aligned([Parenthesized(start), Parenthesized(step)]));
    }

    private static Formula RuleFormula(string rule, bool cubic)
    {
        Formula a = Id("a"), b = Id("b"), c = Id("c");
        var monomial = cubic ? Call("and", Call("and", a, b), c) : Call("and", b, c);
        var expression = Call("xor", Call("xor", Call("xor", a, b), c), monomial);
        return F.Disp(All("a", Booleans(), All("b", Booleans(), All("c", Booleans(),
            Equal(Call(rule, a, b, c), expression)))));
    }

    private static Formula SupportFormula()
    {
        Formula g = Id("g"), m = Id("m"), r = Id("r");
        var support = F.Seq(F.OpenBrace, r, F.Colon, new Formula.Integers(), F.Mid,
            Equal(Call("row", g, m, r), Id("true")), F.CloseBrace);
        return F.Disp(All("g", RuleType(), All("m", Naturals(),
            Equal(Call("supportCard", g, m), QualifiedCall("Set", "ncard", support)))));
    }

    private static Formula EpsFormula()
    {
        Formula m = Id("m");
        return F.Disp(All("m", Naturals(), Equal(Call("eps", m),
            Subtract(AsInt(Call("supportCard", Id("g30"), m)),
                AsInt(Call("supportCard", Id("g22"), m))))));
    }

    private static Formula ClaimFormula()
    {
        Formula m = Id("m"), k = Id("k");
        var mersenne = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("k"),
            Naturals(), And(LessEqual(Num(1), k),
                Equal(m, Subtract(new Formula.Power(Num(2), k), Num(1)))));
        var biconditional = new Formula.Logic(LessEqual(Call("eps", m), Num(0)),
            FormulaLogicOperator.Iff, Parenthesized(mersenne));
        var body = All("m", Naturals(), new Formula.Logic(LessEqual(Num(1), m),
            FormulaLogicOperator.Implies, Parenthesized(biconditional)));
        return F.Disp(Equal(Id("claim"), Parenthesized(body)));
    }
}
