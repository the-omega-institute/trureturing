using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class PronkoFredkinAntiAdjointExpansionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/pronko2025fredkin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The total spin operators and the anti-adjoint action are defined on the spin-word basis of the periodic Fredkin chain. Pronko's nonlocal raising and lowering operators are then finite anti-adjoint expansions of the total spin operators, with one family of coefficients for both signs and every number of sites.",
        H("Pronko's operators as finite anti-adjoint expansions"),
        Blocks(
            DefinitionNode("antiAd", "The anti-adjoint action", AntiAdFormula(),
                "For square complex matrices a and b indexed by spin words, the anti-adjoint action of a on b is the anticommutator a b + b a, as printed with Conjecture 2."),
            DefinitionNode("totalPlus", "The total raising operator", TotalPlusFormula(),
                "The total raising operator is the sum over every site j in Fin N of the one-site raising matrix sigmaPlus acting at site j, matching the normalization chosen in section 2.1 without a factor one half."),
            DefinitionNode("totalMinus", "The total lowering operator", TotalMinusFormula(),
                "The total lowering operator is the sum over every site j in Fin N of the one-site lowering matrix sigmaMinus acting at site j."),
            DefinitionNode("claim", "Pronko's Conjecture 2", ClaimDefinitionFormula(),
                "For every number of sites N there is a single complex coefficient family gamma indexed by Fin of the floor of (N + 1)/2, which equals the ceiling of N/2. The Lean index k corresponds to the printed index k + 1, so the exponent k of the iterated map is the printed exponent k - 1. For the raising sign the iterated map sends X to the anti-adjoint action of totalPlus N on the anti-adjoint action of totalMinus N on X, applied to totalPlus N; for the lowering sign the two total spin operators are exchanged. Sigma N 1 and Sigma N (-1) are the operators of equation (3.1). The printed table lists the coefficients for N from 3 to 10; the statement covers every natural number N."),
            TheoremNode("result", "Conjecture 2 holds", ClaimFormula(),
                "For spin words y and x let b count the sites with y up and x down, and c the sites with y down and x up. Let Z_r be the matrix with entry one exactly when b = r + 1 and c = r, and E_s the matrix with entry one exactly when b = c = s. Summing single-site flips site by site gives the anticommutator identities {S^-, Z_r} = 2(r + 1) E_(r+1) + (N - 2r) E_r and {S^+, E_s} = 2(s + 1) Z_s + (N - 2s + 1) Z_(s-1), where the counts of sites with equal letters combine to N - b - c. Composing them, the map X to {S^+, {S^-, X}} sends Z_r to 4(r + 1)(r + 2) Z_(r+1) + 2(r + 1)(2N - 4r - 1) Z_r + (N - 2r)(N - 2r + 1) Z_(r-1). The case s = 0 gives S^+ = Z_0 because E_0 is the identity, and the leading coefficient 4(r + 1)(r + 2) is nonzero, so by induction on r each Z_r lies in the span of the first r + 1 iterates of that map applied to S^+. Reading the Kronecker sum (3.1) entrywise gives Sigma^+(y, x) = 1 exactly when b - c = 1, and b + c is at most N, so Sigma^+ is the sum of Z_r over r below the ceiling of N/2 and lies in the span of the first ceiling of N/2 iterates, which yields the coefficients. Transposition exchanges sigmaPlus with sigmaMinus, maps Sigma^+ to Sigma^- and each raising iterate to the corresponding lowering iterate, so the same coefficients give the lowering identity."))),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation"))]));

    private static DocumentBlock DefinitionNode(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("pronko-antiadjoint-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static DocumentBlock TheoremNode(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("pronko-antiadjoint-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula ComplexNumbers() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Named(string name)
    {
        var tokens = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count > 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Negative(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Config(Formula n) => new Formula.TypeArrow(Fin(n), Fin(D(2)));
    private static Formula SpinMatrix(Formula n) => Call("Matrix", Config(n), Config(n), ComplexNumbers());
    private static Formula HalfCeiling(Formula n) =>
        new Formula.Floor(new Formula.Fraction(Add(n, D(1)), D(2)));

    private static Formula AntiAdFormula()
    {
        Formula n = F.Id("N"), a = F.Id("a"), b = F.Id("b");
        Formula body = Equal(Call("antiAd", a, b), Add(Multiply(a, b), Multiply(b, a)));
        return Disp(All("N", Naturals(), All("a", SpinMatrix(n), All("b", SpinMatrix(n), body))));
    }

    private static Formula TotalFormula(string name, string local)
    {
        Formula n = F.Id("N"), j = F.Id("j");
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(j, Sp, InMacro, Sp, Fin(n))),
            Sp, Parenthesized(Call("site", n, j, F.Id(local))));
        return Disp(All("N", Naturals(), Equal(Call(name, n), sum)));
    }

    private static Formula TotalPlusFormula() => TotalFormula("totalPlus", "sigmaPlus");

    private static Formula TotalMinusFormula() => TotalFormula("totalMinus", "sigmaMinus");

    private static Formula Expansion(Formula n, Formula sign, string first, string second)
    {
        Formula gamma = F.Id("gamma"), k = F.Id("k"), x = F.Id("X");
        Formula stepMap = Parenthesized(Seq(x, Sp, Mapsto, Sp,
            Call("antiAd", Call(first, n), Call("antiAd", Call(second, n), x))));
        Formula iterate = Call("Nat.iterate", stepMap, k, Call(first, n));
        Formula summand = Multiply(new Formula.Apply(gamma, [k]), iterate);
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(k, Sp, InMacro, Sp, Fin(HalfCeiling(n)))),
            Sp, Parenthesized(summand));
        return Equal(Call("Sigma", n, sign), sum);
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("N");
        Formula plus = Expansion(n, D(1), "totalPlus", "totalMinus");
        Formula minus = Expansion(n, Negative(D(1)), "totalMinus", "totalPlus");
        Formula coefficients = new Formula.TypeArrow(Fin(HalfCeiling(n)), ComplexNumbers());
        return All("N", Naturals(), Some("gamma", coefficients, And(plus, minus)));
    }

    private static Formula ClaimDefinitionFormula() => Disp(
        new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));

    private static Formula ClaimFormula() => Disp(ClaimBody());
}
