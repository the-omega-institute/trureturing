using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class SliwaSevenArbitraryOutcomeLocalBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/SliwaSevenArbitraryOutcomeLocalBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/grandjean2012threesystems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every number K >= 2 of measurement outcomes, the deterministic expression in (B1) has minimum 6(K-1). This settles the local-bound clause alone.",
        H("The local bound of the arbitrary-output Sliwa seventh inequality"),
        Blocks(
            Node("J", "The twelve-term deterministic expression", JFormula(),
                "Appendix B, PDF p. 5, states: “A possible symmetric generalization of Sliwa’s 7th inequality [46] to an arbitrary number of outputs reads as:” The outputs a, b, c encode A_1, B_1, C_1 and A, B, C encode A_2, B_2, C_2, respectively, in ZMod K. The operator val is the least nonnegative residue for K > 0. With S = a+b+c and T = A+B+C, the definition retains all terms and coefficients of (B1). The six mixed brackets completing the party permutations are [-A+b+c]_K, [-B+a+c]_K, [-C+a+b]_K, [-a+B+C]_K, [-b+A+C]_K and [-c+A+B]_K. The first and fourth are the two displayed mixed terms in the source; the other four complete their party permutations. J is natural-valued, and the subtraction K-1 in the bound is natural truncated subtraction; for K >= 2 it agrees with integer subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The local-bound clause of the conjecture", ClaimFormula(),
                "Appendix B, PDF p. 5, gives (B1) verbatim: “2⟨[A_1 + B_1 + C_1]_K⟩ + 2⟨[−A_1 − B_1 − C_1 − 1]_K⟩ + ⟨[−A_1 − B_1 − C_1]_K⟩ + 3⟨[−A_2 − B_2 − C_2 − 1]_K⟩ + ⟨[A_2 + B_2 + C_2 − 1]_K⟩ + ⟨[A_2 + B_2 + C_2]_K⟩ + ⟨[−A_2 + B_1 + C_1]_K⟩ + ⟨[−A_1 + B_2 + C_2]_K⟩ + ⋄ ≥ 6(K − 1), (B1)”. PDF p. 6 states verbatim: “We conjecture that both the local bound and the facet-defining property of inequality (B1) hold for general K.” Only the local-bound clause is encoded and settled here; the facet-defining clause remains open. IsLeast means both that 6(K-1) belongs to the set of deterministic values and that it is no larger than any such value. In Section II, PDF p. 2, fact 1 reads: “It suffices to consider deterministic classical strategies for determining the minimal value of S^{(K)} allowed in a local theory”. A deterministic strategy makes ⟨[X]_K⟩ equal to the residue [X]_K. Local correlations are convex combinations of deterministic strategies, so their values are averages of J and have the same attainable minimum. The convex-mixture interpretation uses the source’s fact 1; the formal statement concerns exactly the deterministic minimum.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The sharp bound for every K", Disp(F.Id("claim")),
                "Put s = val(S), t = val(T), u_1 = val(-A+b+c), u_2 = val(-B+a+c), u_3 = val(-C+a+b). Work with their integer representatives. The remaining mixed residues are v_i = (u_i+t-s) mod K, and the sum U of the first three satisfies U = 2s-t+Kq for an integer q. If t >= s, let h count the residues with u_i+t-s >= K. Then L = sum_i(u_i+v_i) = s+t+K(2q-h); for h = 0, 1, 2, 3, the residue ranges force q >= 0, 1, 2, 2. When s = 0 < t and h = 0, q >= 1. If s > t, let h count the residues with u_i < s-t. Then L = s+t+K(2q+h), with q >= 0, 0, 0, -1 for h = 0, 1, 2, 3. Thus L >= s+t, with L >= s+t+K at s = 0 < t. The pure residues give the integer identity J-6(K-1) = L-s-t+K(1_{t=0}-1_{s=0}). The strengthened estimate handles its only negative correction, proving the lower bound. The all-zero strategy attains 6(K-1). The result supplies the all-K local bound used to compare classical and quantum values of (B1); it establishes no facet, quantum optimum or visibility optimum.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("grandjean-liang-bancal-brunner-gisin-2012-sliwa-seven-local-bound"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("sliwa-local-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessEq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Negate(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Nats() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Zmod(Formula k) => Call("ZMod", k);
    private static Formula Residue(Formula value) => Call("val", value);
    private static Formula Triple(Formula a, Formula b, Formula c) => Add(Add(a, b), c);
    private static Formula Value(Formula k) => Call("J", k, F.Id("a"), F.Id("b"), F.Id("c"), F.Id("A"), F.Id("B"), F.Id("C"));
    private static Formula Outputs(Formula k, Formula body, bool existential)
    {
        foreach (string name in new[] { "C", "B", "A", "c", "b", "a" })
            body = existential ? Some(name, Zmod(k), body) : All(name, Zmod(k), body);
        return body;
    }

    private static Formula JFormula()
    {
        Formula k = F.Id("K"), a = F.Id("a"), b = F.Id("b"), c = F.Id("c"),
            aa = F.Id("A"), bb = F.Id("B"), cc = F.Id("C");
        Formula s = Triple(a, b, c), t = Triple(aa, bb, cc);
        Formula[] terms = [Mul(D(2), Residue(s)), Mul(D(2), Residue(Sub(Negate(s), D(1)))),
            Residue(Negate(s)), Mul(D(3), Residue(Sub(Negate(t), D(1)))),
            Residue(Sub(t, D(1))), Residue(t),
            Residue(Triple(Negate(aa), b, c)), Residue(Triple(Negate(bb), a, c)),
            Residue(Triple(Negate(cc), a, b)), Residue(Triple(Negate(a), bb, cc)),
            Residue(Triple(Negate(b), aa, cc)), Residue(Triple(Negate(c), aa, bb))];
        Formula expression = terms[0];
        foreach (Formula term in terms.Skip(1)) expression = Add(expression, term);
        return Disp(All("K", Nats(), Outputs(k, Equal(Value(k), expression), false)));
    }

    private static Formula ClaimFormula()
    {
        Formula k = F.Id("K"), z = F.Id("z");
        Formula set = Seq(OpenBrace, z, Sp, Colon, Sp, Nats(), Sp, Mid, Sp,
            Outputs(k, Equal(z, Value(k)), true), CloseBrace);
        Formula minimum = Call("IsLeast", set, Mul(D(6), Parenthesized(Sub(k, D(1)))));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            All("K", Nats(), Logic(LessEq(D(2), k), FormulaLogicOperator.Implies, minimum))));
    }
}
