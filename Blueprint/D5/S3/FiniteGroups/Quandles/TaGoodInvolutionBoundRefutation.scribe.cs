using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.Quandles;

internal sealed class TaGoodInvolutionBoundRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/Quandles/TaGoodInvolutionBoundRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/ta2025goodinvolutions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The conjugation subquandle {±i, ±j} of the quaternion group Q8 has four good involutions and eight automorphisms. Its generated subgroup has center of order two and two conjugation orbits, so the bound min(8, 2^2) = 4 is attained. This answers Lực Ta's Problem 11.7 in the negative.",
        H("A quaternion subquandle attains the good-involution bound"),
        Blocks(
            Node("claim", "The strictness question", ClaimFormula(),
                "Ta, Problem 11.7, printed page 27: \"In the setting of Corollary 6.12, suppose that |Z(H)|, |X/H| ≥ 2 (so, in particular, Conj X is not connected). Is the upper bound on |Good(Conj X)| in Corollary 6.12 always strict?\" Corollary 6.12, printed page 14: \"Let k(X) := |X/H|. Then |Good(Conj X)| ≤ min(|Aut(Conj X)|, |Z(H)|^{k(X)}). If X is not closed under inverses, then the bound |Good(Conj X)| < |Z(H)|^{k(X)} is strict.\" The encoding quantifies over G : Type, each group structure, finite enumeration and decidable equality on G, every finite subset X, and every closure proof h. The binder names group, finite and eq denote these implicit Lean instances. DecidableEq is implementation structure, available classically. H = ⟨X⟩, k = orbitCount X, and z = Nat.card (Subgroup.center H); The displayed FintypeCard on Good and Aut is Fintype.card, NatCard is Nat.card, and FinsetCard is Finset.card. closure, center and Bijective denote Subgroup.closure, Subgroup.center and Function.Bijective, respectively. The displayed center cardinality and orbit count are expressions, rather than extra parameters. This is the finite-group strictness reading: a finite counterexample suffices to refute the unrestricted question. No assertion about infinite cardinal arithmetic is made.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The bound is attained", Disp(new Formula.Not(F.Id("claim"))),
                "Take G = QuaternionGroup 2 and X = {a 1, a 3, xa 0, xa 2} = {±i, ±j}. The inverse of a 1 is a 3 and the inverse of xa 0 is xa 2; a 1 and xa 0 do not commute. Conjugation preserves X, and a 1 and xa 0 generate G. The center has order two. The conjugation orbits are {a 1, a 3} and {xa 0, xa 2}, so k = 2. The four good involutions independently exchange or fix the two elements in each orbit. There are eight automorphisms. Thus |Good| = 4 = min(8, 2^2), which contradicts the proposed strict inequality.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ta-2025-problem-11-7-good-involution-bound-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("ta117-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, Parenthesized(body));
    private static Formula Closure(Formula x) => Call("closure", Parenthesized(Seq(x, Sp, Colon, Sp, Call("Set", F.Id("G")))));
    private static Formula CenterSize(Formula x) => Call("NatCard", Call("center", Closure(x)));
    private static Formula Count(Formula type) => Call("FintypeCard", type);

    private static Formula ClaimFormula()
    {
        Formula g = F.Id("G"), set = F.Id("X"), h = F.Id("h");
        Formula z = CenterSize(set), k = Call("orbitCount", set);
        Formula bound = new Formula.Relation(Count(Call("Good", set, h)),
            FormulaRelationOperator.LessThan,
            Call("min", Count(Call("Aut", set, h)), new Formula.Power(z, k)));
        Formula largeCenter = new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, z);
        Formula manyOrbits = new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, k);
        Formula body = Seq(Forall, Sp, Parenthesized(Seq(g, Sp, Colon, Sp, Named("Type"))), Sp,
            OpenBracket, Call("Group", g), CloseBracket, Sp,
            OpenBracket, Call("Fintype", g), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", g), CloseBracket, Comma, Sp,
            Parenthesized(All(set, Call("Finset", g), All(h, Call("ConjClosed", set),
                Implies(largeCenter, Implies(manyOrbits, bound))))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
