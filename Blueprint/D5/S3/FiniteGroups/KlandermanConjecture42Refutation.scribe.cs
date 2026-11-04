using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class KlandermanConjecture42RefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/KlandermanConjecture42Refutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/klanderman2025transfersystems");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On Q8, ordinary generation after adding the bottom-to-top arrow fails the compatibility clause of Conjecture 4.2.",
        H("Ordinary generation need not produce a compatible pair"),
        Blocks(
            Describe.Lean(DescribeId.Create("klanderman-conjecture-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The full universal conjecture"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Conjecture 4.2 of Klanderman, Lewis, Monson, Shibata and Van Niel, "
                        + "arXiv:2511.13439v2, printed page 15, asserts both non-LSP and compatibility. "
                        + "The claim quantifies over every finite group and every transfer system on all its actual "
                        + "subgroups. No saturation, non-abelian restriction, bound on the carrier, or selected list "
                        + "of subgroups is assumed. Group and Finite are anonymous Lean instance arguments.")),
                    Paragraph(Text(
                        "TransferSystem records refinement of subgroup inclusion, reflexivity, composition, "
                        + "restriction and conjugation. Refinement gives antisymmetry. For L ≤ H, H ∩ L = L, "
                        + "so its restriction field with target L is precisely Definition 2.1. Conjugation is "
                        + "Subgroup.map under Mathlib's MulAut.conj g, hence sends K to gKg⁻¹.")),
                    Paragraph(Text(
                        "Compatible(T,U) means that T is contained in U and, for all actual subgroups B,C ≤ A, "
                        + "T(B,A) and U(B ∩ C,B) imply U(C,A). This is the order (T₁,T₂) of Definition 2.14. "
                        + "Saturated means that L ≤ K ≤ H and T(L,H) imply T(K,H). The hull relation is the "
                        + "intersection of all saturated transfer extensions of T. This family contains the complete "
                        + "inclusion relation; intersections preserve all transfer axioms and saturation, contain T, "
                        + "and are contained in every member. Thus it is the source's least saturated hull. "
                        + "LesserSimplyPaired requires every compatible U to equal that hull or the complete "
                        + "inclusion relation; equality is expressed by agreement on every pair of subgroups.")),
                    Paragraph(Text(
                        "arrowGraph is the actual SimpleGraph on Subgroup G, with an undirected edge between "
                        + "distinct K,H whenever T(K,H) or T(H,K). Removing identity loops changes no component. "
                        + "TwoComponents requires the components of the trivial and whole subgroups to be distinct "
                        + "and every SimpleGraph.ConnectedComponent to equal one of them. TopIsolated says every "
                        + "arrow incident to the whole group is its identity. Under reflexivity, this is equivalent "
                        + "to the conjecture's assertion that its component has only G → G."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("klanderman-ordinary-generation"),
                DeclarationHandle.Create(Prefix + "generated"),
                H("The least ordinary transfer extension"),
                StatementSource.FromAuthor(Disp(GeneratedFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Here rel(U,K,H) denotes U.rel K H, bot is the trivial subgroup and top is the whole group. "
                    + "For each T, generated T intersects all ordinary transfer systems U containing T and bot → top. "
                    + "The complete system belongs to this family, and the definition supplies every transfer axiom. "
                    + "Each arrow of T and bot → top belongs to every U, so both are included. Conversely, if U "
                    + "contains these generators, evaluating the displayed universal quantifier at U proves "
                    + "generated T ⊆ U. This is exactly ordinary least generation. The source cites Rubin's "
                    + "Construction A.1; his Theorem A.2 identifies the construction by this leastness property. "
                    + "No compatibility or saturation closure is part of generated."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("klanderman-conjecture-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The quaternion witness"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Named("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take the existing Mathlib group Q8 = QuaternionGroup 2. Set Z = zpowers(a 2) "
                        + "and A = zpowers(a 1), so bot < Z < A < top. The element a 2 is nonidentity. "
                        + "It is the square of a 1, while a 1 is absent from the two-element cyclic subgroup Z. "
                        + "Every power of a 1 is of constructor a, so xa 0 is absent from A. These facts establish "
                        + "the strict chain without enumerating or replacing the subgroup lattice.")),
                    Paragraph(Text(
                        "Define T(K,H) by K = H or (K = bot and H ≠ top). All nonidentity arrows have source bot. "
                        + "Refinement and reflexivity follow immediately. In a composite the first arrow is an "
                        + "identity or has source bot; the second arrow either preserves its proper target or again "
                        + "has proper target. Restriction has source bot ∩ L = bot and a proper target L ≤ H < top. "
                        + "Conjugation fixes bot and preserves properness because it is a group automorphism. "
                        + "Thus T satisfies every source transfer axiom.")),
                    Paragraph(Text(
                        "Every proper subgroup distinct from bot is adjacent to bot. No nonidentity arrow meets top. "
                        + "Its neighbor set is empty, and Mathlib's reachability criterion separates its actual "
                        + "connected component from that of bot. Induction over actual connected components then "
                        + "shows that these are all components. The hypotheses of the conjecture hold for T.")),
                    Paragraph(Text(
                        "Let U(K,H) mean K = H or K = bot. It also satisfies all five transfer axioms and contains "
                        + "T and bot → top. Leastness gives generated T ⊆ U. Conversely, identities belong to generated T, "
                        + "and restriction of bot → top along every H gives bot → H. These are all arrows of U. "
                        + "The private generated_star proof therefore identifies the ordinary generated relation "
                        + "with U on every actual pair K,H, without a compatibility step.")),
                    Paragraph(Text(
                        "Apply the asserted compatibility at ambient A, B = bot and C = Z. The arrow bot → A "
                        + "belongs to T since A is proper; bot ∩ Z → bot is the identity in generated T. "
                        + "Compatibility would force Z → A. The exact generated-system identification says that "
                        + "this requires Z = A or Z = bot, contradicting the two strict inclusions. This refutes "
                        + "the full conjunction through its compatibility clause. It does not assert the falsity "
                        + "of the non-LSP clause or resolve it separately."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("klanderman-2025-conjecture-4-2"), ResolutionKind.Refuted)))));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula v, Formula type, Formula body) =>
        Seq(Forall, Sp, v, Sp, Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Equal(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula IffOf(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, Par(b));
    private static Formula GroupBody(Formula g, Formula body, bool finite) =>
        Seq(Forall, Sp, Par(Seq(g, Sp, Colon, Sp, Named("Type"))), Sp,
            OpenBracket, Call("Group", g), CloseBracket, Sp,
            finite ? Seq(OpenBracket, Call("Finite", g), CloseBracket, Sp) : Seq(),
            Comma, Sp, Par(body));

    private static Formula ClaimFormula()
    {
        Formula g = F.Id("G"), t = F.Id("T");
        Formula body = All(t, Call("TransferSystem", g),
            Imp(Call("TwoComponents", t), Imp(Call("TopIsolated", t),
                And(new Formula.Not(Call("LesserSimplyPaired", t)),
                    Call("Compatible", t, Call("generated", t))))));
        return Equal(Seq(Named("claim"), Sp, Colon, Sp, Named("Prop")),
            GroupBody(g, body, true));
    }

    private static Formula GeneratedFormula()
    {
        Formula g = F.Id("G"), t = F.Id("T"), u = F.Id("U"), k = F.Id("K"), h = F.Id("H");
        Formula system = Call("TransferSystem", g), subgroup = Call("Subgroup", g);
        Formula rhs = All(u, system, Imp(Call("Extends", t, u),
            Imp(Call("rel", u, Named("bot"), Named("top")), Call("rel", u, k, h))));
        return GroupBody(g, All(t, system, All(k, subgroup, All(h, subgroup,
            IffOf(Call("rel", Call("generated", t), k, h), rhs)))), false);
    }
}
