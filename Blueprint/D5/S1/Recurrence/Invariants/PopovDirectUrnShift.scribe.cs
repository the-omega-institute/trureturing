using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class PopovDirectUrnShiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/PopovDirectUrnShift.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/popov2026mstirling");
    private static readonly Formula Nat = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula M = F.Id("m");
    private static readonly Formula N = F.Id("n");
    private static readonly Formula R = F.Id("r");
    private static readonly Formula K = F.Id("k");
    private static readonly Formula T = F.Id("t");
    private static readonly Formula J = F.Id("j");
    private static readonly Formula Q = F.Id("q");
    private static readonly Formula B = F.Id("b");
    private static readonly Formula Positions = F.Id("J");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chronological first-urn deletion and reinsertion give Popov’s shift identity.",
        H("A direct first-urn bijection for Popov's shift"),
        Blocks(
            Paragraph(Text("Write U(m,t,k) for the orbits of legal chronological urn histories "
                + "of length t with exactly k occupied pairs. The first m marbles must fill "
                + "the first urn. Deletion records the tail positions J that avoid this urn, "
                + "and records a first-urn color at every complementary position. It keeps the "
                + "placements on J in increasing chronological order and drops the first urn "
                + "from their rank system.")),
            Node("firstUrnEquiv", "First-urn deletion and reinsertion",
                Parameters(R, Seq(SourceFiber(), Sp, Sim, Sp,
                    Sigma, Underscore, Grp(Seq(Positions, Sp, InMacro, Sp, Call("Finset", Call("Fin", N)))),
                    Sp, Open, Call("Colors", M, N, Positions), Sp, Times, Sp,
                    Call("U", M, Call("card", Positions), R), Close)),
                "Colors(m,n,J) is the function type from the subtype of positions outside J "
                + "to Fin(m). The dependent sum is called Payload(m,n,r). Reinsertion first "
                + "puts back the forced prefix and then traverses the tail, inserting the "
                + "recorded color or the next residual placement. A color is always legal in the "
                + "full first urn, including when a later urn is partly full. The used pairs are "
                + "the disjoint union of the m first-urn pairs and the shifted residual pairs.",
                DescribeRole.Definition),
            Node("reinsert_delete", "Reinsertion recovers the source orbit",
                Parameters(R, All(Q, SourceFiber(),
                    Eqn(Call("reinsert", Call("delete", Q)), Q))),
                "The composite recovers the forced prefix and each chronological tail entry."),
            Node("delete_reinsert", "Deletion recovers all payload data",
                Parameters(R, All(B, Call("Payload", M, N, R),
                    Eqn(Call("delete", Call("reinsert", B)), B))),
                "The rank ranges separate selected placements and colors, so the composite "
                + "recovers the subset, each color, and the residual orbit."),
            Node("below_first_urn_payload_empty", "Empty payload below the first urn",
                All(M, Nat, All(N, Nat, All(K, Nat, Seq(K, Sp, Lt, Sp, M, Sp, Implies, Sp,
                    Call("IsEmpty", Call("SignedPayload", M, N, Sub(K, M))))))),
                "SignedPayload uses the same subset and colors and the signed residual fiber, "
                + "which is empty at every negative column. The source is empty for k below m "
                + "because the forced prefix uses m distinct pairs."),
            Node("card_urn_eq_stirling", "The urn count satisfies the published recurrence",
                All(M, Nat, Seq(D(0), Sp, Lt, Sp, M, Sp, Implies, Sp, All(T, Nat, All(K, Nat,
                    Eqn(Call("card", Call("U", M, T, K)), Call("stirling", M, T, K)))))),
                "There is one empty history and zero histories of positive length in column zero. "
                + "At a positive column k the last move reuses one of the m floor(k/m) slots "
                + "in complete urns or opens the unique fresh slot from column k−1. This gives "
                + "Definition 7.1 and recurrence (7.1). The signed count S vanishes at negative columns."),
            Node("shift_7_2", "Popov's shift identity by finite counting", Shift(),
                "Take the cardinalities of the exhibited equivalence. Subsets of cardinality j "
                + "contribute the binomial coefficient and there are m to the power n−j "
                + "complement color functions. The residual quotient contributes S(m,j,k−m). "
                + "Popov's Theorem 7.3 gives the prior algebraic proof of the same identity.",
                provenance: AssessedProvenance.FromLiterature(Source)),
            Paragraph(Text("At capacity one, the construction deletes the block containing the "
                + "initial marble. If the tail is empty, the only occupied-count column is m, "
                + "with one forced-prefix orbit and one empty residual orbit. In column m for "
                + "any tail length, every tail marble uses one of the first-urn colors. "
                + "Columns above the number of marbles are empty.")))));

    private static DocumentBlock.Describe Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Shift() => Parameters(K,
        Eqn(Call("S", M, Add(N, M), K),
            Seq(Sum, Underscore, Grp(Seq(J, Eq, D(0))), Caret, Grp(N), Sp,
                Call("choose", N, J), Sp, Cdot, Sp, Call("pow", M, Sub(N, J)), Sp, Cdot, Sp,
                Call("S", M, J, Sub(K, M)))));

    private static Formula SourceFiber() => Call("U", M, Add(N, M), Add(M, R));
    private static Formula Parameters(Formula column, Formula body) =>
        All(M, Nat, All(N, Nat, All(column, Nat, Seq(D(0), Sp, Lt, Sp, M, Sp, Implies, Sp, body))));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, name, Sp, InMacro, Sp, type, Comma, Sp, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
