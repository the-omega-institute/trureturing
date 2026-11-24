using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class PopovUrnNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/PopovUrnNormalization.";
    private static readonly Formula A = F.Id("A");
    private static readonly Formula Nat = Seq(Mathbb, Grp(F.Id("N")));
    private static readonly Formula M = F.Id("m");
    private static readonly Formula T = F.Id("t");
    private static readonly Formula X = F.Id("x");
    private static readonly Formula Y = F.Id("y");
    private static readonly Formula W = F.Id("w");
    private static readonly Formula S = F.Id("s");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First-use words classify chronological urn histories under arbitrary relabelings.",
        H("First-use normalization of urn histories"),
        Blocks(
            Paragraph(Text("A raw history assigns each of t chronological marble positions a pair "
                + "consisting of an urn label in Fin(A) and a slot label in Fin(m). A repeated "
                + "slot requires its own urn to be full. A move to a fresh urn requires all "
                + "started urns to be full. An orbit allows an arbitrary urn permutation and a "
                + "slot permutation for each original urn. All permutations fix every marble "
                + "position. Used(x) is the finite set of distinct values of x.")),
            Node("quotientEquivWord", "The chronological orbit quotient",
                Parameters(Seq(Call("Arrangements", A, M, T), Sp, Sim, Sp, Call("Word", M, T))),
                "Arrangements is the quotient of legal raw histories by the indicated orbit "
                + "relation. A legal word starts with no ranks. With p ranks in use, it may "
                + "introduce rank p or reuse a rank strictly below m times the integer quotient "
                + "of p by m. Replay takes quotient and remainder by m at each marble position.",
                DescribeRole.Definition),
            Node("normalize_eq_iff", "Equality of words is equality of raw orbits",
                Parameters(All(X, Raw(), All(Y, Raw(),
                    Seq(Call("normalize", X), Sp, Eq, Sp, Call("normalize", Y), Sp, Iff, Sp,
                        Call("Orbit", X, Y))))),
                "A prefix induction aligns each new address with its first-use rank. When the "
                + "next address is fresh, the required permutation can be adjusted on unused "
                + "labels. The same-compartment relation determines each legal word uniquely."),
            Node("normalize_replay", "Normalizing a replay recovers the word",
                Parameters(All(W, Call("Word", M, T),
                    Seq(Call("normalize", Call("replay", W)), Sp, Eq, Sp, W))),
                "The replay is legal, including for the empty word. Replaying a normalization "
                + "lies in the original raw orbit."),
            Node("normalized_prefix_interval", "Actual occupied ranks at every prefix",
                Parameters(All(X, Raw(), All(S, Nat,
                    Seq(S, Sp, Le, Sp, T, Sp, Implies, Sp,
                        Call("used", Call("prefix", Call("normalize", X), S)), Sp, Eq, Sp,
                        Call("range", Call("card", Call("used", Call("prefix", X, S)))))))),
                "Here range(p) is the half-open interval from zero to p. The cardinality on "
                + "the right counts actual distinct raw pairs in the prefix. Rank within an urn "
                + "starts at slot zero. The rank at first use of a compartment is the actual "
                + "number of distinct pairs in the preceding prefix."),
            Paragraph(Text("Restricting the quotient equivalence to an occupied-count fiber "
                + "preserves that count. Any two finite ambient urn sets with at least t labels "
                + "give equivalent fibers by passing through the same words.")))));

    private static DocumentBlock.Describe Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Raw() => Call("Raw", A, M, T);
    private static Formula Parameters(Formula body) => All(A, Nat, All(M, Nat, All(T, Nat,
        Seq(D(0), Sp, Lt, Sp, M, Sp, Land, Sp, T, Sp, Le, Sp, A, Sp, Implies, Sp, body))));
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, name, Sp, InMacro, Sp, type, Comma, Sp, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
