using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class CountableClopenReflectionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/CountableClopenReflection.";

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Statement()
    {
        Formula iota = F.Id("I");
        Formula functor = F.Id("F");
        Formula cone = F.Id("C");
        Formula baseStage = F.Id("base");
        Formula beta = F.Id("beta");
        Formula stage = F.Id("CountableStage");
        Formula stageOpp = F.Id("CountableStageOpp");

        Formula obj(Formula j) => Call("Fobj", j);
        Formula conePoint = Call("Cpt");
        Formula set(Formula x) => Call("Set", x);
        Formula member(Formula n) => Call("W", n);
        Formula trace(Formula n) => Call("V", n);
        Formula projection(Formula b) => Call("Cprojection", Call("op", b));
        Formula inverseImage(Formula b, Formula n) => Call("inverseImage", projection(b), trace(n));
        Formula clopen(Formula x) => Call("IsClopen", x);
        Formula nonempty(Formula x) => Call("Nonempty", x);
        Formula disjoint(Formula x, Formula y) => Call("Disjoint", x, y);

        Formula componentNonempty = All("j", stageOpp,
            Call("Nonempty", obj(F.Id("j"))));
        Formula surjectiveBonding = All("i", stageOpp,
            All("j", stageOpp,
                All("f", Call("Hom", F.Id("i"), F.Id("j")),
                    Call("Surjective", Call("Fmap", F.Id("f"))))));
        Formula clopenFamily = All("n", iota,
            clopen(member(F.Id("n"))));

        Formula conclusion = Exists("beta", stage,
            And(Call("Le", baseStage, beta),
                Exists("V", Call("Family", iota, set(obj(Call("op", beta)))),
                    And(
                        All("n", iota, clopen(trace(F.Id("n")))),
                        And(
                            All("n", iota,
                                Eq(member(F.Id("n")), inverseImage(beta, F.Id("n")))),
                            And(
                                All("n", iota,
                                    Iff(nonempty(trace(F.Id("n"))),
                                        nonempty(member(F.Id("n"))))),
                                All("m", iota,
                                    All("n", iota,
                                        Iff(disjoint(trace(F.Id("m")), trace(F.Id("n"))),
                                            disjoint(member(F.Id("m")), member(F.Id("n"))))))))))));

        Formula body = Imp(
            And(Call("Countable", iota), componentNonempty),
            All("C", Call("Cone", functor),
                Imp(And(Call("IsLimit", cone), surjectiveBonding),
                    All("base", stage,
                        All("W", Call("Family", iota, set(conePoint)),
                            Imp(clopenFamily, conclusion))))));

        return Disp(All("I", F.Id("TypeU"),
            All("F", Call("Functor", stageOpp, F.Id("Profinite1")),
                body)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A countable family of final clopens in an omega-one profinite inverse limit has exact traces at one proper common stage.",
        H("Countable common-stage clopen reflection"),
        Blocks(
            Paragraph(Text(
                "CountableStage consists of the ordinals strictly below the first uncountable ordinal. "
                + "F is an actual functor from its opposite preorder category to Profinite at universe one. "
                + "Every component is nonempty and every actual bonding map is surjective. "
                + "C is any actual cone and hC proves that this cone is a limit. The index type I is any countable type in an independent universe, including the empty type. W is any I-indexed family of clopen subsets of C.pt. "
                + "Empty clopens are included; disjointness and nonemptiness are conclusions, not extra hypotheses. "
                + "In the displayed formula TypeU means Type u, Profinite1 means Profinite at universe one, and CountableStageOpp is the opposite stage category. "
                + "Fobj and Fmap are the actual functor object and map operations; Cpt and Cprojection are the actual cone point and projection. "
                + "Family(I,X) means the function type I to X, Le is the ordinal stage order, and inverseImage is literal set preimage. "
                + "IsLimit(C) asserts that the cone has an IsLimit witness. Nonempty applied to a component means carrier nonemptiness; applied to a subset it means set nonemptiness.")),
            Describe.Lean(
                DescribeId.Create("countable-common-stage"),
                DeclarationHandle.Create(Owner + "exists_common_stage"),
                H("Simultaneous exact traces below omega-one"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/kania2026talagrand")),
                Blocks(
                    Paragraph(Text(
                        "For every requested base stage, the theorem returns one beta at or above that base and an I-indexed family V of clopen subsets of F(beta). "
                        + "For every index n the actual final clopen W(n) equals the full inverse image of V(n) under the cone projection at beta. "
                        + "V(n) is nonempty exactly when W(n) is nonempty. For every m and n, V(m) and V(n) are disjoint exactly when W(m) and W(n) are disjoint.")),
                    Paragraph(Text(
                        "Mathlib's Profinite.exists_isClopen_of_cofiltered first reflects each individual W(n) to a stage j(n). "
                        + "Take the supremum over Option(I), assigning base to none and j(n) to some(n). This includes the base even when I is empty. Ordinal.iSup_lt_omega_one certifies that this countable supremum is still a proper stage beta. "
                        + "Pull each reflected clopen back along the actual bonding map from beta to j(n). Cone naturality gives each exact final inverse-image equality.")),
                    Paragraph(Text(
                        "The existing compact_projection_image theorem from D5/S1/Dynamics/Shadowing/MittagLefflerInverseLimit supplies full compatible-thread lifts. "
                        + "Since all bonding maps are surjective, every component point is in the eventual range. "
                        + "The limit-cone isomorphism transfers these lifts to the given cone C, so the actual beta projection is surjective. "
                        + "Lifting one trace point proves the nonemptiness equivalence; lifting a hypothetical intersection point proves the reverse disjointness implication. "
                        + "The private projection helper is a consumed application of that existing theorem, not a separate mathematical contribution.")),
                    Paragraph(Text(
                        "This is attributed known inverse-limit infrastructure. In the Talagrand CH candidate, one may include a separating clopen among the countable family "
                        + "and reflect all final clopen supports into one actual launch row. The theorem supplies that common-stage reflection only. "
                        + "It does not realize the transfinite compactum, prove signed-measure clauses (A)-(G), perform retrospective paired-Dirac capture, "
                        + "or settle Kania and Kakol's arXiv:2607.06808v2 Problem 8.2."))),
                DescribeRole.Theorem))));
}
