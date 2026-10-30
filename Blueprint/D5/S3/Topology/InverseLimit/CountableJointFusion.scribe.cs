using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class CountableJointFusionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/CountableJointFusion.";

    private static Formula V(string name) => F.Id(name);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);

    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Nat => V("Nat");
    private static Formula Bool => V("Bool");
    private static Formula SetNat => Call("Set", Nat);
    private static Formula NatTo(Formula target) => Seq(Nat, Sp, To, Sp, target);
    private static Formula Fun(Formula domain, Formula target) =>
        Seq(domain, Sp, To, Sp, target);
    private static Formula Act(Formula k, Formula j) => Call("active", k, j);
    private static Formula IAt(Formula j) => Call("I", j);
    private static Formula JAt(Formula k, Formula j) => Call("J", k, j);
    private static Formula NAt(Formula k, Formula e) => Call("N", k, e);
    private static Formula VAt(Formula j, Formula k, Formula e) => Call("v", j, k, e);
    private static Formula Eventual(Formula left, Formula right) =>
        Call("EventuallySubset", V("cofinite"), left, right);

    private static Formula Statement()
    {
        Formula hfinite = All("j", Nat,
            Call("Finite", Seq(OpenBrace, V("k"), Colon, Sp, Nat, Sp, Bar, Sp,
                Act(V("k"), V("j")), CloseBrace)));
        Formula heventual = All("k", Nat,
            Ex("j0", Nat,
                All("j", Nat,
                    Imp(Call("Le", V("j0"), V("j")), Act(V("k"), V("j"))))));
        Formula hsub = All("k", Nat,
            All("j", Nat,
                Imp(Act(V("k"), V("j")),
                    Call("Subset", JAt(V("k"), V("j")), IAt(V("j"))))));
        Formula hImono = All("h", Nat,
            All("j", Nat,
                Imp(Call("Le", V("h"), V("j")),
                    Eventual(IAt(V("j")), IAt(V("h"))))));
        Formula hJmono = All("k", Nat,
            All("h", Nat,
                All("j", Nat,
                    Imp(And(Act(V("k"), V("h")),
                        And(Act(V("k"), V("j")), Call("Le", V("h"), V("j")))),
                        Eventual(JAt(V("k"), V("j")), JAt(V("k"), V("h")))))));
        Formula hpool = All("k", Nat,
            All("j", Nat,
                All("e", Bool,
                    Imp(Act(V("k"), V("j")),
                        Call("Infinite", Call("inter", JAt(V("k"), V("j")),
                            NAt(V("k"), V("e"))))))));

        Formula earlierI = All("h", Nat,
            Imp(Call("Le", V("h"), V("j")),
                Call("Member", VAt(V("j"), V("k"), V("e")), IAt(V("h")))));
        Formula earlierJ = All("h", Nat,
            Imp(Call("Le", V("h"), V("j")),
                Imp(Act(V("k"), V("h")),
                    Call("Member", VAt(V("j"), V("k"), V("e")), JAt(V("k"), V("h"))))));
        Formula witness = All("j", Nat,
            All("k", Nat,
                All("e", Bool,
                    Imp(Act(V("k"), V("j")),
                        And(Call("Lt", V("j"), VAt(V("j"), V("k"), V("e"))),
                            And(Call("Member", VAt(V("j"), V("k"), V("e")),
                                    JAt(V("k"), V("j"))),
                                And(Call("Member", VAt(V("j"), V("k"), V("e")),
                                        NAt(V("k"), V("e"))),
                                    And(earlierI, earlierJ))))))));
        Formula definition = All("k", Nat,
            All("n", Nat,
                Iff(Call("Member", V("n"), Call("Jlim", V("k"))),
                    Ex("j", Nat,
                        Ex("e", Bool,
                            And(Act(V("k"), V("j")),
                                Eq(V("n"), VAt(V("j"), V("k"), V("e")))))))));
        Formula reservoir = All("k", Nat,
            All("e", Bool,
                Call("Infinite", Call("inter", Call("Jlim", V("k")),
                    NAt(V("k"), V("e"))))));
        Formula eventualI = All("h", Nat, Eventual(V("Ilim"), IAt(V("h"))));
        Formula eventualJ = All("k", Nat,
            All("h", Nat,
                Imp(Act(V("k"), V("h")),
                    Eventual(Call("Jlim", V("k")), JAt(V("k"), V("h"))))));
        Formula conclusions = And(witness,
            And(definition,
                And(Eq(V("Ilim"), Call("iUnion", V("Jlim"))),
                    And(reservoir, And(eventualI, eventualJ)))));

        Formula hypotheses = And(hfinite, And(heventual,
            And(hsub, And(hImono, And(hJmono, hpool)))));
        return Disp(Seq(
            All("active", NatTo(NatTo(V("Prop"))),
                All("I", NatTo(SetNat),
                    All("J", NatTo(NatTo(SetNat)),
                        All("N", NatTo(Fun(Bool, SetNat)),
                            Imp(hypotheses,
                                Ex("v", Fun(Nat, Fun(Nat, Fun(Bool, Nat))),
                                    Ex("Ilim", SetNat,
                                        Ex("Jlim", NatTo(SetNat), conclusions))))))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A countable finite-block selector jointly preserves fixed reservoirs and one-sided cofinite inclusions.",
        H("Countable joint finite-block fusion"),
        Blocks(
            Paragraph(Text(
                "The active predicate records delayed proper-stage domains. The displayed finite set consists of "
                + "exactly the labels k active in block j. Every block has a finite active fibre, "
                + "and every label is active from some stage onward. I and J are inherited stage sets; N is the "
                + "literal fixed reservoir family, with both Bool colours retained. EventuallySubset uses the cofinite "
                + "filter, so the conclusion is one-sided finite difference rather than symmetric difference.")),
            Describe.Lean(
                DescribeId.Create("countable-joint-finite-block-fusion"),
                DeclarationHandle.Create(Owner + "exists_countable_joint_finite_block_fusion"),
                H("Joint selector and countable limit sets"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each active triple (j,k,e), the proof removes the finitely many earlier I and same-label J "
                        + "exceptions from the infinite pool J(k,j) intersect N(k,e), and also imposes j<n. "
                        + "Classical choice selects one witness. Inactive triples are not inserted into Jlim.")),
                    Paragraph(Text(
                        "The lower bound j<v(j,k,e) makes every fixed Jlim(k) intersect N(k,e) infinitely often once "
                        + "k is eventually active. Values from blocks before a fixed h form a finite set because each "
                        + "block has finitely many active labels and two colours; all later values satisfy the earlier "
                        + "I and J constraints. This proves the stated one-sided cofinite inclusions.")),
                    Paragraph(Text(
                        "The proper-limit manuscript application supplies active(k,j) from a cofinal sequence of proper "
                        + "stages, with N unchanged. The selector applies only at proper countable limits; no final-stage "
                        + "I, J or N bookkeeping is part of this target. This result does not supply the ordinal adapter, "
                        + "successor residual initialization, analytic F or G clauses, lift existence, or transfinite CH "
                        + "recursion. The final inverse-limit model and its analytic endpoints remain outside this supplier, "
                        + "as do the full Talagrand K_r/V_n construction and a solution of Problem 8.2."))),
                DescribeRole.Theorem))));
}
