using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.FixedPoints;

internal sealed class FiniteMonotoneTerminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite monotone refinement terminates, while its limiting fixed point need not be unique.",
        H("Finite Monotone Termination"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-monotone-termination-and-nonunique-example"),
                DeclarationHandle.Create(
                    "D5/S1/FixedPoints/FiniteMonotoneTermination."
                        + "finite_monotone_termination_and_nonunique_example"),
                H("Finite monotone termination with nonunique limits"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let alpha be a finite partial order and let `update` be a monotone "
                            + "endomorphism. The hypothesis `update state <= state` orients strict "
                            + "refinement downward: whenever an update is not fixed, antisymmetry "
                            + "makes that step strictly smaller.")),
                    Paragraph(Text(
                        "The iterates from any initial state form an antitone chain. Pinned Mathlib's "
                            + "`WellFoundedLT.antitone_chain_condition`, together with the finite-order "
                            + "well-founded instance, gives an index after which the chain is constant. "
                            + "Equality at the next index states that the reached value is a fixed point.")),
                    Paragraph(Text(
                        "The uniqueness implication is refuted constructively in the same declaration. "
                            + "The identity update on `Bool` is monotone; the distinct initial states "
                            + "`false` and `true` remain at distinct fixed points under every iterate.")),
                    Paragraph(Text(
                        "Repository search found a finite-set contraction specialization but no generic "
                            + "finite-poset wrapper. The proof therefore directly reuses the exact pinned "
                            + "antitone-chain theorem rather than reproving finite stabilization."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments) =>
        Call(name, arguments);

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

    private static Formula MainFormula()
    {
        Formula carrier = F.Id("alpha");
        Formula update = F.Id("update");
        Formula initial = F.Id("initial");
        Formula state = F.Id("state");
        Formula step = F.Id("N");
        Formula later = F.Id("n");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula orbitAtStep = Apply("iterate", update, step, initial);
        Formula orbitLater = Apply("iterate", update, later, initial);
        Formula termination = Seq(
            Forall, Sp, carrier, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            Typeclass("Finite", carrier), Comma, Sp, Typeclass("PartialOrder", carrier), Comma, Esc,
            update, Colon, Sp, Apply("OrderHom", carrier, carrier), Comma, Sp,
            initial, Colon, Sp, carrier, Comma, Esc,
            Open, Forall, Sp, state, Colon, Sp, carrier, Comma, Sp,
            Apply("update", state), Sp, Leq, Sp, state, Close, Sp, Rightarrow, RowBreak,
            Exists, Sp, step, InMacro, Sp, naturals, Comma, Sp,
            Apply("IsFixedPt", update, orbitAtStep), Sp, Land, Sp,
            Forall, Sp, later, InMacro, Sp, naturals, Comma, Sp,
            step, Sp, Leq, Sp, later, Sp, Rightarrow, Sp,
            orbitLater, Sp, Eq, Sp, orbitAtStep);
        Formula nonunique = Seq(
            Exists, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Colon, Sp, F.Id("Bool"), Comma, Sp,
            F.Id("x"), Sp, Neq, Sp, F.Id("y"), Sp, Land, Sp,
            Open, Forall, Sp, later, InMacro, Sp, naturals, Comma, Sp,
            Apply("iterate", F.Id("id"), later, F.Id("x")),
            Sp, Eq, Sp, F.Id("x"), Close, Sp, Land, Sp,
            Open, Forall, Sp, later, InMacro, Sp, naturals, Comma, Sp,
            Apply("iterate", F.Id("id"), later, F.Id("y")),
            Sp, Eq, Sp, F.Id("y"), Close, Sp, Land, Sp,
            Apply("IsFixedPt", F.Id("id"), F.Id("x")), Sp, Land, Sp,
            Apply("IsFixedPt", F.Id("id"), F.Id("y")));

        return Disp(Seq(Open, termination, Close, Sp, Land, RowBreak, Open, nonunique, Close, Dot));
    }
}
