using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class FrobeniusCentralizerOrbitArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A derangement's centralizer acts freely under the two-point fixed condition, so its order divides the finite action's degree.",
        H("Centralizer Orbits in a Frobenius Action"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("frobenius-centralizer-free-action"),
                DeclarationHandle.Create(
                    "D5/S3/FiniteGroups/FrobeniusCentralizerOrbitArithmetic.centralizer_smul_ne_self_of_ne_one"),
                H("Nonidentity centralizer elements move every point"),
                StatementSource.FromAuthor(FreeAction()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let G act on X, with every nonidentity element fixing at most one point, "
                    + "and let d be a derangement: d moves every point of X. If a nonidentity "
                    + "element c of the subgroup Subgroup.centralizer {d} fixed x, its commutation "
                    + "with d would also make it fix d acting on x. The two-point fixed condition "
                    + "would identify x with d acting on x, contradicting the derangement premise. "
                    + "Thus the restricted centralizer action is free. G and X may be infinite "
                    + "and may lie in different universes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("frobenius-centralizer-degree-divisibility"),
                DeclarationHandle.Create(
                    "D5/S3/FiniteGroups/FrobeniusCentralizerOrbitArithmetic.card_centralizer_dvd_card"),
                H("Centralizer order divides the degree"),
                StatementSource.FromAuthor(Divisibility()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "When G and X are finite, the first theorem makes every stabilizer "
                        + "of the restricted centralizer action trivial. The pinned Mathlib "
                        + "equivalence MulAction.selfEquivOrbitsQuotientProd identifies X with "
                        + "its centralizer-orbit quotient times the centralizer. Nat.card_congr "
                        + "and Nat.card_prod then give the displayed divisibility.")),
                    Paragraph(Text(
                        "The empty type X is allowed: its degree is zero, and the divisibility "
                        + "still holds. Transitivity, faithfulness and nonemptiness are not "
                        + "assumed. These statements give the centralizer free-action argument "
                        + "and its orbit arithmetic; they assert neither the Frobenius kernel "
                        + "theorem nor a classification of Frobenius groups. The exposition "
                        + "records the repository derivation without a literature novelty claim."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(owner)), Dot,
            Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Par(Formula formula) => Seq(Open, formula, Close);
    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(Par(premise), FormulaLogicOperator.Implies, Par(conclusion));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Act(Formula element, Formula point) =>
        Qualified("SMul", "smul", element, point);
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Comma, Sp, body);
    private static Formula Centralizer() => Qualified("Subgroup", "centralizer",
        Par(Seq(OpenBrace, F.Id("d"), CloseBrace, Colon, Sp, Call("Set", F.Id("G")))));
    private static Formula FixedCondition() =>
        All("g", F.Id("G"), Imp(Ne(F.Id("g"), D(1)),
            All("x", F.Id("X"), All("y", F.Id("X"),
                Imp(Equal(Act(F.Id("g"), F.Id("x")), F.Id("x")),
                    Imp(Equal(Act(F.Id("g"), F.Id("y")), F.Id("y")),
                        Equal(F.Id("x"), F.Id("y"))))))));
    private static Formula Derangement() => All("x", F.Id("X"),
        Ne(Act(F.Id("d"), F.Id("x")), F.Id("x")));
    private static Formula Context(Formula body) => Disp(
        Seq(Forall, Sp, F.Id("u"), Sp, F.Id("v"), Comma, Sp,
            All("G", Seq(Operatorname, Grp(F.Id("Type")), Sp, F.Id("u")),
                All("X", Seq(Operatorname, Grp(F.Id("Type")), Sp, F.Id("v")),
                    Instance(Call("Group", F.Id("G")),
                        Instance(Call("MulAction", F.Id("G"), F.Id("X")), body))))));
    private static Formula FreeAction() => Context(Imp(FixedCondition(),
        All("d", F.Id("G"), Imp(Derangement(),
            All("c", Centralizer(), Imp(Ne(F.Id("c"), D(1)),
                All("x", F.Id("X"), Ne(Act(F.Id("c"), F.Id("x")), F.Id("x")))))))));
    private static Formula Divisibility() => Context(
        Instance(Call("Finite", F.Id("G")), Instance(Call("Finite", F.Id("X")),
            Imp(FixedCondition(), All("d", F.Id("G"), Imp(Derangement(),
                Seq(Qualified("Nat", "card", Centralizer()), Sp, Mid, Sp,
                    Qualified("Nat", "card", F.Id("X")))))))));
}
