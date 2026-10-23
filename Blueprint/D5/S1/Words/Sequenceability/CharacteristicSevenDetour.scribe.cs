using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Sequenceability;

internal sealed class CharacteristicSevenDetourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Sequenceability/CharacteristicSevenDetour.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula IffF(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, b, Close);
    private static Formula K => V("K");
    private static Formula R => V("r");
    private static Formula C => V("c");
    private static Formula States => Seq(Call("Fin", D(6)), Sp, Times, Sp, K);
    private static Formula Row => Call("rowReturn", R, C);
    private static Formula Lift => Call("lift", R, C);

    private static Formula FieldBind(Formula body) => All("K", Call("Type"),
        All("f", Call("Field", K), All("finite", Call("Finite", K), body)));

    private static Formula LiftFormula()
    {
        Formula outside = Seq(OpenBrace, V("v"), Colon,
            Seq(Call("ZMod", D(7)), Sp, Times, Sp, K), Mid,
            Ne(Call("fst", V("v")), D(0)), CloseBrace);
        Formula cycles = All("v", States, All("w", States,
            IffF(Call("SameCycle", Lift, V("v"), V("w")),
                IffF(Eqn(Call("initialRow", V("v")), C),
                    Eqn(Call("initialRow", V("w")), C)))));
        Formula round = All("h", K, Eqn(
            new Formula.Apply(new Formula.Power(Lift, D(6)), [Pair(D(0), V("h"))]),
            Pair(D(0), new Formula.Apply(Row, [V("h")]))));
        Formula body = Ex("r", Call("Units", K),
            And(Ne(new Formula.Binary(Call("coe", R), FormulaBinaryOperator.Add, D(1)), D(0)),
            And(cycles, And(Call("BijOn", Call("edgeLabel", R, C), Call("univ"), outside),
            And(Call("BijOn", Call("vertex"), Call("univ"), outside), round))));
        return Disp(FieldBind(All("char", Call("CharP", K, D(7)), All("c", K, body))));
    }

    private static Formula SeamsFormula()
    {
        Formula body = All("r", Call("Units", K), All("u", K,
            Imp(Ne(V("u"), D(0)),
                Imp(Ne(new Formula.Binary(Call("coe", R), FormulaBinaryOperator.Add, D(1)), D(0)),
                    Call("six_column_splice_seams", R, V("u"),
                        Ne(V("u"), D(0)),
                        Ne(new Formula.Binary(Call("coe", R), FormulaBinaryOperator.Add, D(1)), D(0)))))));
        return Disp(FieldBind(All("char", Call("CharP", K, D(7)), body)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-column affine group action and the overlapping two-head characteristic-seven splice.",
        H("Characteristic-seven six-column detour"), Blocks(
            Paragraph(Text("The generic row-return theorem supplies the affine orbit calculation. "
                + "This document records the genuinely new six-phase lift in ZMod(7), its exact inventories, "
                + "and the overlapping endpoint seams used by the relative path.")),
            Describe.Lean(DescribeId.Create("characteristic-seven-detour-lift"),
                DeclarationHandle.Create(Prefix + "exists_characteristic_seven_lift"),
                H("Exact six-phase cycles and inventories"), StatementSource.FromAuthor(LiftFormula()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A primitive unit gives the two affine row cycles. The six first-coordinate "
                        + "differences are the nonzero elements of F7, and each row-coordinate map is invertible. "
                        + "The vertex and label BijOn statements therefore cover every nonzero column exactly once "
                        + "over arbitrary finite extensions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("characteristic-seven-detour-seams"),
                DeclarationHandle.Create(Prefix + "six_column_splice_seams"), H("Overlapping endpoint seams"),
                StatementSource.FromAuthor(SeamsFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("With alpha=(r+1)u/(3r), c=-alpha and beta=u-alpha, the two heads have "
                        + "initial rows c and c+u. The predecessor equations and all four actual seam labels "
                        + "are retained before the closing target-to-source edge is deleted."))), DescribeRole.Theorem))));
}
