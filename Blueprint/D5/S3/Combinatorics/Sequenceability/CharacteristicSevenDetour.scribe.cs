using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;

internal sealed class CharacteristicSevenDetourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Sequenceability/CharacteristicSevenDetour.";
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
            And(Call("BijOn", Call("vertex"), Call("univ"), outside), round)))));
        return Disp(FieldBind(All("char", Call("CharP", K, D(7)), All("c", K, body))));
    }

    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Apply(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Conjoin(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (int i = clauses.Length - 2; i >= 0; --i) result = And(clauses[i], result);
        return result;
    }
    private static Formula SeamsFormula()
    {
        Formula u = V("u"), s = Call("source"), t = Call("target");
        Formula a = Call("alpha", R, u);
        Formula h1 = Call("headOne", R, u), h2 = Call("headTwo", R, u);
        Formula p1 = Call("predecessorOne", R, u), p2 = Call("predecessorTwo", R, u);
        Formula Q = Call("splice", R, u);
        Formula Vtx(Formula x) => Call("vertexWithEndpoints", u, x);
        Formula body = Conjoin(Eqn(Apply(Q, p1), h2), Eqn(Apply(Q, p2), t),
            Eqn(Apply(Q, s), h1), Eqn(Apply(Q, t), s),
            Eqn(Sub(Vtx(h2), Vtx(p1)), Pair(D(0), u)),
            Eqn(Sub(Vtx(t), Vtx(p2)), Pair(D(2), Mul(D(2), a))),
            Eqn(Sub(Vtx(h1), Vtx(s)), Pair(D(3), a)),
            Eqn(Sub(Vtx(s), Vtx(t)), Pair(D(0), Seq(Minus, u))));
        return Disp(All("K", Call("Type"), All("f", Call("Field", K),
            All("char", Call("CharP", K, D(7)), All("r", Call("Units", K), All("u", K,
            Imp(Ne(u, D(0)), Imp(Ne(Add(Call("coe", R), D(1)), D(0)), body))))))));
    }

    private static Formula Generates() => All("z", Call("Units", K),
        Ex("n", Call("Nat"), Eqn(new Formula.Power(R, V("n")), V("z"))));
    private static Formula CycleFormula()
    {
        Formula criterion = All("v", States, All("w", States,
            IffF(Call("SameCycle", Lift, V("v"), V("w")),
                IffF(Eqn(Call("initialRow", V("v")), C), Eqn(Call("initialRow", V("w")), C)))));
        return Disp(FieldBind(All("r", Call("Units", K), Imp(Generates(), All("c", K, criterion)))));
    }
    private static Formula GeneratorFormula() => Disp(All("K", Call("Type"), All("f", Call("Field", K),
        All("char", Call("CharP", K, D(7)), All("r", Call("Units", K),
            Imp(Generates(), Ne(Add(Call("coe", R), D(1)), D(0))))))));
    private static Formula LabelFormula()
    {
        Formula u = V("u");
        Formula tails = Seq(OpenBrace, V("x"), Sp, Mid, Sp, Ne(V("x"), Call("target")), CloseBrace);
        Formula labels = Seq(OpenBrace, V("z"), Sp, Mid, Sp,
            new Formula.Logic(Ne(Call("fst", V("z")), D(0)), FormulaLogicOperator.Or,
                Eqn(V("z"), Pair(D(0), u))), CloseBrace);
        Formula body = All("r", Call("Units", K), All("u", K,
            Imp(Ne(u, D(0)), Imp(Ne(Add(Call("coe", R), D(1)), D(0)),
                Call("BijOn", Call("successorLabel", R, u), tails, labels)))));
        return Disp(FieldBind(All("char", Call("CharP", K, D(7)), body)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-column affine group action and the overlapping two-head characteristic-seven splice.",
        H("Characteristic-seven six-column detour"), Blocks(
            Paragraph(Text("The generic row-return theorem supplies the affine orbit calculation. "
                + "This document records the genuinely new six-phase lift in ZMod(7), its exact inventories, "
                + "and exact vector-label conservation for the overlapping endpoint splice. "
                + "These are formal proofs of the stated construction, with no claim of literature novelty.")),
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
                        + "are retained before the closing target-to-source edge is deleted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("characteristic-seven-detour-row-cycles"),
                DeclarationHandle.Create(Prefix + "lift_same_cycle"), H("Generating-unit cycle criterion"),
                StatementSource.FromAuthor(CycleFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every field with finite carrier, every generating unit r, every c and "
                        + "all two vertices, the six-phase lift has the same-cycle relation exactly when their "
                        + "initial rows are simultaneously equal or unequal to c. Generating means that every "
                        + "unit is a natural power of r. CharacteristicSevenRelativePath uses this criterion "
                        + "to identify the distinct marked base cycles."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("characteristic-seven-detour-generator-coefficient"),
                DeclarationHandle.Create(Prefix + "generator_add_one_ne_zero"), H("Nonzero primitive affine coefficient"),
                StatementSource.FromAuthor(GeneratorFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("In every characteristic-seven field, a unit generating all units cannot "
                        + "equal minus one: the powers of minus one omit the unit two. There is no finiteness "
                        + "assumption in this conditional statement. The lift and the final path use the "
                        + "result to invert their label coefficient, including both primitive units of F7."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("characteristic-seven-detour-label-conservation"),
                DeclarationHandle.Create(Prefix + "splice_labels_bijective"), H("Exact off-target vector-label inventory"),
                StatementSource.FromAuthor(LabelFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every finite characteristic-seven field, every unit r with r+1 nonzero, "
                        + "and every nonzero u, successorLabel(r,u)(x) means vertexWithEndpoints(u)(splice(r,u)(x)) "
                        + "minus vertexWithEndpoints(u)(x). Its restriction to tails different from target "
                        + "is bijective onto all nonzero columns together with (0,u). The exact tail reindexing "
                        + "fixes target and redistributes the three changed labels, so deleting target removes "
                        + "exactly (0,-u). The path enumeration consumes this entire vector inventory."))), DescribeRole.Theorem))));
}
