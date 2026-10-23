using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Sequenceability;

internal sealed class RowOrbitLiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Sequenceability/RowOrbitLift.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula IffF(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, b, Close);
    private static Formula K => V("K");
    private static Formula R => V("r");
    private static Formula C => V("c");
    private static Formula States => Seq(Call("Fin", D(4)), Sp, Times, Sp, K);
    private static Formula Row => Call("rowReturn", R, C);
    private static Formula Lift => Call("lift", R, C);
    private static Formula FieldBind(Formula body) => All("K", Call("Type"),
        All("f", Call("Field", K), All("finite", Call("Finite", K), body)));
    private static Formula Generator => All("z", Call("Units", K),
        Ex("n", Call("Nat"), Eqn(new Formula.Power(R, V("n")), V("z"))));
    private static Formula OrbitFormula() => Disp(FieldBind(All("r", Call("Units", K),
        Imp(Generator, All("c", K, All("a", K, All("b", K,
            IffF(Call("SameCycle", Row, V("a"), V("b")),
                IffF(Eqn(V("a"), C), Eqn(V("b"), C))))))))));
    private static Formula LiftFormula()
    {
        Formula outside = Seq(OpenBrace, V("v"), Colon, Seq(Call("ZMod", D(5)), Sp, Times, Sp, K),
            Mid, Ne(Call("fst", V("v")), D(0)), CloseBrace);
        Formula cycles = All("v", States, All("w", States,
            IffF(Call("SameCycle", Lift, V("v"), V("w")),
                IffF(Eqn(Call("initialRow", V("v")), C), Eqn(Call("initialRow", V("w")), C)))));
        Formula round = All("h", K, Eqn(
            new Formula.Apply(new Formula.Power(Lift, D(4)), [Pair(D(0), V("h"))]),
            Pair(D(0), new Formula.Apply(Row, [V("h")]))));
        Formula body = Ex("r", Call("Units", K),
            And(Ne(new Formula.Binary(Call("coe", R), FormulaBinaryOperator.Add, D(1)), D(0)),
            And(cycles, And(Call("BijOn", Call("edgeLabel", R, C), Call("univ"), outside),
            And(Call("BijOn", Call("vertex"), Call("univ"), outside), round)))));
        return Disp(FieldBind(All("char", Call("CharP", K, D(5)), All("c", K, body))));
    }
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Affine row orbits give exact lifted cycles and differences over finite fields of characteristic five.",
        H("Affine row orbits and a characteristic-five lift"), Blocks(
            Paragraph(Text("All universe levels, field structures and finite fields in the displayed quantifiers are included. "
                + "Operations use the bound field structure f. The map rowReturn(r,c) sends h to c+r(h-c), where r is a unit. "
                + "SameCycle is the orbit relation of the actual permutation under integer powers.")),
            Describe.Lean(DescribeId.Create("row-orbit-lift-row-same-cycle-iff"),
                DeclarationHandle.Create(Prefix + "row_same_cycle_iff"), H("Two affine row orbits"),
                StatementSource.FromAuthor(OrbitFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("When every unit is a natural power of r, the center c is fixed and every "
                        + "other row belongs to one orbit. For a and b different from c, choose a power of r "
                        + "equal to (b-c)/(a-c). The n-th return is c+r^n(a-c), so that power sends a to b. "
                        + "Conversely, a permutation orbit meeting a fixed point contains only that point."))),
                DescribeRole.Theorem),
            Paragraph(Text("The state space is Fin(4) times K. Its actual vertices are vertex(i,h)=(column(i),h), "
                + "where column=(1,2,4,3) in ZMod(5). The successor lift(r,c) sends (0,h),(1,h),(2,h) "
                + "to (1,-h),(2,-h),(3,-h), respectively, and sends (3,h) to (0,-rh+(1-r)c). "
                + "The first row initialRow(i,h) is h at phases 0 and 2 and -h at phases 1 and 3. "
                + "The edgeLabel is vertex(lift(r,c)(v))-vertex(v), with coefficient one.")),
            Describe.Lean(DescribeId.Create("row-orbit-lift-exists-characteristic-five-lift"),
                DeclarationHandle.Create(Prefix + "exists_characteristic_five_lift"),
                H("Exact cycles and closing-edge inventory over every finite rowfield"),
                StatementSource.FromAuthor(LiftFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Choose a generator of the finite field's unit group. It cannot be -1: "
                        + "powers of -1 are 1 or -1, whereas 2 is neither in characteristic five. Thus r+1 "
                        + "is nonzero. Four successor steps return to phase zero by rowReturn(r,c). "
                        + "The preceding orbit theorem and the first three successor steps prove the exact "
                        + "SameCycle criterion for arbitrary states, including the closing edge.")),
                    Paragraph(Text("The first coordinates of the four edge labels are 1,2,4,3. Their row "
                        + "coordinates are -2h,-2h,-2h and -(r+1)h+(1-r)c. Each row map is bijective, "
                        + "so BijOn means that every vector with nonzero first coordinate occurs exactly "
                        + "once as a label. The separate vertex BijOn states the same exact inventory for "
                        + "vertices. This covers arbitrary finite extensions in characteristic five; no "
                        + "bound on their degree is imposed.")),
                    Paragraph(Text("These are the row-lift ingredients for the dependent-hole construction. "
                        + "A relative detour still requires the three-cut reconnection. The prime seed, "
                        + "the different two-cut construction for primes at least seven, dimension induction "
                        + "and transport to the original vector-space coordinates are not asserted here."))),
                DescribeRole.Theorem))));
}
