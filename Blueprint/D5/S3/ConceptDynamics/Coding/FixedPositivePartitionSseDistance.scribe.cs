using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class FixedPositivePartitionSseDistanceDocument : IScribeDocumentDefinition
{
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; i--)
            body = Seq(Forall, Sp, F.Id(variables[i].Name.Value), Colon, Sp,
                variables[i].Domain, Comma, Sp, body);
        return body;
    }
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula Instances(Formula body, params Formula[] types)
    {
        for (var i = types.Length - 1; i >= 0; i--)
            body = Seq(OpenBracket, types[i], CloseBracket, Comma, Sp, body);
        return body;
    }
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Endpoint(Formula h, Formula p) => Call("partitionMatrix", h, p);
    private static Formula Chain(Formula h, Formula p, Formula r, Formula l) =>
        Call("ExchangeChain", Call("MonoidAlgebra", F.Id("Nat"), h), Endpoint(h, p), Endpoint(h, r), l);
    private static Formula GroupFamily(Formula body, bool nontrivial = false)
    {
        Formula h = F.Id("H");
        Formula[] instances = nontrivial
            ? [Call("Group", h), Call("Fintype", h), Call("Nontrivial", h)]
            : [Call("Group", h), Call("Fintype", h)];
        return All(Instances(body, instances), B("H", F.Id("Type")));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed positive group-ring partition family has exact maximum-coordinate exchange distance.",
        H("Fixed positive partition exchange distance"), Blocks(
            Describe.Lean(DescribeId.Create("fixed-positive-partition-exact-distance"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FixedPositivePartitionSseDistance.theorem32_2"),
                H("The entire fixed partition family"),
                StatementSource.FromAuthor(Disp(Claim())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let H be a finite nontrivial group, q its order, u the sum of its group elements, and write z(H)=q1-u in the integer group ring. Here smul denotes natural-number scalar multiplication, and toNat converts each integer coefficient to a natural number. A partition p of n is padded to n decreasing coordinates. Its nilpotent shift is the direct sum of the upper Jordan shifts of these lengths, flattened by prefix sums. Thus the coordinates and endpoint depend only on p.")),
                    Paragraph(Math(Disp(CenteredUniform()))),
                    Paragraph(Math(Disp(EndpointEntries()))),
                    Paragraph(Text("The displayed integer group-ring entries are strictly positive and hence determine natural group-ring entries. The baseline q cubed times n is fixed throughout the family.")),
                    Paragraph(Text("For neighboring partitions, rectangular zero-one block factors P and Q multiply to their respective shifts. Empty blocks are allowed. Flattening uses the two independent prefix-sum coordinates. The group-ring factors U=qJu+Pz and V=qJu+Qz have strictly positive natural coefficients and their actual products are the two endpoints. The fixed-mass partition geodesic therefore gives a chain of the exact displayed length, including length zero.")),
                    Paragraph(Text("For the lower bound, every competing rectangular chain supplies cumulative intertwining maps R and S whose two products are the endpoint powers of its length L. Intermediate dimensions may change and may be zero. Act on the kernel of rational augmentation, whose rational dimension is q-1. The uniform element annihilates this ideal, and the endpoint acts as q squared times its partition shift on each ideal coordinate.")),
                    Paragraph(Text("For the endpoint operators T and Q, set I=im(T to the j), M=S(I), and N=im(T to the j+L). The map R from M onto N intertwines the restrictions. It induces an actual surjection from M/QM onto N/TN. Rank-nullity and the embedding of the kernel on M into the kernel on im(Q to the j) compare the endpoint layer dimensions.")),
                    Paragraph(Math(Disp(LayerBound()))),
                    Paragraph(Text("Explicit endpoint shift coordinates evaluate each layer as q-1 times the number of partition parts exceeding its threshold. Cancel q-1, which is positive. Taking j equal to each part of the opposite partition proves the coordinate bound in both directions. Their maximum gives the lower bound on every chain length. No classification or partition assumption is imposed on the intermediate matrices."))),
                DescribeRole.Theorem))));

    private static Formula Claim()
    {
        Formula h = F.Id("H"), n = F.Id("n"), p = F.Id("p"), r = F.Id("r"), l = F.Id("L");
        Formula distance = Call("dInf", p, r);
        return GroupFamily(All(Imp(Le(D(1), n),
                And(Call("Nonempty", Chain(h, p, r, distance)),
                    Par(All(Imp(Chain(h, p, r, l), Le(distance, l)), B("L", F.Id("Nat")))))),
            B("n", F.Id("Nat")), B("p", Call("Partition", n)),
            B("r", Call("Partition", n))), nontrivial: true);
    }

    private static Formula CenteredUniform()
    {
        Formula h = F.Id("H");
        return GroupFamily(Equal(Call("z", h),
            Sub(Call("smul", Call("card", h), D(1)), Call("uniform", h))));
    }

    private static Formula EndpointEntries()
    {
        Formula h = F.Id("H"), n = F.Id("n"), p = F.Id("p");
        Formula i = F.Id("i"), j = F.Id("j"), q = Call("card", h);
        return GroupFamily(All(Equal(Call("partitionMatrix", h, p, i, j),
                Call("toNat", Add(
                    Call("smul", Mul(Call("power", q, D(3)), n), Call("uniform", h)),
                    Call("smul", Mul(q, Call("partitionShift", p, i, j)), Call("z", h))))),
            B("n", F.Id("Nat")), B("p", Call("Partition", n)),
            B("i", Call("Fin", n)), B("j", Call("Fin", n))));
    }

    private static Formula LayerBound()
    {
        Formula v = F.Id("V"), w = F.Id("W"), t = F.Id("T"), q = F.Id("Q");
        Formula r = F.Id("R"), s = F.Id("S"), l = F.Id("L"), j = F.Id("j");
        Formula rational = F.Id("Rational");
        Formula Rank(Formula f, Formula k) =>
            Call("finrank", rational, Call("range", Call("power", f, k)));
        Formula premises = And(Equal(Call("comp", t, r), Call("comp", r, q)),
            And(Equal(Call("comp", q, s), Call("comp", s, t)),
                Equal(Call("comp", r, s), Call("power", t, l))));
        Formula bound = Le(Sub(Rank(t, Add(j, l)), Rank(t, Add(Add(j, l), D(1)))),
            Sub(Rank(q, j), Rank(q, Add(j, D(1)))));
        return All(Instances(All(Imp(premises, Par(All(bound, B("j", F.Id("Nat"))))),
                B("T", Call("End", rational, v)), B("Q", Call("End", rational, w)),
                B("R", Call("LinearMap", rational, w, v)),
                B("S", Call("LinearMap", rational, v, w)), B("L", F.Id("Nat"))),
            Call("AddCommGroup", v), Call("Module", rational, v), Call("FiniteDimensional", rational, v),
            Call("AddCommGroup", w), Call("Module", rational, w), Call("FiniteDimensional", rational, w)),
            B("V", F.Id("Type")), B("W", F.Id("Type")));
    }
}
