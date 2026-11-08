using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class MayerKnillInfidelityScalingCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/MayerKnillInfidelityScalingCore.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite connected relations propagate uniform edge estimates to all pairs. Pure-state channel survival is the sum of squared Kraus amplitudes.",
        H("Finite graph estimates and Kraus amplitudes"), Blocks(
            Node("mk-core-survival", "kraus_survival", Survival(),
                "The channel action is expanded as the sum of Kj times the input projector times the conjugate transpose of Kj. Each term contributes the squared modulus of the corresponding survival amplitude. No normalization of the vector or trace-preservation assumption is needed."),
            Node("mk-core-graph", "finite_graph_squared_distance_bound", GraphBound(),
                "For a finite relation whose generated equivalence relation connects every pair, a positive constant controls every squared pair distance by any common nonnegative squared edge bound. The constant depends on the relation, and works for all maps into the normed additive group."))));
    private static DocumentBlock Node(string id, string name, Formula f, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    private static Formula V(string x) => F.Id(x);
    private static Formula Q(string a, string b) => Seq(Operatorname, Grp(V(a)), Dot, Operatorname, Grp(V(b)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string x, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(x), [.. args]);
    private static Formula Field(string x) => Seq(Mathbb, Grp(V(x)));
    private static Formula.BoundVariable B(string x, Formula t) => new(FormulaIdentifier.Create(x), t);
    private static Formula All(Formula.BoundVariable[] bs, Formula x) => new Formula.BindMany(FormulaQuantifier.ForAll, [.. bs], x);
    private static Formula Ex(Formula.BoundVariable[] bs, Formula x) => new Formula.BindMany(FormulaQuantifier.Exists, [.. bs], x);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Square(Formula a) => new Formula.Power(a, Num(2));
    private static Formula Norm(Formula a) => Seq(Vert, Sp, a, Sp, Vert);
    private static Formula Instance(string cls, Formula arg) => Seq(OpenBracket, Call(cls, arg), CloseBracket);
    private static Formula SumAt(string x, Formula t, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(V(x), Sp, Colon, Sp, t)), Sp, body);
    private static Formula Survival()
    {
        Formula a = V("a"), r = V("r"), psi = V("psi"), k = V("K"), j = V("j");
        Formula mat = Call("Matrix", a, a, Field("C"));
        Formula kj = App(k, j);
        Formula density = App(Q("PureStateHandshake", "rankOneDensity"), psi);
        Formula output = SumAt("j", Call("Fin", r), Mul(Mul(kj, density), App(Q("Matrix", "conjTranspose"), kj)));
        Formula lhs = App(Q("Complex", "re"), Call("dotProduct", Call("star", psi), App(Q("Matrix", "mulVec"), output, psi)));
        Formula rhs = SumAt("j", Call("Fin", r), Square(Norm(Call("dotProduct", Call("star", psi), App(Q("Matrix", "mulVec"), kj, psi)))));
        return All([B("a", V("Type"))], Seq(Instance("Fintype", a), Sp,
            All([B("r", Field("N")), B("psi", Arrow(a, Field("C"))), B("K", Arrow(Call("Fin", r), mat))], Eq(lhs, rhs))));
    }
    private static Formula GraphBound()
    {
        Formula iota = V("iota"), e = V("E"), r = V("r"), v = V("v"), eta = V("eta");
        Formula connected = All([B("i", iota), B("j", iota)], App(Q("Relation", "EqvGen"), r, V("i"), V("j")));
        Formula edges = All([B("a", iota), B("b", iota)], Imp(App(r, V("a"), V("b")),
            Le(Square(Norm(Sub(App(v, V("a")), App(v, V("b"))))), eta)));
        Formula pairs = All([B("i", iota), B("j", iota)],
            Le(Square(Norm(Sub(App(v, V("i")), App(v, V("j"))))), Mul(V("C"), eta)));
        Formula estimate = Ex([B("C", Field("R"))], And(Lt(Num(0), V("C")),
            All([B("v", Arrow(iota, e)), B("eta", Field("R"))], Imp(Le(Num(0), eta), Imp(edges, pairs)))));
        return All([B("iota", V("Type")), B("E", V("Type"))],
            Seq(Instance("Fintype", iota), Sp, Instance("NormedAddCommGroup", e), Sp,
                All([B("r", Arrow(iota, Arrow(iota, V("Prop"))))], Imp(connected, estimate))));
    }
}
