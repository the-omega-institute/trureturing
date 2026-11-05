using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class SparsePavingMatchingObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A specified basis fails exactly when its admissible target union is a circuit-hyperplane.",
        H("Native sparse-paving matching obstruction"),
        Blocks(
            Node("admissibleUnion", Admissible(), DescribeRole.Definition,
                "The admissible targets are the union over the specified source set: a target belongs if at least one source element has its sum outside the source ground. The empty source set gives the empty union. Its complement in the target ground is the set of translations keeping every source element inside the source ground."),
            Node("BasisMatches", Matches(), DescribeRole.Definition,
                "The target-base existential ranges over all actual bases of the independently specified native target matroid. An equivalence of subtypes is a bijection between the source set and that target base. No representation, common ground, ordering, sign condition, or translation invariance of independence is required."),
            Node("basiswise_obstruction", Obstruction(), DescribeRole.Theorem,
                "Let M and N be finite loopless native matroids on a torsion-free abelian group, of common positive rank r and equal ground cardinality m. Only N and its dual are required to be paving. The circuit and flat predicates, and the extended natural rank, are those of the actual N. The equation rho(C) + 1 = r states the hyperplane rank without truncated subtraction. All four consequences are conditional on failure, so rank one, full-rank grounds, and rank-zero duals remain within the quantified domain. Zero may belong to the source ground.",
                "For each nonempty source subset X, the complement U of its admissible union satisfies X + (U union {0}) contained in the source ground. The pinned torsion-free Cauchy-Davenport theorem gives card(X) + card(U) at most m; zero contributes exactly once because it is excluded from the target ground. Subtracting from the target cardinality proves Hall's inequalities, including the empty-subset case separately.",
                "Apply the pinned finite Hall theorem to obtain distinct admissible representatives. In a sparse-paving matroid, dual paving bounds every nonspanning set by r elements: otherwise its complementary set is smaller than the dual rank and is independent, contradicting the native dual-rank identity. Paving then identifies any dependent r-element representative image as a circuit and a flat. If an admissible target lies outside that image, replace the representative at an index admitting it. A circuit with one element deleted spans the same flat, so adjoining the outside target gives an independent r-element set and hence an actual base. Thus failure forces the entire admissible union to equal the circuit-hyperplane. The converse follows because a base-sized injective image inside that union would equal the dependent circuit.",
                "Looplessness excludes a singleton circuit, giving r at least two. If m equals r, the rank equation contradicts the circuit-hyperplane condition. Complementary cardinalities give card(U) = m - r. Applying the same sumset estimate again makes the contained sumset have cardinality m, so it equals the source ground. The additive bound, dual-rank formula, and Hall theorem are reused library inputs; the native representative repair and their source-domain composition are the formalized inference. No claim of external novelty is made."))));

    private static DocumentBlock Node(string name, Formula formula, DescribeRole role,
        params string[] prose) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/SparsePavingMatchingObstruction." + name),
            H(name), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(prose.Select(p => Paragraph(Text(p))).ToArray()), role);

    private static Formula Admissible()
    {
        var rhs = And(In(V("b"), V("B")), Some("s", V("G"),
            And(In(V("s"), V("X")), Not(In(Add(V("s"), V("b")), V("A"))))));
        return Group(All("A", SetG, All("B", SetG, All("X", SetG, All("b", V("G"),
            Iff(In(V("b"), Call("admissibleUnion", V("A"), V("B"), V("X"))), rhs))))));
    }

    private static Formula Matches()
    {
        var rhs = Some("T", SetG, And(App(Q("N", "IsBase"), V("T")),
            Some("f", App(V("Equiv"), V("S"), V("T")), All("s", V("S"),
                Not(In(Add(V("s"), App(V("f"), V("s"))), V("A")))))));
        return Group(All("A", SetG, All("N", MatroidG, All("S", SetG,
            Iff(Call("BasisMatches", V("A"), V("N"), V("S")), rhs)))));
    }

    private static Formula Obstruction()
    {
        var c = Call("admissibleUnion", Q("M", "E"), Q("N", "E"), V("S"));
        var u = App(Q("Set", "sdiff"), Q("N", "E"), c);
        var failure = Not(Call("BasisMatches", Q("M", "E"), V("N"), V("S")));
        var obstruction = And(App(Q("N", "IsCircuit"), c), And(App(Q("N", "IsFlat"), c),
            And(Equal(Add(App(Q("N", "eRk"), c), D(1)), V("r")), Equal(Card(c), V("r")))));
        var consequences = And(Le(D(2), V("r")), And(Le(Add(V("r"), D(1)), V("m")),
            And(Equal(Card(u), Sub(V("m"), V("r"))),
                Equal(Add(V("S"), App(Q("Set", "union"), u, App(Q("Set", "singleton"), D(0)))), Q("M", "E")))));
        Formula body = And(Iff(failure, obstruction), Imp(failure, consequences));
        body = Imp(App(Q("M", "IsBase"), V("S")), body);
        body = All("S", SetG, body);
        body = Imp(Equal(Card(Q("N", "E")), V("m")), body);
        body = Imp(Equal(Card(Q("M", "E")), V("m")), body);
        body = Imp(Not(In(D(0), Q("N", "E"))), body);
        body = Imp(Call("IsSparsePaving", V("N")), body);
        body = Imp(Equal(Q("N", "eRank"), V("r")), body);
        body = Imp(Equal(Q("M", "eRank"), V("r")), body);
        body = Imp(Le(D(1), V("r")), body);
        body = All("r", Nat, All("m", Nat, body));
        body = Inst(Q("N", "Loopless"), body);
        body = Inst(Q("M", "Loopless"), body);
        body = Inst(Q("N", "Finite"), body);
        body = Inst(Q("M", "Finite"), body);
        return Group(Inst(Call("IsAddTorsionFree", V("G")), All("M", MatroidG, All("N", MatroidG, body))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula SetG => Call("Set", V("G"));
    private static Formula MatroidG => Call("Matroid", V("G"));
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(V(name), args);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, Par(Seq(V(n), Colon, Sp, t)), Comma, Sp, b);
    private static Formula Some(string n, Formula t, Formula b) => Seq(Exists, Sp, Par(Seq(V(n), Colon, Sp, t)), Comma, Sp, b);
    private static Formula Inst(Formula t, Formula b) => Seq(OpenBracket, t, CloseBracket, Sp, b);
    private static Formula Group(Formula b) => All("G", V("Type"), Inst(Call("AddCommGroup", V("G")), b));
    private static Formula In(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Not(Formula a) => Seq(Neg, Par(a));
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Card(Formula a) => App(Q("Set", "ncard"), a);
}
