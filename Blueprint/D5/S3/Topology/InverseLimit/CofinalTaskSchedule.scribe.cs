using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class CofinalTaskScheduleDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/CofinalTaskSchedule.";
    private static Formula V(string x) => F.Id(x);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Ex(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(x), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Label => V("Label");
    private static Formula Pred => Arr(Label, Arr(Label, Arr(Label, Arr(V("Nat"), V("Prop")))));
    private static Formula Decoded => Call("fst", Call("reservation", V("a")));
    private static Formula Exec => Call("execute", V("a"), V("delayed"));
    private static Formula Pair(string a, string b) => Call("pair", V(a), V(b));
    private static Formula Above => Call("Lt", V("base"), V("a"));
    private static Formula Lower(string r) => Call("Le", V("omega"), Call("val", V(r)));
    private static Formula ReservationStatement() => Disp(All("task", V("Task"), All("base", Label,
        Ex("a", Label, And(Above, Eq(Decoded, V("task")))))));
    private static Formula ValidStatement() => Disp(All("a", Label, Imp(Lower("a"),
        All("delayed", Pred, Call("OrdinaryValid", V("a"), Call("fst", Exec), Call("snd", Exec))))));
    private static Formula OrdinaryStatement() => Disp(All("r", Label, All("d", Label,
        All("base", Label, Imp(Lower("r"), All("delayed", Pred,
            Ex("a", Label, And(Above, And(Call("OrdinaryValid", V("a"), V("r"), V("d")),
                And(Eq(Decoded, Call("inl", Pair("r", "d"))), Eq(Exec, Pair("r", "d"))))))))))));
    private static Formula DelayedStatement() => Disp(All("theta", Label, All("s", Label,
        All("t", Label, All("base", Label, All("k", V("Nat"), Imp(Lower("theta"),
            All("delayed", Pred, Imp(Call("delayed", V("theta"), V("s"), V("t"), V("k")),
                Ex("a", Label, And(Above, And(Call("DelayedValid", V("a"), V("theta"), V("s"), V("t")),
                    And(Eq(Decoded, Call("inr", Call("tuple", V("theta"), V("s"), V("t"), V("k")))),
                        Eq(Exec, Pair("theta", "t")))))))))))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed cofinal ordinal reservations with domain checks and a legal fallback.",
        H("Cofinal syntactic task schedule"),
        Blocks(
            Paragraph(Text(
                "Label is the literal set of ordinals below omegaOne from SignedProperLimit. "
                + "Task is the disjoint sum (Label times Label) plus (Label times Label times Label times Nat). "
                + "The first summand reserves ordinary pairs, and the second reserves delayed tuples. "
                + "Labels below omega are allowed in the syntax and rejected when their execution domains fail. "
                + "reservation is a single fixed equivalence Label to Task times Label. "
                + "Its definition contains no born spaces, clopens, points or measures, and requires no continuum hypothesis.")),
            Describe.Lean(DescribeId.Create("reservation-fibers-cofinal"),
                DeclarationHandle.Create(Owner + "exists_reservation_above"), H("Unbounded reservation fibers"),
                StatementSource.FromAuthor(ReservationStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every task and every proper ordinal base, some later stage decodes to that task. "
                    + "Finite cardinal products and sums give the equivalence. A bounded inverse fiber would inject "
                    + "uncountable Label into the countable segment below the successor of its bound, a contradiction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("executed-target-domain"),
                DeclarationHandle.Create(Owner + "execute_valid"), H("Every executed target is legal"),
                StatementSource.FromAuthor(ValidStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "OrdinaryValid(a,r,d) means omega<=r, r<=a and d<=a. "
                    + "DelayedValid(a,theta,s,t) means omega<=theta and theta,s,t<a. "
                    + "execute inspects the first component of reservation(a). A valid ordinary pair is returned literally. "
                    + "A delayed tuple returns (theta,t) only when DelayedValid and the supplied semantic predicate both hold. "
                    + "Every rejected case returns the literal pair (omega,0). For a>=omega this pair is legal. "
                    + "The semantic predicate can refer to already born data; classical branching makes no recognition-algorithm claim."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordinary-tasks-cofinally-executed"),
                DeclarationHandle.Create(Owner + "ordinary_cofinal"), H("Cofinal ordinary execution"),
                StatementSource.FromAuthor(OrdinaryStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every r>=omega, d and base, and every delayed predicate, a later stage reserves the ordinary pair "
                    + "and executes exactly (r,d). Choose its reservation beyond the maximum of base,r,d. "
                    + "Equality r=a or d=a is accepted by the execution rule, without asserting any old convergence law there."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("valid-delayed-tasks-cofinally-executed"),
                DeclarationHandle.Create(Owner + "delayed_cofinal"), H("Cofinal valid delayed execution"),
                StatementSource.FromAuthor(DelayedStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If theta>=omega and the semantic predicate holds for a tuple, every base has a later reservation "
                    + "strictly beyond theta,s,t, executing exactly (theta,t). The semantic predicate in this statement "
                    + "is fixed; applying it to a history requires proving that its already born data persist. "
                    + "This schedule constructs no successor carrier, signed enumeration, coherent history or signed A-G law."))), DescribeRole.Theorem))));
}
