using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class FiniteResponseTableDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite response tables compute least forgetting depths and deterministic sorted quotient sections for numbered incoming lifts.",
        H("Finite response tables"),
        Blocks(
            Paragraph(Text("Throughout, n and q are arbitrary natural numbers, A is a natural count matrix on Fin n, and L is an IncomingLift A (Fin q), including its given surjective projection and typed numbered-edge lifts. Nat subtraction is truncated. ForgettingDepths(L) denotes every natural d satisfying Forgets(L,d), without a bounded-depth restriction. In the displays, liftValue(L,edge(i,j,a),u) is the value of the typed lift in the guarded target fiber; proof arguments are implicit. sortedIndex and sortedEntry are the inverse and forward maps of the increasing Finset.orderIsoOfFin, and QuotientClass denotes the response class at the displayed depth.")),
            Describe.Lean(
                DescribeId.Create("lift-tables"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteResponseTable.LiftTables"),
                H("Numbered input arrays"), StatementSource.FromAuthor(Presentation("LiftTables")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The input stores a projection from Fin q to Fin n and a predecessor state for every ordered pair of base vertices, every parallel edge number and every state. Target-fiber checks precede use of entries."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lift-tables-valid"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteResponseTable.valid"),
                H("Finite input validation"), StatementSource.FromAuthor(Presentation("LiftTables.valid")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Boolean validator checks surjectivity and source-fiber coherence for each actual numbered edge whenever the supplied state lies in its target fiber. Zero edge counts and empty finite domains remain part of the input family."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("lift-tables-to-lift"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteResponseTable.toLift"),
                H("Typed incoming lift"), StatementSource.FromAuthor(Presentation("LiftTables.toLift")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A successful validator supplies the proof fields of the original IncomingLift structure. The projection and predecessor values are the supplied entries themselves."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("table"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteResponseTable.table"),
                H("Pathwise response table"), StatementSource.FromAuthor(Presentation("table")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Depth zero compares original state numbers. A successor first checks equality of projections, then checks the preceding table on both lifts along each identical numbered incoming edge. Parallel edges are never merged or averaged."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("forgets"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteResponseTable.forgets"),
                H("Whole-fiber forgetting"), StatementSource.FromAuthor(Presentation("forgets")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a given depth, every pair in each terminal projection fiber must have a true response-table bit. This is a pathwise forgetting test, not a marginal count."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("successes"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteResponseTable.successes"),
                H("Inclusive finite depth search"), StatementSource.FromAuthor(Presentation("successes")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The successful-depth set filters every natural number from zero through q minus n, inclusive, using the actual forgetting Boolean."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("minimum-depth"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteResponseTable.minimumDepth"),
                H("Least forgetting decision"), StatementSource.FromAuthor(Presentation("minimumDepth")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The result is some of the finite set minimum when a successful entry exists, and none otherwise. The implementation uses Finset.min'; the global completeness justification reuses the existing common nilpotency bound."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("members"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteResponseTable.members"),
                H("Response class enumeration"), StatementSource.FromAuthor(Presentation("members")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a supplied state, the class is the finite set of original state numbers whose table comparison with that state is true."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("representative"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteResponseTable.representative"),
                H("Least original state representative"), StatementSource.FromAuthor(Presentation("representative")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The representative is the least member of that class. The supplied state certifies nonemptiness; no inhabitant of an empty state domain is chosen."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("representatives"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteResponseTable.representatives"),
                H("Sorted representative set"), StatementSource.FromAuthor(Presentation("representatives")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fixed points of the representative operation form the finite set of class representatives, ordered by the original state numbers."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("class-of"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteResponseTable.classOf"),
                H("Dense sorted class numbers"), StatementSource.FromAuthor(Presentation("classOf")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse of Finset.orderIsoOfFin maps the computed least representative to its dense finite class index. Numbering follows the sorted state order."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("representative-at"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteResponseTable.representativeAt"),
                H("Computed quotient section"), StatementSource.FromAuthor(Presentation("representativeAt")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The forward order isomorphism maps a dense class index to its original representative state. Its domain depends on the computed representative count."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quotient-equiv"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteResponseTable.quotientEquiv"),
                H("Explicit quotient transport"), StatementSource.FromAuthor(Presentation("quotientEquiv")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Quotient.lift sends a semantic response class to its computed dense index. The inverse uses the computed section. The executable output uses neither Quotient.out nor Fintype.equivFin nor classical witness selection."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("parallel-identity-flip-tables"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteResponseTable.parallelIdentityFlipTables"),
                H("Numbered identity and swap input"), StatementSource.FromAuthor(Presentation("parallelIdentityFlipTables")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This concrete checker input has one base vertex, two states and two parallel edges. Edge number zero preserves the state; edge number one swaps the two states. The bounded checker tests both numbered lifts separately."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-response-table-refinement"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteResponseTable.finite_response_table_refinement"),
                H("Complete finite response and quotient refinement"),
                StatementSource.FromAuthor(Presentation("finite_response_table_refinement")), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("1. For every depth and every pair of states, the table bit is true exactly when the original IncomingLift response relation holds.")),
                    Paragraph(Text("2. For every depth, the whole-fiber forgetting Boolean is true exactly when the original Forgets predicate holds.")),
                    Paragraph(Text("3. For every natural depth, minimumDepth returns that depth exactly when it is least among all forgetting depths.")),
                    Paragraph(Text("4. minimumDepth is none exactly when no finite forgetting depth exists.")),
                    Paragraph(Text("5. Every returned depth is at most q minus n, with truncated natural subtraction and no added bound hypothesis.")),
                    Paragraph(Text("6. Equality of two adjacent whole response tables persists at every later depth.")),
                    Paragraph(Text("7. Two dense class numbers agree exactly when their states have the original response relation.")),
                    Paragraph(Text("8. Classifying the selected state of any dense class returns the same class index.")),
                    Paragraph(Text("9. Selecting the class of a state returns its computed least representative.")),
                    Paragraph(Text("10. Every computed representative is response-related to its input state.")),
                    Paragraph(Text("11. That representative is no greater than any response-related original state number.")),
                    Paragraph(Text("The proof relates the actual edge recursion to response_successor_iff and response_zero_and_step, connects forgetting to the private original pathwise kernel equivalence, and uses the existing common_nilpotency_forgetting_bound. The new algorithm refinement is distinct from those supplier results.")),
                    Paragraph(Text("The theorem concerns one incoming lift. Separate applications can supply independent least depths for two lifts, but this module does not construct a controlled trace, serialize a trace exporter or decide a fixed-positive-lag certificate.")),
                    Paragraph(Text("The domain permits zero states, zero base vertices, zero edge counts and depth zero. Surjectivity is part of the supplied IncomingLift. No essentiality, positive order, common lag, certificate or extra finite bound is added to this one-lift result."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Exists(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Conjoin(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var k = clauses.Length - 2; k >= 0; --k) result = And(clauses[k], result);
        return result;
    }
    private static Formula N => Id("n");
    private static Formula Q => Id("q");
    private static Formula A => Id("A");
    private static Formula L => Id("L");
    private static Formula D => Id("d");
    private static Formula U => Id("u");
    private static Formula V => Id("v");
    private static Formula Nat => Id("Nat");
    private static Formula Fin(Formula x) => Call("Fin", x);
    private static Formula Bit(Formula d, Formula u, Formula v) => Call("table", L, d, u, v);
    private static Formula Response(Formula d, Formula u, Formula v) => Call("response", L, d, u, v);
    private static Formula Forgot(Formula d) => Call("Forgets", L, d);
    private static Formula Minimum => Call("minimumDepth", L);
    private static Formula Rep(Formula d, Formula u) => Call("representative", L, d, u);
    private static Formula Reps(Formula d) => Call("representatives", L, d);
    private static Formula Class(Formula d, Formula u) => Call("classOf", L, d, u);
    private static Formula Selected(Formula d, Formula i) => Call("representativeAt", L, d, i);
    private static Formula Count(Formula d) => Call("card", Reps(d));
    private static Formula TrueBit(Formula bit) => Equal(bit, Id("true"));
    private static Formula Project(Formula owner, Formula u) => Call("project", owner, u);
    private static Formula Raw(Formula body) => All(body,
        B("n", Nat), B("q", Nat), B("A", Call("CountMat", N, N)));
    private static Formula Family(Formula body) => Raw(All(body, B("L", Call("IncomingLift", A, Fin(Q)))));
    private static Formula Depth(Formula body) => All(body, B("d", Nat));
    private static Formula States(Formula body) => All(body, B("d", Nat), B("u", Fin(Q)), B("v", Fin(Q)));
    private static Formula State(Formula body) => All(body, B("d", Nat), B("u", Fin(Q)));
    private static Formula Index(Formula body) => All(body, B("d", Nat), B("i", Fin(Count(D))));

    private static Formula Refinement()
    {
        var i = Id("i"); var t = Id("t");
        return Family(Conjoin(
            States(Iff(TrueBit(Bit(D, U, V)), Response(D, U, V))),
            Depth(Iff(TrueBit(Call("forgets", L, D)), Forgot(D))),
            Depth(Iff(Equal(Minimum, Call("some", D)), Call("IsLeast", Call("ForgettingDepths", L), D))),
            Iff(Equal(Minimum, Id("none")), new Formula.Not(Exists(Forgot(D), B("d", Nat)))),
            Depth(Imp(Equal(Minimum, Call("some", D)), Le(D, Subtract(Q, N)))),
            Depth(Imp(Equal(Call("table", L, Add(D, Num(1))), Call("table", L, D)),
                All(Equal(Call("table", L, Add(D, t)), Call("table", L, D)), B("t", Nat)))),
            States(Iff(Equal(Class(D, U), Class(D, V)), Response(D, U, V))),
            Index(Equal(Class(D, Selected(D, i)), i)),
            State(Equal(Selected(D, Class(D, U)), Rep(D, U))),
            State(Response(D, Rep(D, U), U)),
            States(Imp(Response(D, V, U), Le(Rep(D, U), V)))));
    }

    private static Formula Presentation(string name)
    {
        var i = Id("i"); var j = Id("j"); var a = Id("a"); var t = Id("T");
        var tableType = Call("LiftTables", N, Q, A);
        var edge = Call("edge", i, j, a);
        var members = Call("members", L, D, U);
        var successes = Call("successes", L);
        var sameFiber = Equal(Project(L, U), Project(L, V));
        var sourceIncidence = All(Imp(Equal(Project(t, U), j),
            Equal(Project(t, Call("predecessor", t, i, j, a, U)), i)),
            B("i", Fin(N)), B("j", Fin(N)), B("a", Fin(Call("entry", A, i, j))), B("u", Fin(Q)));
        Formula value = name switch
        {
            "LiftTables" => Raw(Call("Fields", tableType,
                Call("project", new Formula.TypeArrow(Fin(Q), Fin(N))),
                Call("predecessor", All(Fin(Q), B("i", Fin(N)), B("j", Fin(N)),
                    B("a", Fin(Call("entry", A, i, j))), B("u", Fin(Q)))))),
            "LiftTables.valid" => Raw(All(Equal(Call("valid", t), Call("decide", And(
                All(Exists(Equal(Project(t, U), i), B("u", Fin(Q))), B("i", Fin(N))), sourceIncidence))), B("T", tableType))),
            "LiftTables.toLift" => Raw(All(And(
                Equal(Call("project", Call("toLift", t, Id("h"))), Call("project", t)),
                All(Equal(Call("liftValue", Call("toLift", t, Id("h")), edge, U),
                    Call("predecessor", t, i, j, a, U)),
                    B("i", Fin(N)), B("j", Fin(N)), B("a", Fin(Call("entry", A, i, j))),
                    B("u", Fin(Q)), B("hu", Equal(Project(t, U), j)))),
                B("T", tableType), B("h", TrueBit(Call("valid", t))))),
            "table" => Family(States(And(
                Equal(Bit(Num(0), U, V), Call("decide", Equal(U, V))),
                Equal(Bit(Add(D, Num(1)), U, V), Call("andBool", Call("decide", sameFiber),
                    Call("decide", All(Imp(And(Equal(Project(L, U), j), Equal(Project(L, V), j)),
                        TrueBit(Bit(D, Call("liftValue", L, edge, U), Call("liftValue", L, edge, V)))),
                        B("i", Fin(N)), B("j", Fin(N)), B("a", Fin(Call("entry", A, i, j)))))))))),
            "forgets" => Family(Depth(Equal(Call("forgets", L, D), Call("decide",
                All(Imp(sameFiber, TrueBit(Bit(D, U, V))), B("u", Fin(Q)), B("v", Fin(Q))))))),
            "successes" => Family(Depth(Iff(Mem(D, successes), And(Le(D, Subtract(Q, N)), TrueBit(Call("forgets", L, D)))))),
            "minimumDepth" => Family(Equal(Minimum, Call("ifThenElse", Call("Nonempty", successes),
                Call("some", Call("minimumElement", successes)), Id("none")))),
            "members" => Family(States(Iff(Mem(V, members), TrueBit(Bit(D, V, U))))),
            "representative" => Family(State(Equal(Rep(D, U), Call("minimumElement", members)))),
            "representatives" => Family(State(Iff(Mem(U, Reps(D)), Equal(Rep(D, U), U)))),
            "classOf" => Family(State(Equal(Class(D, U), Call("sortedIndex", Reps(D), Rep(D, U))))),
            "representativeAt" => Family(Index(Equal(Selected(D, i), Call("sortedEntry", Reps(D), i)))),
            "quotientEquiv" => Family(And(
                State(Equal(Call("apply", Call("quotientEquiv", L, D), Call("QuotientClass", L, D, U)), Class(D, U))),
                Index(Equal(Call("inverseApply", Call("quotientEquiv", L, D), i), Call("QuotientClass", L, D, Selected(D, i)))))),
            "parallelIdentityFlipTables" => All(And(
                Equal(Project(Id("parallelIdentityFlipTables"), U), Num(0)),
                Equal(Call("predecessor", Id("parallelIdentityFlipTables"), Num(0), Num(0), a, U),
                    Call("ifThenElse", Equal(a, Num(0)), U, Call("ifThenElse", Equal(U, Num(0)), Num(1), Num(0))))),
                B("a", Fin(Num(2))), B("u", Fin(Num(2)))),
            "finite_response_table_refinement" => Refinement(),
            _ => throw new ArgumentException("Unknown finite-response declaration", nameof(name)),
        };
        return FormulaDsl.Disp(value);
    }
}
