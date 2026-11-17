using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class NativeLocalSourceExecutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/NativeLocalSourceExecution.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Guarded native source execution, birth sorts and exact successful-event indices.",
        H("Ordered source syntax and original local guards"), Blocks(
            Paragraph(Text("Source is the existing free ordered binary magma over Bool: true labels alpha and false labels beta. Address is List Bool, with false for a left edge and true for a right edge. Event is Address times Bool. For every t : Source, p : Address and k : Bool, edit t p k navigates existing logical binary children. At a reached leaf labelled b it succeeds exactly when b equals k, returning its original local replacement. Thus true is precisely promotion P at alpha and false is precisely split S at beta. A wrong tag, branch target, absent address or attempted descent through a leaf rejects. Beta's unary material marker is excluded from this logical navigation.")),
            Paragraph(Text("For every t : Source and es : List Event, replay t es executes these guarded events chronologically, propagating rejection. For every t : Source, oldFrontier t is the finite left-first list of its original leaf addresses and their actual labels. The list is sealed before replay. Each branch concatenates the left list, prefixed by false, and the right list, prefixed by true. Newly created leaves do not enter this list. For every t : Source, leftmost t follows only left logical children; splitLeft t changes just its terminal beta on the native domain.")),
            Paragraph(Text("For every a : Bool and t : Source, native a t is the birth-sort test: at a leaf labelled b it tests whether a is true or b is false; at a branch it tests the left child at false and the right child at true. For every t : Source, Native t means native false t is true. The root sort true is exactly attainment from alpha by the original guarded events. The root sort false is exactly such attainment with alpha excluded. These tests retain all irregular shapes and every finite depth, with no composition restriction.")),
            Paragraph(Text("For every t : Source, eventIndex t is the number of alpha leaves plus twice the number of beta leaves, minus one. This is an alpha-origin successful-event count. It is not material size, elapsed time or replacement quantity.")),
            Paragraph(Text("In the statement, of is the labelled leaf constructor, some is the successful Option constructor, and List is the finite-list type constructor. The function length counts leaves on Source and entries on lists. The function composition returns the ordered pair of alpha and beta leaf counts. The function add denotes natural addition or componentwise addition of these natural pairs, and pair denotes an ordered pair.")),
            Describe.Lean(DescribeId.Create("native-guarded-execution"), DeclarationHandle.Create(Prefix + "native_execution"),
                H("Full frontier replay, current leftmost splitting and attained sorts"),
                StatementSource.FromAuthor(NativeExecutionFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Lift a finite guarded replay into either child of a fixed branch. Chronological concatenation then proves, by induction over the entire original tree, that the sealed frontier reaches precisely the existing global substitution. The proof covers both leaf tags and every ordered pair. It executes one event per original leaf. The left descent of a native tree ends at beta, so its single S guard succeeds; induction preserves the right siblings and gives the alpha-translation composition law.")),
                    Paragraph(Text("Each successful P or S increases eventIndex by exactly one. Address induction transports that equality through an arbitrary enclosing ordered source; chronological induction sums it over a successful replay. Leaf-count total is directly the existing ActualObserverAbsorbingNormalization.composition_total, and substitution composition is directly the existing fiberMap law. Together with the native beta count this gives the full-frontier increment equal to the old number of leaves, the leftmost-split increment one, and eventIndex one exactly at beta.")),
                    Paragraph(Text("For the attained-domain equivalence, a guarded edit preserves the birth-sort test, and hence so does every successful replay. Conversely construct every accepted target from its birth tag. At a branch, perform its necessary root promotion, if any, and root split, then replay the constructed left child from beta and the right child from alpha. Prefixing the two child event lists gives actual legal guarded source executions. Thus no unattained tree is silently admitted and no attained beta-positive entry is omitted.")),
                    Paragraph(Text("The physical interpretation retains one authentically bound root, source and epoch, current exclusive rights, stable finite traversal and actual reached operands. Every primitive performs all ancestral-tape maintenance and consumes its literal reply, acknowledgement and inner return. A completed outer F or G additionally consumes its own full reply, acknowledgement and real return. These are completion and resource premises of the native installation; logical replay does not certify controller bytes or an unfinished outer call. Finite reference, exact counter, frontier, traversal, workspace and output backing are supplied for each finite run. There are no interleaved source edits and no fixed finite arena for all histories."))
                ), DescribeRole.Theorem)
        )));

    private static Formula NativeExecutionFormula()
    {
        Formula source = FormulaDsl.Id("Source");
        Formula events = Call("List", FormulaDsl.Id("Event"));

        Formula All(Formula body, params Formula.BoundVariable[] variables) =>
            new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
        Formula Exists(string name, Formula domain, Formula body) =>
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
        Formula And(params Formula[] items)
        {
            var result = items[0];
            for (var i = 1; i < items.Length; i++)
                result = new Formula.Logic(result, FormulaLogicOperator.And, items[i]);
            return result;
        }
        Formula Implies(Formula left, Formula right) =>
            new Formula.Logic(left, FormulaLogicOperator.Implies, right);
        Formula Iff(Formula left, Formula right) =>
            new Formula.Logic(left, FormulaLogicOperator.Iff, right);
        Formula Eq(Formula left, Formula right) =>
            new Formula.Relation(left, FormulaRelationOperator.Equal, right);
        Formula Ne(Formula left, Formula right) =>
            new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
        Formula Call(string name, params Formula[] arguments) =>
            new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
        Formula App(string name, params Formula[] arguments) => Call(name, arguments);
        Formula Num(long value) => new Formula.Number(value);
        Formula.BoundVariable B(string name, Formula domain) =>
            new(FormulaIdentifier.Create(name), domain);
        Formula Of(bool value) => App("of", FormulaDsl.Id(value ? "true" : "false"));
        Formula Some(Formula value) => App("some", value);
        Formula Length(Formula value) => App("length", value);
        Formula Native(Formula value) => App("Native", value);
        Formula NativeAt(bool a, Formula value) => App("native", FormulaDsl.Id(a ? "true" : "false"), value);
        Formula EventIndex(Formula value) => App("eventIndex", value);
        Formula OldFrontier(Formula value) => App("oldFrontier", value);
        Formula Replay(Formula value, Formula word) => App("replay", value, word);
        Formula Substitution(Formula value) => App("substitution", value);
        Formula Composition(Formula value) => App("composition", value);
        Formula Edit(Formula t, Formula p, Formula k) => App("edit", t, p, k);
        Formula Leftmost(Formula value) => App("leftmost", value);
        Formula SplitLeft(Formula value) => App("splitLeft", value);

        var t = FormulaDsl.Id("t");
        var u = FormulaDsl.Id("u");
        var es = FormulaDsl.Id("es");
        var clause1 = All(
            And(
                Eq(Replay(t, App("oldFrontier", t)), Some(Substitution(t))),
                Eq(Length(OldFrontier(t)), Length(t)),
                Native(Substitution(t))),
            B("t", source));
        var clause2 = All(
            Implies(
                Native(t),
                And(
                    Eq(Edit(t, Leftmost(t), FormulaDsl.Id("false")), Some(SplitLeft(t))),
                    Native(SplitLeft(t)),
                    Eq(Composition(SplitLeft(t)),
                        App("add", Composition(t), App("pair", Num(1), Num(0)))))),
            B("t", source));
        var clause3 = All(
            Implies(
                Eq(Replay(t, es), Some(u)),
                Eq(EventIndex(u), App("add", EventIndex(t), Length(es)))),
            B("t", source), B("u", source), B("es", events));
        var clause4 = All(
            Implies(
                Native(t),
                And(
                    Eq(EventIndex(Substitution(t)), App("add", EventIndex(t), Length(t))),
                    Eq(EventIndex(SplitLeft(t)), App("add", EventIndex(t), Num(1))),
                    Iff(Eq(EventIndex(t), Num(1)), Eq(t, Of(false))))),
            B("t", source));
        var clause5 = All(
            Iff(
                Exists("es", events, Eq(Replay(Of(true), es), Some(t))),
                Eq(NativeAt(true, t), FormulaDsl.Id("true"))),
            B("t", source));
        var clause6 = All(
            Iff(
                Native(t),
                And(
                    Exists("es", events, Eq(Replay(Of(true), es), Some(t))),
                    Ne(t, Of(true)))),
            B("t", source));
        return Disp(And(clause1, clause2, clause3, clause4, clause5, clause6));
    }
}
