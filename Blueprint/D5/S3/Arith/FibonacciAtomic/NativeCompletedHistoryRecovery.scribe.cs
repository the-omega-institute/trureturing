using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class NativeCompletedHistoryRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/NativeCompletedHistoryRecovery.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unknown-entry native completed histories have an executable inverse and only the beta first-choice ambiguity.",
        H("The completed native menu and its acquired inputs"), Blocks(
            Paragraph(Text("Letter has precisely the distinct constructors F and G. For every X : Letter and t : Source, act X t is the existing global substitution when X is F, and the current leftmost-beta split when X is G. The guarded execution theorem identifies F with replay of the sealed OLD frontier and G with the acquired current leftmost split. For every t : Source and W : List Letter, run t W folds those actual logical actions in chronological order. The empty word leaves t unchanged. The domain Native contains every attained beta-positive tree, with arbitrary unknown composition, depth and shape.")),
            Paragraph(Text("For every n0 : Nat and z : Source, recover n0 z receives only the authenticated exact entry event index and acquired final logical syntax. It does not receive the old tree, its composition, its depth, a word length, a retained pair or another acquired field. The executable computation rejects indices at most one; the beta case is classified separately. The syntax input is the existing full ordered labelled Source type, including nonnative inputs.")),
            Paragraph(Text("For every e : NativeLocalSourceExecution.Event, toCall e selects the original Geometry.NativeGuardedLeafRepair.Call.promote or Call.split at its literal logical address. For every c : Geometry.NativeGuardedLeafRepair.Call, fromCall c recovers its address and original guard tag. Address induction identifies edit with the existing subtree guard and existing replacement; chronological induction proves equality of replay with the canonical guarded-call interpreter on the converted list, including every rejected input. Converting in both directions identifies Native with actual guarded attainment from alpha with alpha excluded.")),
            Paragraph(Text("For every X : Letter and t : Source, macroCalls X t seals the original frontier for F and acquires the current leftmost beta for G. For every t : Source and W : List Letter, primitiveWord t W concatenates these actual canonical calls, recomputing each next macro frontier on its current input. Guarded-call concatenation and the one-macro correspondence prove that the entire primitive expansion reaches run t W on every native input. Its exact length is the final event index minus the entry event index. This is a proved source-run correspondence, without an assumed decoder-correctness certificate.")),
            Paragraph(Text("For every native t : Source, actual guarded attainment and the existing run_preserves_D imply the original material birth condition D. For every native t : Source, W : List Letter, labels : RawMap, next : Integer and x : Value, the existing history_preserves_values applied to the proved primitiveWord trace supplies labelsPrime : RawMap, nextPrime : Integer and y : Value for an actual nativeRun whose source is run t W. Every old material address keeps its value and every fresh material address has value zero. This connects the completed logical word to the existing guarded source, raw-label and value execution; it does not certify an installation's serialized outer return.")),
            new DocumentBlock.Section(H("Native overlap and the exact predecessor"), Blocks(
                Paragraph(Text("For every z : Source, collapse z searches only its left spine and collapses the deepest beta/alpha pair to beta. Failure means there is no such native G predecessor. For every z p : Source, collapse z equal to some p implies splitLeft p equal to z, and Native z implies Native p. For every native t : Source, collapse of splitLeft t returns t.")),
                Paragraph(Text("For every t : Source, H t retains its terminal left leaf and globally substitutes each old right subtree on the left spine. On a native input t, substitution t equals splitLeft of H t, and H t is native. Collapse of H t always fails: each deepest right subtree is a substitution image and cannot be alpha. Its event index plus one equals the entry event index plus its old leaf count. Consequently, at a multileaf native entry its event index strictly exceeds the entry index. This is the native overlap boundary, rather than a disjoint-image root-graft argument.")),
                Paragraph(Text("For every z : Source, rhoPredecessor z runs the existing inverseCode at rank one on encode z, expands the candidate and checks literal forward substitution equality. The existing finite_normal_inverse supplies the candidate on every actual image; the existing public substitution injectivity identifies its expansion. The final equality test rejects any phantom candidate on other inputs. No new copy of the substitution parser or assumption of decoder correctness is used.")),
                Paragraph(Text("For every n0 : Nat and z : Source above the entry index, previous first requires a successful collapse c. It chooses G when c has index n0 or itself admits collapse. Otherwise it requires a successful rhoPredecessor and a native predecessor and chooses F. In an actual G-ending history, c is the preceding tree: it is either the entry or a nonempty macro output. In an actual F-ending history from a multileaf tree s, c is H s: collapse fails there and its index strictly exceeds n0. Thus this test selects the actual last letter, including histories whose entry and word length were unknown."))
            )),
            new DocumentBlock.Section(H("Total finite decoding and both inverse laws"), Blocks(
                Paragraph(Text("For every fuel : Nat, n0 : Nat and z : Source, recoverFuel returns a pair whose first component is a Nat accepted-transition count and whose second component is an optional pair of entry Source and literal List Letter. It rejects a nonnative tree, an index at most one, or a current index below n0. Equality of indices returns the current tree and empty word. Otherwise a positive fuel permits exactly one previous transition, with an explicit test that its index lies between n0 and the current index, strictly below the latter. It recursively decodes that predecessor, increments the returned count once even if a later check rejects, and appends the selected last letter to a successful answer. For every n0 : Nat and z : Source, recover uses exactly eventIndex z minus n0 as fuel and projects that computation’s answer; recoverySteps projects the same computation’s count. Structural recursion on this computed natural fuel terminates on every finite input.")),
                Describe.Lean(DescribeId.Create("complete-native-history-recovery"), DeclarationHandle.Create(Prefix + "completed_history_recovery"),
                    H("All unknown native entries, literal words and the exact beta fibre"),
                        StatementSource.FromAuthor(CompletedHistoryRecoveryFormula()), AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("Induct on the chronological word by appending its last letter. The native overlap boundary selects the actual predecessor and strict event growth supplies sufficient smaller fuel. This proves recovery of the entire original pair on every actual input, with the empty word included. Conversely induct on decoding fuel. Every accepted predecessor really replays to the supplied syntax; the accepted base is native and has exactly the supplied entry index. Hence every accepted answer is in the actual image. The public success equivalence states the entry domain directly as actual canonical guarded attainment from alpha. Positive entry index excludes alpha and the proved sort equivalence supplies Native; no attainment witness is a runtime input. The success equivalence yields rejection exactly off that image, and applying it to two purported answers proves injectivity even across different unknown entries.")),
                        Paragraph(Text("Every successful primitive adds one event. Every macro adds at least one. Induction on fuel bounds the accepted-transition count on every input, including inputs eventually rejected. On success that count equals the returned literal word length. Thus the number of accepted predecessor transitions is at most the final event index minus n0. Every accepted previous transition has a strictly smaller event index. This counts descriptive predecessor transitions; it supplies no bit-complexity, physical driver-duration or uniform workspace bound.")),
                        Paragraph(Text("At index one the attained entry is beta. Strict event growth makes its empty word the only history ending again at beta. Both first letters send beta to K, the ordered beta/alpha pair of index two. Applying the already established index-two inverse to any nonempty beta endpoint gives one unique entire suffix U : List Letter. Its full fibre consists exactly of F followed by U and G followed by U. No other word or entry belongs to this fibre.")),
                        Paragraph(Text("For every supplement type A, function E from literal words to A and suffix U, there exists a decoder of E on this concrete fixed endpoint fibre exactly when E gives different values on F followed by U and G followed by U. Equal supplementary values force the same decoder answer for two distinct targets. Distinct values select their first letter and share the recovered suffix. For every W : List Letter, firstChoice W is true exactly when its first letter is F, and is false at G or the empty word. This explicit Boolean supplement has a checked decoder on each nonempty endpoint fibre. Thus one binary first-macro choice is necessary and sufficient under this conditioning. An actual retained request or script channel can already supply that distinction; no additional bit is then required. This is a two-point native fibre statement, with no general coding or information theorem substituted for it.")),
                        Paragraph(Text("The same-source acquisition, rights, lawful stationary traversal, complete ancestral tapes and finite backing premises remain explicit. All primitives and outer macros must have completed their actual replies, acknowledgements and returns. Parsed syntax alone does not certify that completion. The inverse computes descriptions only. It grants no source reset, deletion, physical undo, old pointer restoration, copying authority, elapsed-time recovery or reduced total installation storage. The unfinished-history join can use this completed inverse only for macros whose outer returns have actually completed."))
                    ), DescribeRole.Theorem)
            ))
        )));

    private static Formula CompletedHistoryRecoveryFormula()
    {
        Formula source = Id("Source");
        Formula nat = Id("Nat");
        Formula letter = Id("Letter");
        Formula letters = Call("List", letter);
        Formula calls = Id("NativeGuardedLeafRepairCall");
        Formula callList = Call("List", calls);
        Formula eventList = Call("List", Id("Event"));
        Formula address = Id("Address");

        Formula All(Formula body, params Formula.BoundVariable[] variables) =>
            new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
        Formula Exists(string name, Formula domain, Formula body) =>
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
        Formula ExistsUnique(string name, Formula domain, Func<Formula, Formula> property)
        {
            var chosen = Id(name);
            var other = Id(name + "2");
            return Exists(name, domain,
                And(property(chosen), All(Implies(property(other), Eq(other, chosen)), B(name + "2", domain))));
        }
        Formula And(params Formula[] items)
        {
            var result = items[0];
            for (var i = 1; i < items.Length; i++)
                result = new Formula.Logic(result, FormulaLogicOperator.And, items[i]);
            return result;
        }
        Formula Or(Formula left, Formula right) =>
            new Formula.Logic(left, FormulaLogicOperator.Or, right);
        Formula Implies(Formula left, Formula right) =>
            new Formula.Logic(left, FormulaLogicOperator.Implies, right);
        Formula Iff(Formula left, Formula right) =>
            new Formula.Logic(left, FormulaLogicOperator.Iff, right);
        Formula Eq(Formula left, Formula right) =>
            new Formula.Relation(left, FormulaRelationOperator.Equal, right);
        Formula Ne(Formula left, Formula right) =>
            new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
        Formula Lt(Formula left, Formula right) =>
            new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
        Formula Le(Formula left, Formula right) =>
            new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
        Formula Call(string name, params Formula[] arguments) =>
            new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
        Formula App(string name, params Formula[] arguments) => Call(name, arguments);
        Formula Num(long value) => new Formula.Number(value);
        Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
        Formula.BoundVariable B(string name, Formula domain) =>
            new(FormulaIdentifier.Create(name), domain);
        Formula Of(bool value) => App("of", Id(value ? "true" : "false"));
        Formula Some(Formula value) => App("some", value);
        Formula Pair(Formula left, Formula right) => App("pair", left, right);
        Formula Run(Formula t, Formula w) => App("run", t, w);
        Formula Act(Formula x, Formula t) => App("act", x, t);
        Formula Recover(Formula n0, Formula z) => App("recover", n0, z);
        Formula Previous(Formula n0, Formula z) => App("previous", n0, z);
        Formula EventIndex(Formula t) => App("eventIndex", t);
        Formula Native(Formula t) => App("Native", t);
        Formula Length(Formula value) => App("length", value);
        Formula Attained(Formula t) =>
            Exists("cs", callList,
                Eq(App("guardedRun", Of(true), Id("cs")), Some(t)));
        Formula Mem(Formula p, Formula set) => App("mem", p, set);
        Formula Material(Formula t) => App("material", t);
        Formula Word(Formula t, Formula w) => App("primitiveWord", t, w);
        Formula NativeRun(Formula t, Formula labels, Formula next, Formula x, Formula word) =>
            App("nativeRun", t, labels, next, x, word);
        Formula Empty() => Id("nil");
        Formula Cons(Formula head, Formula tail) => App("cons", head, tail);
        Formula LetterF() => Id("F");
        Formula LetterG() => Id("G");

        var n0 = Id("n0");
        var z = Id("z");
        var t = Id("t");
        var p = Id("p");
        var w = Id("W");
        var x = Id("X");
        var s = Id("s");
        var v = Id("V");

        var clause1 = All(
            Iff(
                Eq(Recover(n0, z), Some(Pair(t, w))),
                And(Lt(Num(1), n0), Attained(t),
                    Eq(EventIndex(t), n0), Eq(Run(t, w), z))),
            B("n0", nat), B("z", source), B("t", source), B("W", letters));
        var clause2 = All(
            Iff(
                Eq(Recover(n0, z), Id("none")),
                new Formula.Not(Exists("t", source,
                    Exists("W", letters,
                        And(Lt(Num(1), n0), Attained(Id("t")),
                            Eq(EventIndex(Id("t")), n0), Eq(Run(Id("t"), Id("W")), z)))))),
            B("n0", nat), B("z", source));
        var clause3 = All(
            Implies(
                Eq(Recover(n0, z), Some(Pair(t, w))),
                And(Le(Length(w), App("subtract", EventIndex(z), n0)),
                    Eq(App("recoverySteps", n0, z), Length(w)))),
            B("n0", nat), B("z", source), B("t", source), B("W", letters));
        var clause4 = All(
            Implies(
                Native(z),
                Implies(
                    Eq(Previous(n0, z), Some(Pair(p, x))),
                    And(Native(p), Eq(Act(x, p), z), Lt(EventIndex(p), EventIndex(z))))),
            B("n0", nat), B("z", source), B("p", source), B("X", letter));
        var clause5 = All(
            Implies(
                And(Lt(Num(1), n0), Attained(s), Attained(t), Eq(EventIndex(s), n0), Eq(EventIndex(t), n0)),
                All(
                    Implies(Eq(Run(s, v), Run(t, w)), And(Eq(s, t), Eq(v, w))),
                    B("V", letters), B("W", letters))),
            B("n0", nat), B("s", source), B("t", source));
        var clause6 = All(
            Iff(Eq(Run(Of(false), w), Of(false)), Eq(w, Empty())),
            B("W", letters));
        var clause7 = All(
            Implies(
                Exists("W", letters, And(Ne(Id("W"), Empty()), Eq(Run(Of(false), Id("W")), z))),
                ExistsUnique("U", letters, u =>
                    And(
                        Eq(Recover(Num(2), z), Some(Pair(Id("K"), u))),
                        All(
                            Iff(
                                Eq(Run(Of(false), Id("W")), z),
                                Or(Eq(Id("W"), Cons(LetterF(), u)), Eq(Id("W"), Cons(LetterG(), u)))),
                            B("W", letters))))),
            B("z", source));
        var clause8 = All(
            Iff(
                Exists("D", Arrow(Id("A"), letters),
                    All(
                        Implies(Eq(Run(Of(false), w), Run(Id("K"), Id("U"))),
                            Eq(App("D", App("E", w)), w)),
                        B("W", letters))),
                Ne(App("E", Cons(LetterF(), Id("U"))), App("E", Cons(LetterG(), Id("U"))))),
            B("A", Id("Type")), B("E", Arrow(letters, Id("A"))), B("U", letters));
        var clause9 = All(
            Eq(
                App("replay", t, Id("es")),
                App("guardedRun", t, App("map", Id("es"), Id("toCall")))),
            B("t", source), B("es", eventList));
        var clause10 = All(
            Iff(Native(t), And(Attained(t), Ne(t, Of(true)))),
            B("t", source));
        var clause11 = All(
            Implies(
                Native(t),
                And(
                    Eq(App("guardedRun", t, Word(t, w)), Some(Run(t, w))),
                    Eq(Length(Word(t, w)), App("subtract", EventIndex(Run(t, w)), EventIndex(t))))),
            B("t", source), B("W", letters));
        var preservedValues = All(
            Implies(Mem(p, Material(t)), Eq(App("y", p), App("x", p))),
            B("p", address));
        var freshValues = All(
            Implies(Mem(p, Material(Run(t, w))),
                Implies(new Formula.Not(Mem(p, Material(t))), Eq(App("y", p), Num(0)))),
            B("p", address));
        var materialExecution = Eq(
            NativeRun(t, Id("labels"), Id("next"), Id("x"), Word(t, w)),
            Some(App("quad", Run(t, w), Id("labelsPrime"), Id("nextPrime"), Id("y"))));
        var materialAnswer = Exists("labelsPrime", Id("RawMap"),
            Exists("nextPrime", Id("Int"),
                Exists("y", Id("Value"), And(materialExecution, preservedValues, freshValues))));
        var clause12 = All(
            Implies(Native(t), All(materialAnswer,
                B("labels", Id("RawMap")), B("next", Id("Int")), B("x", Id("Value")))),
            B("t", source), B("W", letters));
        var clause13 = All(
            Exists("D", Arrow(Id("Bool"), letters),
                All(
                    Implies(Eq(Run(Of(false), w), Run(Id("K"), Id("U"))),
                        Eq(App("D", App("firstChoice", w)), w)),
                    B("W", letters))),
            B("U", letters));
        var clause14 = All(
            Le(App("recoverySteps", n0, z), App("subtract", EventIndex(z), n0)),
            B("n0", nat), B("z", source));

        return Disp(And(clause1, clause2, clause3, clause4, clause5, clause6, clause7,
            clause8, clause9, clause10, clause11, clause12, clause13, clause14));
    }
}
