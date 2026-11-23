using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class LabelledExtensionRecoveryDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Left, Open, body, Right, Close);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(variable, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Imp(Formula premise, Formula conclusion) =>
        Seq(Par(premise), Sp, Implies, Sp, Par(conclusion));
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complete label history identifies its event order exactly when every label fiber " +
        "is a chain, for finite induced supports and for complete histories of countably " +
        "infinite past-finite partial orders.",
        H("Recovering Event Order from Labels"),
        Blocks(
            Paragraph(Text(
                "Let E be any partially ordered type, A any alphabet, F any finite subset of E, " +
                "and label a function from E to A. The two types have independent universes and " +
                "may be empty or infinite. A complete extension has no repeated event, contains " +
                "exactly F, and never places a predecessor after its successor. The order is " +
                "the order induced on F. An arbitrary F need not be a lower set of E, so these " +
                "lists do not assert global execution in the ambient event system. " +
                "ExtensionList is the original EnabledPathSwapConnectivity predicate, with F " +
                "viewed as its underlying set in the displayed formula.")),
            Describe.Lean(
                DescribeId.Create("labelled-extension-recovery"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/PartialIdentification/LabelledExtensionRecovery.result"),
                H("Exact classification of label recovery"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every two equal-labelled events in F are comparable if and only if any " +
                        "two complete extensions with the same label list are equal as event lists. " +
                        "Repeated labels are allowed, and neither a finite alphabet nor a finite " +
                        "ambient event type is assumed. The empty support is included.")),
                    Paragraph(Text(
                        "For reconstruction, compare the first events of two extensions. Their " +
                        "labels agree. If they were distinct, each would occur in the other tail. " +
                        "The two extension conditions would then forbid both comparison directions, " +
                        "contradicting the chain condition on that label fiber. The heads agree, " +
                        "and recursion recovers the remaining events.")),
                    Paragraph(Text(
                        "For the obstruction, take incomparable events with the same label. In the " +
                        "finite subtype of F, the union of their strict predecessor sets is a lower " +
                        "cut containing neither event. The existing finite-poset extension theorem " +
                        "supplies a prefix ending at this cut and a suffix after both events. " +
                        "Concatenating extension lists gives both adjacent orders with a shared " +
                        "prefix and suffix. They have the same label word and distinct event orders. " +
                        "The proof transports exact support, no repetitions, and the pairwise order " +
                        "condition between subtype lists and ambient lists.")),
                    Paragraph(Text(
                        "This is a repository-derived classification with classical nice-labelling " +
                        "context. Nice labels in finite conflict-free " +
                        "event structures separate incomparable events, equivalently giving chain " +
                        "fibers. See Santocanale, https://arxiv.org/html/0903.3462v1, Definition 2.3, Lemma 2.11, " +
                        "and Proposition 2.12. The present statement concerns complete extensions " +
                        "of arbitrary finite induced subsets and an arbitrary alphabet."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For the infinite statement, E is a countably infinite partially ordered type, " +
                "and every strict past Iio x is finite. The alphabet A lies in an independent " +
                "universe and is arbitrary. A History E is a bijection e from the natural numbers " +
                "onto E satisfying, for every i < j, not (e j <= e i). Thus every event occurs " +
                "exactly once, and each predecessor occurs before its successor. No total order " +
                "on E or history is supplied as an additional premise.")),
            Describe.Lean(
                DescribeId.Create("infinite-labelled-extension-recovery"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/PartialIdentification/LabelledExtensionRecovery.infinite_result"),
                H("Complete natural histories and exact label recovery"),
                StatementSource.FromAuthor(InfiniteResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There exists a complete natural history. On all such histories, the " +
                        "complete infinite label word determines the history exactly when all " +
                        "equal-label events are comparable. Countability and finite strict pasts " +
                        "apply to the original partial order; the statement imposes no bound on " +
                        "its width or on the alphabet.")),
                    Paragraph(Text(
                        "For existence, choose an injective natural-number code c for E. The " +
                        "closed past of x is finite, so define its rank r(x) as the sum of " +
                        "c(y)+1 over y <= x. This rank bounds c(x) and increases strictly when " +
                        "x < y. Pair r(x) with c(x) using Nat.pair. Pairing is injective, and " +
                        "the square bounds for Nat.pair show that this key increases along " +
                        "strict comparisons: the key for x is less than (r(x)+1)^2, while the " +
                        "key for y is at least r(y)^2. Its range is an infinite subset of the " +
                        "natural numbers. Mathlib's Nat.Subtype.orderIsoOfNat enumerates this " +
                        "range in increasing order, and Equiv.ofInjective transports that " +
                        "enumeration back to E. The resulting bijection is compatible with " +
                        "the original partial order.")),
                    Paragraph(Text(
                        "For recovery, use strong induction on the index. Suppose two histories " +
                        "agree before n and have the same label at n. If their current events " +
                        "differ, surjectivity places each event somewhere in the other history. " +
                        "Injectivity and equality at all earlier indices force both positions " +
                        "to be strictly after n. The two history conditions then forbid both " +
                        "order comparisons between those events, contradicting the chain-fiber " +
                        "hypothesis. This argument uses complete histories and does not assume " +
                        "that arbitrary prefixes of equal length have the same support.")),
                    Paragraph(Text(
                        "For necessity, let a and b be incomparable events with the same label. " +
                        "The union of their closed pasts is a finite lower support F. The " +
                        "existing private incomparable_collision construction on the subtype F " +
                        "gives complete finite extensions with a shared prefix and suffix and " +
                        "with a,b in the two adjacent orders. The complement of F remains " +
                        "countably infinite and past-finite. Choose one complete history of " +
                        "that complement. The history_append construction joins each finite " +
                        "extension to this same actual continuation, proving bijectivity and " +
                        "order compatibility across the join. The two resulting complete " +
                        "histories differ at the swap position and have identical infinite " +
                        "label words.")),
                    Paragraph(Text(
                        "Brightwell and Luczak, Order-invariant measures on fixed causal sets, " +
                        "https://arxiv.org/abs/0901.0242v2, abstract and Introduction, identify " +
                        "countably infinite past-finite posets precisely with posets admitting " +
                        "natural extensions. Their natural extension is the History object " +
                        "used here. The Lean construction combines countability, finite sums, " +
                        "natural-number pairing and Mathlib's exact infinite-subset enumeration " +
                        "API with the finite extension and collision machinery in this owner."))),
                DescribeRole.Theorem))));

    private static Formula InfiniteResultFormula()
    {
        var e = V("E");
        var alphabet = V("A");
        var label = V("label");
        var a = V("a");
        var b = V("b");
        var x = V("x");
        var history = Call("History", e);
        var natural = Seq(Mathbb, Grp(V("N")));
        var chains = All(a, e, All(b, e,
            Imp(Equal(new Formula.Apply(label, [a]), new Formula.Apply(label, [b])),
                Seq(Par(Seq(a, Sp, Le, Sp, b)), Sp, Lor, Sp,
                    Par(Seq(b, Sp, Le, Sp, a))))));
        var word = Seq(LambdaLower, Sp, Par(Seq(V("h"), Colon, Sp, history)), Sp, Mapsto, Sp,
            LambdaLower, Sp, Par(Seq(V("n"), Colon, Sp, natural)), Sp, Mapsto, Sp,
            new Formula.Apply(label, [new Formula.Apply(V("h"), [V("n")])]));
        var classification = Seq(Par(chains), Sp, Iff, Sp, Call("Injective", Par(word)));
        var conclusion = Seq(Call("Nonempty", history), Sp, Land, Sp, Par(classification));
        var past = All(x, e, Call("Finite", Call("Iio", x)));
        return All(e, Seq(V("Type"), Underscore, Grp(V("u"))),
            All(alphabet, Seq(V("Type"), Underscore, Grp(V("v"))),
            Seq(OpenBracket, Call("PartialOrder", e), CloseBracket, Sp,
                OpenBracket, Call("Countable", e), CloseBracket, Sp,
                OpenBracket, Call("Infinite", e), CloseBracket, Sp,
                Imp(past, All(label, Seq(e, Sp, To, Sp, alphabet), conclusion)))));
    }

    private static Formula ResultFormula()
    {
        var e = V("E");
        var alphabet = V("A");
        var support = V("F");
        var label = V("label");
        var a = V("a");
        var b = V("b");
        var l = V("l");
        var m = V("m");
        var sameLabel = Equal(new Formula.Apply(label, [a]), new Formula.Apply(label, [b]));
        var comparable = Seq(Par(Seq(a, Sp, Le, Sp, b)), Sp, Lor, Sp,
            Par(Seq(b, Sp, Le, Sp, a)));
        var chains = All(a, e, Imp(Seq(a, Sp, InMacro, Sp, support),
            All(b, e, Imp(Seq(b, Sp, InMacro, Sp, support), Imp(sameLabel, comparable)))));
        var recovery = All(l, Call("List", e), All(m, Call("List", e),
            Imp(Call("ExtensionList", Emptyset, support, l),
                Imp(Call("ExtensionList", Emptyset, support, m),
                    Imp(Equal(Call("map", label, l), Call("map", label, m)), Equal(l, m))))));
        var classification = Seq(Par(chains), Sp, Iff, Sp, Par(recovery));
        return All(e, V("Type"), All(alphabet, V("Type"),
            Seq(OpenBracket, Call("PartialOrder", e), CloseBracket, Sp,
                All(support, Call("Finset", e),
                    All(label, Seq(e, Sp, To, Sp, alphabet), classification)))));
    }
}
