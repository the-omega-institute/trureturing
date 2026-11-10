using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure;

internal sealed class TypedFiniteViewKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Typed partial labelled path views refine to full behavior at any plateau.",
        H("Typed finite path views and stable refinement"),
        Blocks(
            Paragraph(Text(
                "The types, their state and readout spaces, the named edges between types, "
                    + "and each edge's label space are arbitrary. Each edge responds partially "
                    + "with a label and a state of its target type. An absent response is "
                    + "illegality, not an extra state. No finiteness, decidable equality, "
                    + "or totality assumption is imposed.")),
            Paragraph(Text(
                "A path is a composable word of named edges in execution order. Its response "
                    + "is absent if any edge is illegal; otherwise it contains the complete "
                    + "ordered tuple of edge labels and the terminal typed readout. The "
                    + "finite view records responses to every path up to its depth, including "
                    + "every prefix and the empty path. The complete behavior records all "
                    + "finite paths. Both retain the starting type as a separate tag.")),
            Paragraph(Text(
                "The refinement relation is defined independently: depth zero requires "
                    + "equal type tags and roots; the next depth additionally requires "
                    + "simultaneous legality for every named outgoing edge and, when legal, "
                    + "equal labels and successors related at the preceding depth.")),
            Paragraph(Text(
                "For a complete response contract, an alternative trace retains the readout at "
                    + "every cut. Its empty trace is the current readout. At a nonempty word it "
                    + "pairs that readout with an absent tag if the first operation is illegal, "
                    + "or with the actual first record and the recursively obtained suffix "
                    + "trace when the operation is legal. Thus an illegal suffix keeps the "
                    + "earlier readouts and records and stops at the first missing transition. "
                    + "A continuing failure remains a legal transition with its failure and "
                    + "reason in the record. Terminal outcomes are represented by declared "
                    + "terminal types on which all operations are absent. Operation parameters "
                    + "remain part of the named edge. Readouts and records retain every source, "
                    + "permission, archive and calibration field required by the fixed "
                    + "contract. Omitting a field in a later projection does not erase a "
                    + "record already retained by that contract.")),
            Paragraph(Text(
                "Equality of these complete traces for all finite words is exactly equality "
                    + "of complete behavior here. In one direction, erase the earlier cut "
                    + "readouts from each trace to obtain the successful label tuple and "
                    + "terminal readout, or absence. In the other direction, use the finite "
                    + "refinement relation at the word's length: its root equality gives the "
                    + "first cut, its one-step clause gives simultaneous legality and the "
                    + "same record, and its successor clause gives the remaining trace. The "
                    + "outer type tag is retained in both presentations. No bound on state "
                    + "fibers, word length or branching is needed.")),
            Paragraph(Text(
                "Take the quotient separately in each actual state fiber by this complete "
                    + "response equality, and then take the disjoint typed union. A partial "
                    + "named operation descends by mapping a legal successor to its quotient "
                    + "class and retaining its actual record. The refinement clause proves "
                    + "that this partial map is independent of the representative, including "
                    + "whether it is absent. A graph arrow consists of a legal name at the "
                    + "source residual and its determined target residual. Different names "
                    + "remain different arrows, even when their endpoints coincide.")),
            Paragraph(Text(
                "Every such arrow lifts from every actual representative of its source "
                    + "residual, with the same record and the stipulated successor class. "
                    + "Induction on a composable graph word therefore lifts the whole word "
                    + "from one fixed initial representative, keeping an actual intermediate "
                    + "state at every prefix. The state images are the original fibers; "
                    + "the trace tuples are outputs of these states, with no assumption "
                    + "that independently possible record fields can be jointly realized. "
                    + "Empty fibers are allowed, and the chosen initial state supplies the "
                    + "inhabited starting fiber.")),
            Paragraph(Text(
                "This response correspondence supplies a representative-independent legal "
                    + "graph. It places no finiteness or recurrence condition on that graph "
                    + "and gives no cycle criterion for reconstructing the chronological "
                    + "word from a final residual and an additive duration. Duration must "
                    + "itself descend, either because it is a declared record field or "
                    + "by a separate hypothesis with one common unit and calibration.")),
            Describe.Lean(
                DescribeId.Create("typed-finite-view-kernel"),
                DeclarationHandle.Create(Prefix + "typed_finite_view_kernel"),
                H("Finite views, intersection, and permanent stability"),
                StatementSource.FromAuthor(KernelStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the full disjoint union of states, refinement at any depth is "
                            + "exactly equality of the corresponding finite views. Each next "
                            + "relation is contained in the previous one, and equality of "
                            + "complete behavior is their intersection.")),
                    Paragraph(Text(
                        "If two consecutive refinement relations coincide at one depth, "
                            + "that relation already equals the complete behavior kernel. "
                            + "Every later relation equals it as well. This is a conditional "
                            + "stability certificate and does not assert that a plateau exists.")),
                    Paragraph(Text(
                        "Induction on depth splits nonempty paths at their first edge. "
                            + "One-edge responses recover legality and the first label; "
                            + "removing that label from longer responses recovers every "
                            + "successor path response. Restricting lengths gives descent, "
                            + "and each finite path belongs to its own length bound. Equality "
                            + "of consecutive relations propagates through the recurrence, "
                            + "so the path characterization identifies the plateau with "
                            + "complete behavior."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula All(Formula names, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, names, Colon, Sp, type, Comma, Sp, body, Close);

    private static Formula ProductOver(Formula names, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, names, Colon, Sp, type, Comma, Sp, body, Close);

    private static Formula Applied(string name, params Formula[] arguments) =>
        Call(name, [F.Id("Label"), F.Id("q"), F.Id("step"), .. arguments]);

    private static Formula KernelStatement()
    {
        Formula i = F.Id("i"), j = F.Id("j"), e = F.Id("e");
        Formula n = F.Id("n"), k = F.Id("k"), s = F.Id("s"), t = F.Id("t");
        Formula index = F.Id("I"), type = F.Id("Type");
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula indices = Seq(i, Comma, Sp, j);
        Formula states = Seq(Sigma, Sp, i, Colon, Sp, index, Comma, Sp, Call("S", i));
        Formula pair = Seq(s, Comma, Sp, t);
        Formula next = Seq(Open, n, Plus, D(1), Close);
        Formula later = Seq(Open, n, Plus, k, Close);
        Formula relation = Applied("E", n);
        Formula kernel = Applied("behaviorKernel");

        Formula views = All(n, natural, All(pair, states,
            Seq(Applied("E", n, s, t), Sp, Leftrightarrow, Sp,
                Applied("finiteView", n, s), Eq, Applied("finiteView", n, t))));
        Formula descent = All(n, natural, All(pair, states,
            Seq(Applied("E", next, s, t), Sp, Rightarrow, Sp, Applied("E", n, s, t))));
        Formula intersection = Seq(Open, kernel, Eq,
            Open, LambdaLower, Sp, pair, Colon, Sp, states, Sp, Mapsto, Sp,
                All(n, natural, Applied("E", n, s, t)), Close, Close);
        Formula plateau = All(n, natural,
            Seq(Open, relation, Eq, Applied("E", next), Close, Sp, Rightarrow, Sp,
                Open, relation, Eq, kernel, Sp, Land, Sp,
                    All(k, natural, Seq(Applied("E", later), Eq, relation)), Close));
        Formula result = Seq(views, Sp, Land, RowBreak, Grp(),
            descent, Sp, Land, RowBreak, Grp(),
            intersection, Sp, Land, RowBreak, Grp(), plateau);

        Formula edgeType = Arrow(index, Arrow(index, type));
        Formula family = Arrow(index, type);
        Formula labelType = ProductOver(indices, index, Arrow(Call("Edge", i, j), type));
        Formula readoutType = ProductOver(i, index, Arrow(Call("S", i), Call("O", i)));
        Formula responseType = ProductOver(indices, index,
            ProductOver(e, Call("Edge", i, j),
                Arrow(Call("S", i), Call("Option",
                    Seq(Open, Call("Label", e), Sp, Times, Sp, Call("S", j), Close)))));

        return Disp(All(index, type,
            All(F.Id("Edge"), edgeType,
                All(F.Id("Label"), labelType,
                    All(Seq(F.Id("S"), Comma, Sp, F.Id("O")), family,
                        All(F.Id("q"), readoutType,
                            All(F.Id("step"), responseType, result)))))));
    }
}
