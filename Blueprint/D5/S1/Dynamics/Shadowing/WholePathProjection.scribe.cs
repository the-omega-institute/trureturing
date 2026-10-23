using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class WholePathProjectionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/WholePathProjection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A given finite hidden graph retains every whole visible path exactly when all prefixes lift; a live finite target has a bounded failure certificate.",
        H("Whole Path Projection and Finite Prefix Diagnostics"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hidden-prefix-lift"),
                DeclarationHandle.Create(Owner + "PrefixLift"),
                H("A prefix includes its initial vertex"),
                StatementSource.FromAuthor(PrefixFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For hidden vertices H, visible vertices P, hidden edges EH and labels q:H→P, "
                    + "PrefixLift(EH,q,a,m) requires a hidden path on Fin(m+1) matching a at every "
                    + "time from zero through m. The m indices of Fin m specify its consecutive "
                    + "edges. Thus m counts edges, not vertices. At m=0 the condition is precisely "
                    + "a hidden preimage of a(0); it cannot be discarded as an empty-prefix check."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("whole-path-onto-prefix-criterion"),
                DeclarationHandle.Create(Owner + "graphLanguage_eq_iff_prefix_lifts"),
                H("All prefixes of the same whole path suffice"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume H is finite and q preserves directed edges from EH to EP. The "
                        + "hidden graph's complete label language equals graphLanguage(EP,id) if "
                        + "and only if every finite prefix of every complete visible path lifts. "
                        + "The entire old target is retained, with all starting vertices allowed. "
                        + "There is no finiteness or live-vertex assumption on P for this criterion.")),
                    Paragraph(Text(
                        "For one fixed whole visible path a, the finite types of its hidden lifts "
                        + "through each time m form an inverse system under literal truncation. "
                        + "Mathlib's nonempty_sections_of_finite_inverse_system supplies a compatible "
                        + "section when each prefix lifts. Read its time-m terminal coordinate to "
                        + "obtain a single entire hidden path. No truncation map is assumed onto, "
                        + "and individual finite lifts need not have continuations. Restriction "
                        + "of a whole lift proves the other implication; edge preservation pays "
                        + "the automatic hidden-to-visible language inclusion.")),
                    Paragraph(Text(
                        "The reusable contribution is the graph-specific finite-prefix functor, "
                        + "its truncation laws and reconstruction of a whole graph path, composed "
                        + "with the existing inverse-system compactness theorem. Neither a new "
                        + "compactness proof nor a surjectivity theorem for the bonding maps is claimed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bounded-whole-projection-failure"),
                DeclarationHandle.Create(Owner + "exists_bounded_prefix_without_lift"),
                H("A bounded certificate for one candidate graph"),
                StatementSource.FromAuthor(BoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Now assume both vertex types are finite with N=card P and M=card H, "
                        + "q preserves edges, and each visible vertex starts some whole visible "
                        + "path. If the whole projection is not onto, there is a whole visible "
                        + "path a and a time m≤N·2^M whose prefix through m has no hidden lift. "
                        + "This is at most N·2^M+1 visible vertices. Hidden seriality is unnecessary.")),
                    Paragraph(Text(
                        "The initial hidden subset is q⁻¹{a(0)}. Reading the tail labels uses "
                        + "Mathlib's NFA stepSet and subset-construction DFA. Hidden endpoints are "
                        + "identified with actual finite prefix lifts. The diagnostic DFA stores "
                        + "Option(P×Set H): a visible vertex and hidden subset, plus an absorbing "
                        + "invalid-visible-edge sink. Acceptance means a nonsink empty hidden subset. "
                        + "A shortest accepted tail has length less than this DFA's state cardinal "
                        + "by Mathlib's evalFrom_split: remove its supplied nonempty loop to contradict "
                        + "minimality. The upstream set, product and option cardinalities give "
                        + "N·2^M+1 states and hence a tail of at most N·2^M labels. The visible live "
                        + "hypothesis extends the valid shortened tail to a whole target path.")),
                    Paragraph(Text(
                        "The empty visible type makes the entire target empty, so onto is vacuous. "
                        + "If the hidden type is empty and the target is nonempty, failure already "
                        + "occurs at m=0. Live trimming of the target may supply the stated assumption "
                        + "while preserving every original whole path; no trimming theorem or "
                        + "executable graph enumeration is asserted in this module.")),
                    Paragraph(Text(
                        "The Reg variation uses a visible two-vertex full graph and a hidden "
                        + "four-vertex graph with states (x,k), label x, and edges (x,k)→(k,k). "
                        + "Every visible vertex and edge has a preimage, and all hidden vertices "
                        + "are live. Yet each hidden visible history is constant after time one: "
                        + "the visible prefix 0,1,0 cannot lift. This checks that vertex or edge "
                        + "onto was not substituted for whole-path onto and that checking only "
                        + "time zero is insufficient.")),
                    Paragraph(Text(
                        "The suppliers are pinned Mathlib CofilteredSystem, NFA and DFA; their "
                        + "compactness, subset construction and pigeonhole loop removal are reused. "
                        + "This formalizes the finite diagnostic in the Peng visible/hidden research "
                        + "continuation. It checks a supplied candidate graph. It does not prove existence "
                        + "of a successful candidate, a finite horizon for actual source realizability, "
                        + "convergence of core/control/net choices, or a solution of Peng Questions "
                        + "5.1 or 5.2. No originality or open-problem resolution is claimed."))),
                DescribeRole.Theorem))));

    private static Formula PrefixFormula() => Disp(Seq(
        Call("PrefixLift", F.Id("EH"), F.Id("q"), F.Id("a"), F.Id("m")), Sp,
        Leftrightarrow, Sp, Exists, Sp, F.Id("b"), Colon, Sp,
        Call("Fin", Seq(F.Id("m"), Plus, D(1))), Sp, Rightarrow, Sp, F.Id("H"), Comma, Sp,
        Open, Forall, Sp, F.Id("i"), Colon, Sp, Call("Fin", F.Id("m")), Comma, Sp,
        Call("EH", Call("b", Call("castSucc", F.Id("i"))),
            Call("b", Call("succ", F.Id("i")))), Close, Sp, Land, Sp,
        Forall, Sp, F.Id("i"), Colon, Sp, Call("Fin", Seq(F.Id("m"), Plus, D(1))), Comma, Sp,
        Call("q", Call("b", F.Id("i"))), Eq, Call("a", Call("val", F.Id("i")))));

    private static Formula CriterionFormula() => Disp(Seq(
        Call("Finite", F.Id("H")), Sp, Land, Sp,
        Call("EdgePreserving", F.Id("q"), F.Id("EH"), F.Id("EP")), Sp, Rightarrow, Sp,
        Open, Call("graphLanguage", F.Id("EH"), F.Id("q")), Sp, Eq, Sp,
        Call("graphLanguage", F.Id("EP"), F.Id("id")), Sp, Leftrightarrow, Sp,
        Forall, Sp, F.Id("a"), InMacro, Call("graphLanguage", F.Id("EP"), F.Id("id")), Comma, Sp,
        Forall, Sp, F.Id("m"), InMacro, Nat(), Comma, Sp,
        Call("PrefixLift", F.Id("EH"), F.Id("q"), F.Id("a"), F.Id("m")), Close));

    private static Formula BoundFormula() => Disp(Seq(
        Call("FiniteLiveTarget", F.Id("P"), F.Id("EP")), Sp, Land, Sp,
        Call("Finite", F.Id("H")), Sp, Land, Sp,
        Call("EdgePreserving", F.Id("q"), F.Id("EH"), F.Id("EP")), Sp, Land, Sp,
        Call("graphLanguage", F.Id("EH"), F.Id("q")), Sp, Neq, Sp,
        Call("graphLanguage", F.Id("EP"), F.Id("id")), Sp, Rightarrow, Sp,
        Exists, Sp, F.Id("a"), InMacro, Call("graphLanguage", F.Id("EP"), F.Id("id")), Comma, Sp,
        Exists, Sp, F.Id("m"), Le, Sp, Seq(F.Id("N"), Cdot, Seq(D(2), Caret, Grp(F.Id("M")))), Comma, Sp,
        Neg, Call("PrefixLift", F.Id("EH"), F.Id("q"), F.Id("a"), F.Id("m"))));

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Seq(Operatorname, Grp(F.Id(name))), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
