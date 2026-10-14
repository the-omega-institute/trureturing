using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2SelectedCDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2SelectedC.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal F2 seams and the exact inventory of one supplied frame walk earn the selected-terminal condition for every actual c edge.",
        H("Selected Terminal Labels of the Same Actual c Edges"),
        Blocks(
            Item("native_f2_seam_selected_terminal", "Every Literal Seam Endpoint Has a Selected Terminal", RawFormula(),
                "For every m at least five, every literal F2 seam e, and every endpoint x of e, the terminal label x(m) is zero or m. For a T seam, its starting endpoint is the finish of its own indexed deleted a or b edge. The complete a-cut classification puts both terminal labels in {0,m}; the b-cut classification puts its terminal in the same set. An E seam similarly starts at the finish of its own indexed deleted b edge. The generator c fixes the terminal position, so the second endpoint keeps that label. This proves the condition directly from the independently defined seams."),
            Item("native_j2_frame_c_selected", "The Supplied Frame Walk Earns Its Selected c-Terminal Condition", FrameFormula(),
                "For every m at least five and every SupplyFrame(m,2), take any supplied closed walk w in the actual FrameDomain, with its exact undo-relabel inventory of native-minus-deleted edges together with F2 seams. Whenever x,y are actual frame vertices, y=x*c and their actual subtype edge occurs in w, the terminal label of x belongs to F.selected.toFinset. The c generator differs from both native generators a and b, so the retained native branch of this same inventory cannot supply that edge. The seam branch supplies the raw {0,m} terminal condition, and the same earned frame relabelling maps that set exactly to F.selected. The proof keeps this particular walk and earns its c-edge condition; no replacement cycle or separate target invariant is assumed."))));

    private static Formula RawFormula()
    {
        Formula m = F.Id("m"), e = F.Id("e"), x = F.Id("x");
        return Disp(All("m", Call("Nat"), Implies(Le(D(5), m),
            All("e", Call("Sym2", Call("Configuration", m)), Implies(Call("F2Seam", m, e),
                All("x", Call("Configuration", m), Implies(Member(x, e),
                    Member(Call("LastLabel", x), Call("PairSet", D(0), Call("Last", m))))))))));
    }

    private static Formula FrameFormula()
    {
        Formula m = F.Id("m"), frame = F.Id("frame"), w = F.Id("w"), e = F.Id("e");
        Formula x = F.Id("x"), y = F.Id("y");
        Formula down = Call("Sym2Map", Call("undoRelabel", frame), e);
        Formula inventory = All("e", Call("Sym2", Call("Configuration", m)),
            Iff(Member(e, Call("AmbientEdges", w)),
                Or(And(Call("F2NativeEdge", m, down), Not(Call("F2DeletedEdge", m, down))),
                    Call("F2Seam", m, down))));
        Formula conclusion = All("x", Call("FrameVertex", frame), All("y", Call("FrameVertex", frame),
            Implies(And(Eq(Call("Value", y), Call("Multiply", Call("Value", x), Call("c", m))),
                Member(Call("Sym2Pair", x, y), Call("Edges", w))),
                Member(Call("LastLabel", x), Call("ToFinset", Call("Selected", frame))))));
        return Disp(All("m", Call("Nat"), Implies(Le(D(5), m),
            All("frame", Call("SupplyFrame", m, D(2)),
                All("base", Call("FrameVertex", frame),
                    All("w", Call("FrameClosedWalk", frame, F.Id("base")),
                        Implies(inventory, conclusion)))))));
    }

    private static DocumentBlock Item(string name, string title, Formula formula, string meaning) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(meaning))), DescribeRole.Theorem);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula Member(Formula a, Formula b) => Call("Member", a, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
