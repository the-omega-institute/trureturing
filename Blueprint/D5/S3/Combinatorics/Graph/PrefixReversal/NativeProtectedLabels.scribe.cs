using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeProtectedLabelsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeProtectedLabels.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The final two selected labels form one fixed actual protected pair throughout native recursive frame growth and child-base rotation.",
        H("Fixed Protected Labels in Actual Recursive Frames"),
        Blocks(
            Item("protectedP", "The Penultimate Selected Label", DescribeRole.Definition,
                Frame(Eq(P("frame"), Call("ListGet", Selected("frame"), Call("NatSub", F.Id("k"), D(2))))),
                "For every complete SupplyFrame(m,k) with k at least two, protectedP is the actual selected label at index k minus two. The supplied length proof earns that this index exists."),
            Item("protectedQ", "The Final Selected Label", DescribeRole.Definition,
                Frame(Eq(Q("frame"), Call("ListGet", Selected("frame"), Call("NatSub", F.Id("k"), D(1))))),
                "The actual selected label at index k minus one is protectedQ. These labels are fixed by their list positions, without choosing another cycle or a separate relabelling."),
            Item("native_protected_labels", "The Protected Pair Is Distinct and Outside the Base", DescribeRole.Theorem,
                Frame(And(Ne(P("frame"), Q("frame")),
                    And(Member(P("frame"), Selected("frame")), And(Member(Q("frame"), Selected("frame")),
                    And(Not(Member(P("frame"), Call("Base", F.Id("frame")))),
                    And(Not(Member(Q("frame"), Call("Base", F.Id("frame")))),
                    And(Ne(P("frame"), Call("Terminal", F.Id("frame"))),
                        Ne(Q("frame"), Call("Terminal", F.Id("frame")))))))))),
                "Full tuple nodup proves that the last two selected positions have different actual labels. The same tuple separates selected labels from the independent base and terminal. This supplies one nondegenerate pair for the a-edge retention invariant in the same actual recursive cycle."),
            Item("native_protected_labels_prepend", "Prepending Preserves Both Labels", DescribeRole.Theorem,
                Frame(All("next", Call("SupplyFrame", F.Id("m"), Call("NatAdd", F.Id("k"), D(1))),
                    All("u", Call("Fin", Call("NatAdd", F.Id("m"), D(1))),
                    Implies(Eq(Selected("next"), Call("Cons", F.Id("u"), Selected("frame"))), SamePair())))),
                "For any actual next frame whose selected list is u cons the old selected list, both protected labels remain literally equal. The proof earns the shifted indices from k at least two. In particular, the native nextFrame constructor passes its defining selected-list equality."),
            Item("native_protected_labels_same_selected", "Child-Base Rotation Preserves Both Labels", DescribeRole.Theorem,
                Frame(All("next", Call("SupplyFrame", F.Id("m"), F.Id("k")),
                    Implies(Eq(Selected("next"), Selected("frame")), SamePair()))),
                "Any two complete frames with exactly the same selected list have the same protected labels. The nativeChildFrame operation rotates only the independent base, so it passes this premise by definition. This keeps the same pair across all ordinary children, without assuming that independently chosen cycle witnesses agree."))));

    private static DocumentBlock Item(string name, string title, DescribeRole role, Formula formula, string meaning) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(meaning))), role);
    private static Formula Frame(Formula body) => Disp(All("m", Call("Nat"), All("k", Call("Nat"),
        All("frame", Call("SupplyFrame", F.Id("m"), F.Id("k")),
            Implies(Call("AtLeast", F.Id("k"), D(2)), body)))));
    private static Formula SamePair() => And(Eq(P("next"), P("frame")), Eq(Q("next"), Q("frame")));
    private static Formula Selected(string name) => Call("Selected", F.Id(name));
    private static Formula P(string name) => Call("ProtectedP", F.Id(name));
    private static Formula Q(string name) => Call("ProtectedQ", F.Id(name));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => Not(Eq(a, b));
    private static Formula Not(Formula a) => Call("Not", a);
    private static Formula Member(Formula a, Formula b) => Call("Member", a, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
