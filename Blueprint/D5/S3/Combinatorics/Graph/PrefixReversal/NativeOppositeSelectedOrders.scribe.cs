using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeOppositeSelectedOrdersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeOppositeSelectedOrders.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two recursive marked orders are tied by one canonical exchange of the last two selected labels. Their earlier selected positions, base, terminal and child-base rotation retain exact literal identities.",
        H("Canonical Opposite Selected Orders"),
        Blocks(
            Item("oppositeSelectedFrame", "Exchange Only the Protected Pair", DescribeRole.Definition,
                Frame(Eq(Call("Selected", Bar("frame")),
                    Call("Map", Call("Swap", P(F.Id("frame")), Q(F.Id("frame"))), Call("Selected", F.Id("frame"))))),
                "The complete SupplyFrame is rebuilt with the selected list mapped through the transposition of protectedP and protectedQ. Both labels occur in the original selected list, so the map is a permutation of that list. The independent base and terminal are literally unchanged. This fixes an ordering, rather than merely requiring equality of selected-label sets."),
            Item("native_opposite_protected_labels", "The Protected Labels Exchange Positions", DescribeRole.Theorem,
                Frame(And(Eq(P(Bar("frame")), Q(F.Id("frame"))), Eq(Q(Bar("frame")), P(F.Id("frame"))))),
                "The actual labels at indices k minus two and k minus one exchange. No independently chosen opposite frame, cycle or relabelling is assumed."),
            Item("native_opposite_selected_prefix", "The Earlier Selected Prefix Is Unchanged", DescribeRole.Theorem,
                Frame(Eq(Call("Take", Call("NatSub", F.Id("k"), D(2)), Call("Selected", Bar("frame"))),
                    Call("Take", Call("NatSub", F.Id("k"), D(2)), Call("Selected", F.Id("frame"))))),
                "Nodup of the complete literal tuple separates each earlier selected position from both protected labels. The transposition therefore fixes every one of those positions. Along with the exchanged final pair, this determines the exact opposite selected order."),
            Item("native_opposite_selected_involutive", "The Canonical Exchange Is an Involution", DescribeRole.Theorem,
                Frame(Eq(Call("OppositeSelectedFrame", Bar("frame")), F.Id("frame"))),
                "After one exchange the protected labels themselves are reversed. The second exchange uses the same unordered transposition, restoring the entire complete frame, including its unchanged base and terminal."),
            Item("native_opposite_selected_two", "The Exceptional J2 Order Uses the Same Exchange", DescribeRole.Theorem,
                Disp(All("m", Call("Nat"), All("frame", Call("SupplyFrame", F.Id("m"), D(2)),
                    Eq(Bar("frame"), Call("ReverseSelected", F.Id("frame")))))),
                "At order two the protected pair is the entire selected list. The canonical exchange is exactly the existing reverseSelected frame used by the actual J2 seed, with the same base, terminal and port indices. This bridges the exceptional seed to the precise ordering required by later simultaneous states."),
            Item("native_opposite_next_frame", "Prepending Commutes with the Exchange", DescribeRole.Theorem,
                ConstructorFrame(Eq(Call("OppositeSelectedFrame", Call("NextFrame", F.Id("frame"), F.Id("A"), F.Id("u"))),
                    Call("NextFrame", Bar("frame"), F.Id("A"), F.Id("u")))),
                "For an original base A append singleton u, nextFrame prepends u to the selected list. Full tuple nodup proves u differs from both protected labels; the protected-label prepend theorem keeps their literal identities. Hence constructing the next frame and taking its opposite commutes exactly. This gives compatible simultaneous induction instances rather than assuming agreement of separately chosen orders."),
            Item("native_opposite_outer_frame", "The Outer Supplier Commutes with the Exchange", DescribeRole.Theorem,
                ConstructorFrame(Eq(Call("OppositeSelectedFrame", Call("OuterFrame", F.Id("frame"), F.Id("A"), F.Id("u"))),
                    Call("OuterFrame", Bar("frame"), F.Id("A"), F.Id("u")))),
                "The actual outer supplier replaces the base by A append the old terminal and replaces the terminal by u. Its selected list keeps the old order. The canonical opposite operation therefore commutes with this same literal supplier constructor."),
            Item("native_opposite_child_frame", "Every Child-Base Rotation Commutes with the Exchange", DescribeRole.Theorem,
                Frame(All("j", Call("Fin", Call("Length", Call("Base", F.Id("frame")))),
                    Eq(Call("OppositeSelectedFrame", Call("NativeChildFrame", F.Id("frame"), F.Id("j"))),
                        Call("NativeChildFrame", Bar("frame"), F.Id("j"))))),
                "For each independent child index, nativeChildFrame rotates the base by exactly that index and retains the selected list and terminal. Both marked orders therefore use the same literal child-base rotation. These order identities supply missing frame compatibility; they do not assert a completed all-order Hamiltonian induction."))));

    private static DocumentBlock Item(string name, string title, DescribeRole role, Formula formula, string meaning) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(meaning))), role);
    private static Formula Frame(Formula body) => Disp(All("m", Call("Nat"), All("k", Call("Nat"),
        All("frame", Call("SupplyFrame", F.Id("m"), F.Id("k")),
            Implies(Call("AtLeast", F.Id("k"), D(2)), body)))));
    private static Formula ConstructorFrame(Formula body) => Frame(
        All("A", Call("List", Call("Fin", Call("NatAdd", F.Id("m"), D(1)))),
        All("u", Call("Fin", Call("NatAdd", F.Id("m"), D(1))),
            Implies(Eq(Call("Base", F.Id("frame")), Call("Append", F.Id("A"), Call("Singleton", F.Id("u")))), body))));
    private static Formula Bar(string name) => Call("OppositeSelectedFrame", F.Id(name));
    private static Formula P(Formula frame) => Call("ProtectedP", frame);
    private static Formula Q(Formula frame) => Call("ProtectedQ", frame);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
