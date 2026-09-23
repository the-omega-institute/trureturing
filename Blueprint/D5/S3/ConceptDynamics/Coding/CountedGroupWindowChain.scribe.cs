using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedGroupWindowChainDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/CountedGroupWindowChain.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Id(string name) => F.Id(name);
    private static Formula A => Id("A");
    private static Formula Target => Id("B");
    private static Formula Length => Id("L");
    private static Formula Chain => Id("ch");
    private static Formula Code => Call("chainWindowCode", Chain);
    private static Formula Forward(Formula x) => Call("apply", Call("homeomorph", Code), x);
    private static Formula Inverse(Formula x) => Call("apply", Call("symm", Call("homeomorph", Code)), x);
    private static Formula EdgeAt(Formula x, Formula i) => Call("edgeAt", Call("first", x), i);
    private static Formula Extension(Formula matrix) => Call("Prod", Call("Path", matrix), Id("H"));
    private static Formula Conj(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Impl(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Leq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Plus(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Minus(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula All(Formula body, params Formula.BoundVariable[] extra) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("H", Id("Type")), B("group", Call("Group", Id("H"))),
             B("finite", Call("Fintype", Id("H"))),
             B("topology", Call("TopologicalSpace", Id("H"))),
             B("continuousGroup", Call("IsTopologicalGroup", Id("H"))),
             B("a", Id("Nat")), B("b", Id("Nat")), B("L", Id("Nat")),
             B("A", Call("GroupMat", Id("H"), Id("a"), Id("a"))),
             B("B", Call("GroupMat", Id("H"), Id("b"), Id("b"))),
             B("ch", Call("ExchangeChain", Call("MonoidAlgebra", Id("Nat"), Id("H")), A, Target, Length)),
             .. extra], body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One finite matrix chain constructs one equivariant homeomorphism carrying both edge windows and both group-coordinate windows. The transfer is read from that same code.",
        H("Counted group chain recovery windows"),
        Blocks(
            Describe.Lean(DescribeId.Create("counted-group-chain-four-windows"),
                DeclarationHandle.Create(Prefix + "chain_has_window_group_conjugacy"),
                H("Construct one code with four recovery budgets"),
                StatementSource.FromAuthor(Disp(All(
                    Call("Nonempty", Call("WindowGroupConjugacy", A, Target, Length))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The elementary map is built from counted group-labelled edge fibers. Its forward edge uses the present and next input, its inverse uses the preceding and present output. The group transfers use the first split label and the preceding inverse split label. Composition adds all four budgets, and induction handles every intermediate matrix dimension."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("counted-group-chain-both-recoveries"),
                DeclarationHandle.Create(Prefix + "chain_two_sided_recovery"),
                H("Recover both directions with the same chosen code"),
                StatementSource.FromAuthor(Disp(RecoveryStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both equalities are the inverse laws of chainWindowCode. No different decoder is chosen for a different precision or for the opposite direction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("counted-group-chain-future-interval"),
                DeclarationHandle.Create(Prefix + "chain_future_interval"),
                H("Determine every edge of an output interval"),
                StatementSource.FromAuthor(Disp(IntervalStatement(false))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Agreement from lo through hi plus L implies forward agreement from lo through hi. The proof takes the union of the local future windows; the input group coordinates need not agree for this base-edge statement."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("counted-group-chain-past-interval"),
                DeclarationHandle.Create(Prefix + "chain_past_interval"),
                H("Recover every edge of an input interval"),
                StatementSource.FromAuthor(Disp(IntervalStatement(true))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Agreement from lo minus L through hi implies inverse agreement from lo through hi. This is the past window of the same homeomorphism, not an independently assumed inverse observation."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("counted-group-chain-transfer-cocycle"),
                DeclarationHandle.Create(Prefix + "constructed_transfer_cocycle"),
                H("Read a solution of the ordered transfer equation"),
                StatementSource.FromAuthor(Disp(TransferStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Evaluate the constructed code at group coordinate one. Equivariance gives its value at every group coordinate, and the original-time law gives the cocycle equation without permuting any group factors. coordinate_future supplies a finite window for this very transfer."))),
                DescribeRole.Theorem))));

    private static Formula RecoveryStatement() => All(Conj(
        new Formula.BindMany(FormulaQuantifier.ForAll, [B("x", Extension(A))],
            Equal(Inverse(Forward(Id("x"))), Id("x"))),
        new Formula.BindMany(FormulaQuantifier.ForAll, [B("y", Extension(Target))],
            Equal(Forward(Inverse(Id("y"))), Id("y")))));

    private static Formula IntervalStatement(bool inverse)
    {
        Formula Input = inverse ? Target : A;
        Formula Lo = Id("lo"), Hi = Id("hi"), I = Id("i");
        Formula Left = inverse ? Minus(Lo, Call("intCast", Length)) : Lo;
        Formula Right = inverse ? Hi : Plus(Hi, Call("intCast", Length));
        Formula Same = new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("i", Id("Int"))], Impl(Leq(Left, I), Impl(Leq(I, Right),
                Equal(EdgeAt(Id("x"), I), EdgeAt(Id("y"), I)))));
        Formula OutX = inverse ? Inverse(Id("x")) : Forward(Id("x"));
        Formula OutY = inverse ? Inverse(Id("y")) : Forward(Id("y"));
        Formula Conclusion = new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("i", Id("Int"))], Impl(Leq(Lo, I), Impl(Leq(I, Hi),
                Equal(EdgeAt(OutX, I), EdgeAt(OutY, I)))));
        return All(Impl(Same, Conclusion), B("x", Extension(Input)),
            B("y", Extension(Input)), B("lo", Id("Int")), B("hi", Id("Int")));
    }

    private static Formula TransferStatement() => new Formula.BindMany(FormulaQuantifier.ForAll,
        [B("H", Id("Type")), B("group", Call("Group", Id("H"))),
         B("finite", Call("Fintype", Id("H"))),
         B("topology", Call("TopologicalSpace", Id("H"))),
         B("continuousGroup", Call("IsTopologicalGroup", Id("H"))),
         B("a", Id("Nat")), B("b", Id("Nat")), B("r", Id("Nat")),
         B("A", Call("GroupMat", Id("H"), Id("a"), Id("a"))),
         B("B", Call("GroupMat", Id("H"), Id("b"), Id("b"))),
         B("f", Call("WindowGroupConjugacy", A, Target, Id("r"))),
         B("x", Call("Path", A))],
        Equal(Call("product", Call("label", Call("edgeAt", Id("x"), F.D(0))),
                Call("coordinateTransfer", Id("f"), Call("shift", A, Id("x")))),
            Call("product", Call("coordinateTransfer", Id("f"), Id("x")),
                Call("label", Call("edgeAt", Call("baseCode", Id("f"), Id("x")), F.D(0))))));
}
