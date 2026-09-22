using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class BipartiteOverlapConjugacyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/BipartiteOverlapConjugacy.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula A(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Read(Formula path, Formula index) => A(Call("value", path), index);
    private static Formula All(Formula body, params Formula.BoundVariable[] extra) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("U", F.Id("Type")), B("V", F.Id("Type")), B("I", F.Id("Type")),
             B("J", F.Id("Type")), B("d", Call("Boundary", F.Id("U"), F.Id("V"),
                 F.Id("I"), F.Id("J"))), .. extra], body);
    private static Formula L => Call("LeftPath", F.Id("d"));
    private static Formula R => Call("RightPath", F.Id("d"));
    private static Formula X => F.Id("x");
    private static Formula Y => F.Id("y");
    private static Formula D => F.Id("d");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rebracketing a legal alternating path preserves every half-edge and gives an invertible code.",
        H("Bipartite overlap conjugacy"),
        Blocks(
            Describe.Lean(DescribeId.Create("overlap-left-recovery"),
                DeclarationHandle.Create(Prefix + "backward_forward"), H("Recover the input path"),
                StatementSource.FromAuthor(Disp(All(
                    Equal(Call("backward", D, Call("forward", D, X)), X), B("x", L)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The previous output contains the first half-edge of the current input. The current output contains its second half-edge. Their combination recovers the complete legal input path."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("overlap-right-recovery"),
                DeclarationHandle.Create(Prefix + "forward_backward"), H("Recover the output path"),
                StatementSource.FromAuthor(Disp(All(
                    Equal(Call("forward", D, Call("backward", D, Y)), Y), B("y", R)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Decoding followed by recoding recovers both half-edges at each integer position. The endpoint equations ensure that the decoded sequence is a legal path."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("overlap-one-step-intertwining"),
                DeclarationHandle.Create(Prefix + "forward_shift"), H("Preserve one time step"),
                StatementSource.FromAuthor(Disp(All(Equal(
                    Call("forward", D, Call("leftShift", D, X)),
                    Call("rightShift", D, Call("forward", D, X))), B("x", L)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The recoding uses the same adjacent-coordinate formula at every integer position. Applying one shift before recoding or after recoding gives the same path."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("overlap-finite-forward-window"),
                DeclarationHandle.Create(Prefix + "forward_window"), H("A two-edge forward window"),
                StatementSource.FromAuthor(Disp(Window())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equality at positions i and i+1 forces equality of the recoded edge at i. No information outside this window is used."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("overlap-cannot-read-only-present"),
                DeclarationHandle.Create(Prefix + "no_present_only_recoder"), H("The present edge alone is insufficient"),
                StatementSource.FromAuthor(Disp(NoPresent())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In the one-vertex example with a binary first half-edge, two histories agree at zero and differ at one. Recoding distinguishes them at zero, so no function of the present input edge alone implements this code."))),
                DescribeRole.Theorem))));

    private static Formula Window()
    {
        Formula i = F.Id("i");
        Formula next = new Formula.Binary(i, FormulaBinaryOperator.Add, F.D(1));
        return All(new Formula.Logic(Equal(Read(X, i), Read(Y, i)), FormulaLogicOperator.Implies,
            new Formula.Logic(Equal(Read(X, next), Read(Y, next)), FormulaLogicOperator.Implies,
                Equal(Read(Call("forward", D, X), i), Read(Call("forward", D, Y), i)))),
            B("x", L), B("y", L), B("i", F.Id("Int")));
    }

    private static Formula NoPresent()
    {
        Formula input = Call("Prod", F.Id("Bool"), F.Id("Unit"));
        Formula output = Call("Prod", F.Id("Unit"), F.Id("Bool"));
        Formula boundary = F.Id("binaryBoundary");
        Formula body = new Formula.BindMany(FormulaQuantifier.ForAll,
            [B("x", Call("LeftPath", boundary))],
            Equal(A(F.Id("f"), Read(X, F.D(0))),
                Read(Call("forward", boundary, X), F.D(0))));
        return new Formula.Not(new Formula.BindMany(FormulaQuantifier.Exists,
            [B("f", new Formula.TypeArrow(input, output))], body));
    }
}
