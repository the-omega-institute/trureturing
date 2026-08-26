using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class RecordingIsometryDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Decoherence/RecordingIsometry."
            + "recording_isometry_and_state_blocks";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical projective recording map is isometric and exposes every state block.",
        H("Recording Isometry"),
        Blocks(Describe.Lean(
            DescribeId.Create("recording-isometry-and-state-blocks"),
            DeclarationHandle.Create(Declaration),
            H("Projective recording is isometric with explicit state blocks"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The finite system and outcome carriers have decidable equality. The supplied "
                        + "matrices are self-adjoint orthogonal projectors whose sum is the identity.")),
                Paragraph(Text(
                    "The recording matrix is defined on the product basis by V((i,a),j) = "
                        + "P(a)(i,j). Its adjoint product is the identity, and conjugating any "
                        + "complex system matrix yields the displayed P(a) rho P(b) block."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Entry(Formula matrix, Formula row, Formula column) =>
        Call("entry", matrix, row, column);

    private static Formula Adjoint(Formula matrix) =>
        Seq(matrix, Caret, Grp(Star));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula system = F.Id("S");
        Formula outcome = F.Id("A");
        Formula projector = F.Id("P");
        Formula recording = F.Id("V");
        Formula rho = Rho;
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", system, system, complex);
        Formula productCarrier = Seq(system, Sp, Times, Sp, outcome);
        Formula recordingMatrix = Call("Matrix", productCarrier, system, complex);
        Formula projectorType = Arrow(outcome, matrix);
        Formula instances = And(
            Call("Fintype", system),
            And(
                Call("DecidableEq", system),
                And(Call("Fintype", outcome), Call("DecidableEq", outcome))));
        Formula selfAdjoint = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("a"),
            outcome,
            Equal(Adjoint(Apply(projector, a)), Apply(projector, a)));
        Formula orthogonal = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("a", outcome), Bound("b", outcome)],
            Equal(
                Multiply(Apply(projector, a), Apply(projector, b)),
                Call("ite", Equal(a, b), Apply(projector, a), Num(0))));
        Formula complete = Equal(
            Seq(Sum, Underscore, Grp(a, Sp, InMacro, Sp, outcome), Sp,
                Apply(projector, a)),
            F.Id("I"));
        Formula recordingDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, recording, Colon, Sp, recordingMatrix,
            Comma, Sp,
            Forall, Sp, i, Colon, Sp, system, Comma, Sp,
            a, Colon, Sp, outcome, Comma, Sp,
            j, Colon, Sp, system, Comma, Sp,
            Entry(recording, Call("pair", i, a), j), Sp, Eq, Sp,
            Entry(Apply(projector, a), i, j), Semi, Sp);
        Formula isometry = Equal(
            Multiply(Adjoint(recording), recording),
            F.Id("I"));
        Formula stateBlocks = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("rho", matrix),
                Bound("a", outcome),
                Bound("b", outcome),
                Bound("i", system),
                Bound("j", system),
            ],
            Equal(
                Entry(
                    Multiply(Multiply(recording, rho), Adjoint(recording)),
                    Call("pair", i, a),
                    Call("pair", j, b)),
                Entry(
                    Multiply(Multiply(Apply(projector, a), rho), Apply(projector, b)),
                    i,
                    j)));
        Formula conclusion = Seq(recordingDefinition, And(isometry, stateBlocks));
        Formula premises = And(selfAdjoint, And(orthogonal, complete));
        Formula projectorBinder = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("P"),
            projectorType,
            ImpliesFormula(premises, conclusion));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("S", type), Bound("A", type)],
            ImpliesFormula(instances, projectorBinder)));
    }
}
