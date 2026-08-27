using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class NonselectiveMarginalizationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Decoherence/NonselectiveMarginalization."
            + "nonselective_recording_marginal";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical finite recording map has a non-selective marginal equal to the sum of diagonal projective blocks.",
        H("Nonselective Marginalization"),
        Blocks(Describe.Lean(
            DescribeId.Create("nonselective-recording-marginal"),
            DeclarationHandle.Create(Declaration),
            H("Tracing out the recording register gives the unread update"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The system and outcome carriers are finite with decidable equality. "
                        + "Self-adjoint orthogonal projectors summing to the identity define "
                        + "the canonical recording matrix V((i,a),j) = P(a)(i,j).")),
                Paragraph(Text(
                    "The displayed partial-trace map sums equal outcome indices in each system "
                        + "matrix entry. Applied to V rho V^*, it therefore returns exactly the "
                        + "sum of the diagonal blocks P(a) rho P(a), for every complex system matrix rho.")),
                Paragraph(Text(
                    "The proof applies the frozen recording-isometry state-block theorem directly; "
                        + "no alternate recording or partial-trace primitive is introduced."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Matrix(Formula row, Formula column, Formula scalar) =>
        Call("Matrix", row, column, scalar);

    private static Formula Entry(Formula matrix, Formula row, Formula column) =>
        Call("entry", matrix, row, column);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula system = F.Id("S");
        Formula outcome = F.Id("A");
        Formula projector = F.Id("P");
        Formula recording = F.Id("V");
        Formula trace = F.Id("Tr");
        Formula rho = F.Id("rho");
        Formula joint = F.Id("X");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Matrix(system, system, complex);
        Formula jointMatrix = Matrix(
            Seq(system, Sp, Times, Sp, outcome),
            Seq(system, Sp, Times, Sp, outcome),
            complex);
        Formula projectorType = Arrow(outcome, matrix);
        Formula instances = Seq(
            Call("Fintype", system), Sp, Land, Sp,
            Call("DecidableEq", system), Sp, Land, Sp,
            Call("Fintype", outcome), Sp, Land, Sp,
            Call("DecidableEq", outcome));
        Formula selfAdjoint = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("a"),
            outcome,
            Seq(
                Seq(Operatorname, Grp(F.Id("adjoint")), Open,
                    Apply(projector, a), Close), Sp, Eq, Sp, Apply(projector, a)));
        Formula orthogonal = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("a"), outcome),
                new Formula.BoundVariable(FormulaIdentifier.Create("b"), outcome),
            ],
            Equal(
                Multiply(Apply(projector, a), Apply(projector, b)),
                Call("ite", Equal(a, b), Apply(projector, a), Num(0))));
        Formula complete = Seq(
            Seq(Sum, Underscore, Grp(a, Sp, InMacro, Sp, outcome), Sp,
                Apply(projector, a)), Sp, Eq, Sp, F.Id("I"));
        Formula recordingType = Matrix(
            Seq(system, Sp, Times, Sp, outcome), system, complex);
        Formula recordingDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, recording, Colon, Sp, recordingType,
            Comma, Sp,
            Forall, Sp, i, Comma, Sp, a, Comma, Sp, j, Colon, Sp, system,
            Comma, Sp, Entry(recording, Call("pair", i, a), j), Sp, Eq, Sp,
            Entry(Apply(projector, a), i, j), Semi, Sp);
        Formula traceDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, trace, Colon, Sp,
            Arrow(jointMatrix, matrix), Comma, Sp,
            Forall, Sp, joint, Comma, Sp, i, Comma, Sp, j, Colon, Sp, system,
            Comma, Sp, Entry(Apply(trace, joint), i, j), Sp, Eq, Sp,
            Seq(Sum, Underscore, Grp(a, Sp, InMacro, Sp, outcome), Sp,
                Entry(joint, Call("pair", i, a), Call("pair", j, a))), Semi, Sp);
        Formula conjugated = Seq(
            recording, Sp, rho, Sp, recording, Caret, Grp(Star));
        Formula conclusion = Seq(
            recordingDefinition, traceDefinition,
            Apply(trace, conjugated), Sp, Eq, Sp,
            Seq(Sum, Underscore, Grp(a, Sp, InMacro, Sp, outcome), Sp,
                Apply(Apply(Apply(projector, a), rho), Apply(projector, a))));
        Formula premises = Seq(
            instances, Sp, Land, Sp,
            projector, Colon, Sp, projectorType, Comma, Sp,
            selfAdjoint, Sp, Land, Sp, orthogonal, Sp, Land, Sp, complete);
        return Disp(Seq(
            Forall, Sp, system, Comma, Sp, outcome, Colon, Sp, type, Comma, Sp,
            premises, Sp, Rightarrow, Sp, conclusion, Dot));
    }

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
