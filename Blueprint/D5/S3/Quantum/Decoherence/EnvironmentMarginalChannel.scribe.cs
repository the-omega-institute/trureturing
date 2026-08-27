using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class EnvironmentMarginalChannelDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Decoherence/EnvironmentMarginalChannel."
            + "environment_marginal_channel";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite controlled environment record reduces to its Gram entrywise channel.",
        H("Environment Marginal Channel"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-environment-marginal-is-the-record-gram-channel"),
            DeclarationHandle.Create(Declaration),
            H("Finite environment marginal is the record Gram channel"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For finite system and environment coordinate sets, the displayed matrix V "
                        + "writes the environment amplitudes belonging to each system address. "
                        + "The displayed environment trace sums equal environment coordinates.")),
                Paragraph(Text(
                    "For every complex system matrix, tracing V rho V^* gives the canonical "
                        + "recordChannel and also the Hadamard product of rho with the canonical "
                        + "recordGram matrix. The final clause states the same calculation at "
                        + "each system-matrix entry."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Entry(Formula matrix, Formula row, Formula column) =>
        Call("entry", matrix, row, column);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), e = F.Id("e"), i = F.Id("i"), j = F.Id("j");
        Formula a = F.Id("a"), record = F.Id("E"), rho = Rho, joint = F.Id("X");
        Formula recording = F.Id("V"), trace = F.Id("T"), gram = F.Id("G");
        Formula nat = F.Id("Nat"), complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula system = Call("Fin", d), environment = Call("Fin", e);
        Formula systemMatrix = Call("Matrix", system, system, complex);
        Formula product = Seq(system, Sp, Times, Sp, environment);
        Formula jointMatrix = Call("Matrix", product, product, complex);
        Formula recordingMatrix = Call("Matrix", product, system, complex);
        Formula recordType = Arrow(system, Arrow(environment, complex));
        Formula pairIA = Call("pair", i, a), pairJA = Call("pair", j, a);
        Formula recordingEntry = Call(
            "ite", Equal(j, i), Apply(Apply(record, i), a), Num(0));
        Formula recordingDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, recording, Colon, Sp, recordingMatrix,
            Comma, Sp,
            Forall, Sp, i, Colon, Sp, system, Comma, Sp,
            a, Colon, Sp, environment, Comma, Sp,
            j, Colon, Sp, system, Comma, Sp,
            Equal(Entry(recording, pairIA, j), recordingEntry), Semi, Sp);
        Formula traceDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, trace, Colon, Sp,
            Arrow(jointMatrix, systemMatrix), Comma, Sp,
            Forall, Sp, joint, Colon, Sp, jointMatrix, Comma, Sp,
            i, Colon, Sp, system, Comma, Sp, j, Colon, Sp, system, Comma, Sp,
            Equal(
                Entry(Apply(trace, joint), i, j),
                Seq(Sum, Underscore, Grp(a, Sp, InMacro, Sp, environment), Sp,
                    Entry(joint, pairIA, pairJA))), Semi, Sp);
        Formula conjugated = Multiply(Multiply(recording, rho),
            Seq(recording, Caret, Grp(Star)));
        Formula marginal = Apply(trace, conjugated);
        Formula gramLambda = Seq(
            Open, i, Comma, Sp, j, Close, Sp, Mapsto, Sp,
            Call("recordGram", record, i, j));
        Formula hadamard = Call("hadamard", gramLambda, rho);
        Formula matrixEqualities = And(
            Equal(marginal, Call("recordChannel", record, rho)),
            Equal(marginal, hadamard));
        Formula entrywise = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", system), Bound("j", system)],
            Equal(
                Entry(marginal, i, j),
                Multiply(Call("recordGram", record, i, j), Entry(rho, i, j))));
        Formula conclusion = Seq(
            recordingDefinition, traceDefinition, And(matrixEqualities, entrywise));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("d", nat), Bound("e", nat), Bound("E", recordType),
                Bound("rho", systemMatrix)],
            conclusion));
    }
}
