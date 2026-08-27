using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Decoherence;

internal sealed class RepeatedRecordExponentialDecayDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Quantum/Decoherence/RepeatedRecordExponentialDecay."
            + "repeated_record_exponential_decay";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Repeated finite records contract cross-class coherence at the uniform Gram rate.",
        H("Repeated Record Exponential Decay"),
        Blocks(Describe.Lean(
            DescribeId.Create("repeated-record-exponential-decay"),
            DeclarationHandle.Create(Declaration),
            H("Repeated records converge exponentially to record-class pinching"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The record amplitudes construct both the Gram channel and the class "
                        + "projectors. The projector sum therefore uses the actual equality "
                        + "classes of environment records.")),
                Paragraph(Text(
                    "The first clause is the exact entrywise iterate. The second computes "
                        + "the projector sum, and the final clause is its Frobenius norm "
                        + "contraction under the stated cross-class Gram bound."))),
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

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d"), e = F.Id("e"), n = F.Id("N");
        Formula i = F.Id("i"), j = F.Id("j"), a = F.Id("a");
        Formula record = F.Id("E"), q = F.Id("q"), rho = Rho;
        Formula label = F.Id("l"), projector = F.Id("P"), pinching = F.Id("Pch");
        Formula nat = F.Id("Nat"), real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula system = Call("Fin", d), environment = Call("Fin", e);
        Formula matrix = Call("Matrix", system, system, complex);
        Formula recordType = Arrow(system, Arrow(environment, complex));
        Formula recordAtI = Apply(record, i), recordAtJ = Apply(record, j);
        Formula gram = Call("recordGram", record, i, j);
        Formula channelIterate = Call("iterate", Call("recordChannel", record), n, rho);
        Formula normalized = Equal(
            Seq(Sum, Underscore, Grp(a, Sp, InMacro, Sp, environment), Sp,
                Multiply(
                    new Formula.Norm(Apply(recordAtI, a)),
                    new Formula.Norm(Apply(recordAtI, a)))),
            D(1));
        Formula normalization = new Formula.BindMany(
            FormulaQuantifier.ForAll, [Bound("i", system)], normalized);
        Formula qType = Call("Ico", D(0), D(1));
        Formula distinctRecords = new Formula.Relation(
            recordAtI, FormulaRelationOperator.NotEqual, recordAtJ);
        Formula gramBound = Seq(
            distinctRecords, Sp, Rightarrow, Sp,
            LessOrEqual(new Formula.Norm(gram), q));
        Formula allGramBounds = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", system), Bound("j", system)], gramBound);
        Formula projectorAt = Call("recordClassProjector", record, label);
        Formula pinchingAtRho = Apply(pinching, rho);
        Formula pinchingDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            pinching, Colon, Sp, Arrow(matrix, matrix), Comma, Sp,
            rho, Mapsto, Sp,
            Seq(Sum, Underscore, Grp(label, Sp, InMacro, Sp,
                Call("range", record)), Sp,
                Multiply(Multiply(projectorAt, rho), projectorAt)), Semi, Sp);
        Formula iterateClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("N", nat), Bound("rho", matrix), Bound("i", system), Bound("j", system)],
            Equal(
                Entry(channelIterate, i, j),
                Multiply(Power(gram, Seq(n)), Entry(rho, i, j))));
        Formula pinchingEntry = Equal(
            Entry(pinchingAtRho, i, j),
            Call("ite", Equal(recordAtI, recordAtJ), Entry(rho, i, j), D(0)));
        Formula pinchingClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("rho", matrix), Bound("i", system), Bound("j", system)],
            pinchingEntry);
        Formula contraction = LessOrEqual(
            new Formula.Norm(Subtract(channelIterate, pinchingAtRho)),
            Multiply(Power(Seq(q), Seq(n)),
                new Formula.Norm(Subtract(rho, pinchingAtRho))));
        Formula contractionClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("N", nat), Bound("rho", matrix)], contraction);

        Formula conclusion = Seq(
            pinchingDefinition,
            And(iterateClause, And(pinchingClause, contractionClause)));

        return Disp(Seq(
            Forall, Sp, d, Colon, Sp, nat, Comma, Sp,
            e, Colon, Sp, nat, Comma, RowBreak, Grp(),
            record, Colon, Sp, recordType, Comma, RowBreak, Grp(),
            normalization, Comma, RowBreak, Grp(),
            q, Colon, Sp, qType, Comma, RowBreak, Grp(),
            Grp(allGramBounds), Sp, Rightarrow, RowBreak, Grp(),
            conclusion, Dot));
    }
}
