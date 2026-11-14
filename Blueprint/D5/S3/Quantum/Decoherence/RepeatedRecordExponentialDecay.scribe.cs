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
                        + "contraction under the stated cross-class Gram bound.")),
                Paragraph(Text(
                    "For a repeated-collision application, each system address labels a "
                        + "normalized environment amplitude vector. The Gram coefficient "
                        + "uses the amplitude at the first address times the conjugate "
                        + "amplitude at the second, summed over environment coordinates. "
                        + "The environment_marginal_channel theorem identifies this "
                        + "entry multiplier with tracing out a controlled record. Repeating "
                        + "the same reduced channel can be realized with fresh, initially "
                        + "uncorrelated environment registers and the same recording map. "
                        + "A correlated or reused environment is not covered merely by "
                        + "assigning it the same one-step overlap.")),
                Paragraph(Text(
                    "The error is relative to record-class pinching, in the Frobenius "
                        + "norm, the square root of the sum of squared entry magnitudes. "
                        + "It is bounded by the initial discarded coherence times the "
                        + "uniform cross-class overlap bound raised to the collision count. "
                        + "No positivity or trace-one premise is imposed on the system "
                        + "matrix, so density matrices are included as a special case. "
                        + "The estimate is not stated in trace norm or diamond norm, "
                        + "and does not by itself give a measurement discrimination error.")),
                Paragraph(Text(
                    "The equality classes contain identical amplitude vectors, not rays "
                        + "modulo phase. Distinct normalized vectors differing only by a "
                        + "phase have overlap of unit magnitude, so the strict cross-class "
                        + "bound excludes them. Distinctness alone therefore does not "
                        + "supply the decay hypothesis. Within each equality class the "
                        + "coherence is retained; complete basis dephasing requires "
                        + "singleton classes. Orthogonal distinct classes permit a zero "
                        + "bound and hence exact pinching after any positive collision count.")),
                Paragraph(Text(
                    "This application replaces a demand for exact orthogonality by a "
                        + "quantitative sufficient condition for small residual coherence. "
                        + "Normalization, the overlap bound and the repeated-channel "
                        + "description remain model premises. Their applicability to a "
                        + "particular experiment requires separate physical evidence; "
                        + "the mathematical estimate does not establish those premises.")),
                Paragraph(Text(
                    "A phase-adjusted application groups normalized records by their "
                        + "complex rays. Choose one unit representative for each ray, "
                        + "and repeat that representative at every system address in its "
                        + "class. Each original record is its representative multiplied "
                        + "by a scalar of unit modulus. Equality in Cauchy--Schwarz "
                        + "characterizes proportional unit vectors, so representatives "
                        + "of distinct rays have overlap magnitude strictly below one. "
                        + "Taking the maximum over the finitely many cross-ray pairs "
                        + "gives a uniform strict bound; if there are no such pairs, "
                        + "zero is a valid bound.")),
                Paragraph(Text(
                    "The phase correspondence must also be carried through the "
                        + "dynamics. The original Gram coefficient is the representative "
                        + "Gram coefficient times the first address's phase and the "
                        + "conjugate of the second address's phase. Entrywise "
                        + "multiplication therefore commutes with the associated diagonal "
                        + "phase action. At repetition count N, the original iterate is "
                        + "the representative-channel iterate conjugated by the diagonal "
                        + "matrix of the address phases raised to N. This preserves "
                        + "the original channel; replacing each record by its rank-one "
                        + "density matrix would instead change the Gram coefficient "
                        + "to its squared magnitude and would not give this identity.")),
                Paragraph(Text(
                    "Apply the stated theorem to these representative records. Their "
                        + "equal-vector pinching retains exactly the original same-ray "
                        + "entries. Diagonal conjugation by unit phases preserves the "
                        + "Frobenius norm, so the same decay rate bounds the distance "
                        + "from the original iterate to the conjugated ray pinching. "
                        + "The comparison is a moving coherent-block orbit: within a "
                        + "ray, an entry is multiplied by the two addresses' relative "
                        + "phase to N and need not approach a stationary value. The "
                        + "bound covers arbitrary complex system matrices and N equal "
                        + "to zero; empty finite system carriers are retained.")),
                Paragraph(Text(
                    "In this ray formulation the strict separation follows from finite "
                        + "unit-record geometry, whereas normalization, the specified "
                        + "controlled coupling and repeated application of one reduced "
                        + "channel remain premises of the physical model. The "
                        + "conditional phases belong to the coupling: the individual "
                        + "environment density matrices alone do not determine them. "
                        + "A rotating reference frame consequently needs the coupling "
                        + "or a phase calibration. This application does not establish "
                        + "a correlated-environment evolution, experimental support, "
                        + "or complete stationary dephasing."))),
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
