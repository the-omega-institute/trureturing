using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class JetResolventSemisimplificationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite nilpotent jet pencil reduces to one simple pole carrying its length as weight.",
        H("Jet Resolvent Semisimplification"),
        Blocks(Describe.Lean(
            DescribeId.Create("jet-resolvent-semisimplification"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/Adelic/JetResolventSemisimplification."
                    + "jet_resolvent_semisimplification"),
            H("Trace and logarithmic derivative retain only jet multiplicity"),
            StatementSource.FromAuthor(Disp(TheoremFormula())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For length m, nilpotentJetShift has value one exactly one step "
                        + "below the diagonal and zero elsewhere. The named "
                        + "jetPencil is (s-rho) times the identity minus that shift.")),
                Paragraph(Text(
                    "Only the exact-order clause assumes positive length, so its jet weight "
                        + "is nonzero. The length-zero pencil instead has determinant one and "
                        + "trace resolvent zero, and therefore has no pole. Only the pointwise "
                        + "trace identity requires s != rho, its exact invertibility domain.")),
                Paragraph(Text(
                    "Lower triangularity makes the pencil determinant (s-rho)^m and every "
                        + "diagonal inverse entry (s-rho)^(-1). Summing the diagonal and "
                        + "differentiating the determinant give the two displayed identities. "
                        + "The punctured identity also proves that the trace resolvent is "
                        + "meromorphic with order minus one and that multiplication by s-rho "
                        + "converges to the nonzero residue m."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula length = F.Id("m");
        Formula zero = F.Id("rho");
        Formula point = F.Id("s");
        Formula variable = F.Id("z");
        Formula pencilAt = Call("jetPencil", length, zero, point);
        Formula inversePencil = new Formula.Power(
            pencilAt,
            Seq(Minus, D(1)));
        Formula traceResolvent = Call("trace", inversePencil);
        Formula determinantFunction = Lambda(
            variable,
            Call("det", Call("jetPencil", length, zero, variable)));
        Formula logarithmicDerivative = Call("logDeriv", determinantFunction, point);
        Formula simplePole = new Formula.Fraction(
            length,
            Seq(point, Sp, Minus, Sp, zero));
        Formula traceFunction = Lambda(
            variable,
            Call("trace", new Formula.Power(
                Call("jetPencil", length, zero, variable),
                Seq(Minus, D(1)))));
        Formula meromorphic = Call("MeromorphicAt", traceFunction, zero);
        Formula poleOrder = EqualTo(
            Call("meromorphicOrderAt", traceFunction, zero),
            Seq(Minus, D(1)));
        Formula puncturedNeighborhood = Call(
            "nhdsWithin",
            zero,
            Seq(complex, Sp, Setminus, Sp, OpenBrace, zero, CloseBrace));
        Formula residueFunction = Lambda(
            variable,
            Seq(
                Grp(Seq(variable, Sp, Minus, Sp, zero)), Sp, Times, Sp,
                Call("trace", new Formula.Power(
                    Call("jetPencil", length, zero, variable),
                    Seq(Minus, D(1))))));
        Formula residueLimit = Call(
            "Tendsto",
            residueFunction,
            puncturedNeighborhood,
            Call("nhds", length));
        Formula traceClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(NotEqualTo(point, zero), EqualTo(traceResolvent, simplePole)));
        Formula logDerivativeClause = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            EqualTo(logarithmicDerivative, simplePole));
        Formula exactOrderClause = Implies(
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, length),
            poleOrder);
        Formula conclusions = And(
            traceClause,
            And(
                logDerivativeClause,
                And(meromorphic, And(exactOrderClause, residueLimit))));

        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("m", natural),
                Bound("rho", complex),
            ],
            conclusions);
    }
}
