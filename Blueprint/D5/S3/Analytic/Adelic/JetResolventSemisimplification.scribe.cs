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
                    "The displayed non-pole premise is the exact invertibility domain of "
                        + "the source resolvent. The logarithmic derivative is Mathlib's "
                        + "branch-independent deriv(f)/f operation, so no principal-log "
                        + "branch condition is introduced.")),
                Paragraph(Text(
                    "Lower triangularity makes the pencil determinant (s-rho)^m and every "
                        + "diagonal inverse entry (s-rho)^(-1). Summing the diagonal and "
                        + "differentiating the determinant therefore give the same simple "
                        + "pole of weight m, exposed again by the final conjunct."))),
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
        Formula conclusions = And(
            EqualTo(traceResolvent, simplePole),
            And(
                EqualTo(logarithmicDerivative, simplePole),
                EqualTo(traceResolvent, logarithmicDerivative)));

        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("m", natural),
                Bound("rho", complex),
                Bound("s", complex),
            ],
            Implies(NotEqualTo(point, zero), conclusions));
    }
}
