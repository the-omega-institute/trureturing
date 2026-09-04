using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Decision;

internal sealed class AdmissionDescentCriterionDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Decision/AdmissionDescentCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Admission descends through a visible quotient exactly when its fibers have no mixed "
            + "boundary and its universal core and existential hull coincide.",
        H("Admission Descent Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fiber-constant-iff-core-and-hull-equalities"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "fiberConstant_iff_core_eq_and_hull_eq"),
                H("Fiber constancy is simultaneous core and hull equality"),
                StatementSource.FromAuthor(CoreHullFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If admission is constant on visible fibers, the current state witnesses "
                        + "existential hull membership and transports membership to every state "
                        + "in the universal core. Conversely, universal-core equality alone "
                        + "transports admission membership in both directions across a fiber."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("admission-descent-four-way-criterion"),
                DeclarationHandle.Create(DeclarationPrefix + "admission_descent_criterion"),
                H("Four equivalent clauses characterize admission descent"),
                StatementSource.FromAuthor(DescentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an anchored state space, an admission predicate factors through the "
                            + "visible quotient exactly when it is constant on each quotient fiber.")),
                    Paragraph(Text(
                        "The same condition is equivalent both to emptiness of the mixed-fiber "
                            + "boundary and to simultaneous equality with the universal fiber core "
                            + "and existential fiber hull.")),
                    Paragraph(Text(
                        "The factorization and empty-boundary clauses reuse the frozen repository "
                            + "theorem AnswerabilityCriterion.answerability_criterion. The new "
                            + "proof obligation is the simultaneous core-hull characterization."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula CoreHullFormula()
    {
        Formula q = F.Id("q");
        Formula admitted = F.Id("A");
        return Disp(Seq(
            Call("FiberConstant", q, admitted), Sp, Leftrightarrow, Sp,
            Open,
            admitted, Sp, Eq, Sp, Call("universalFiberCore", q, admitted),
            Sp, Land, Sp,
            admitted, Sp, Eq, Sp, Call("existentialFiberHull", q, admitted),
            Close, Dot));
    }

    private static Formula DescentFormula()
    {
        Formula q = F.Id("q");
        Formula admitted = F.Id("A");
        Formula descended = F.Id("Abar"), x = F.Id("x");
        Formula descent = Seq(
            Exists, Sp, descended, Colon, Sp, F.Id("B"), Sp, To, Sp,
            Operatorname, Grp(F.Id("Prop")), Comma, Sp,
            Forall, Sp, x, Comma, Sp,
            x, Sp, InMacro, Sp, admitted, Sp, Leftrightarrow, Sp,
            Apply(descended, Apply(q, x)));
        Formula constant = Call("FiberConstant", q, admitted);
        Formula boundary = Seq(Call("admissionBoundary", q, admitted), Sp, Eq, Sp, Emptyset);
        Formula coreHull = Seq(
            admitted, Sp, Eq, Sp, Call("universalFiberCore", q, admitted),
            Sp, Land, Sp,
            admitted, Sp, Eq, Sp, Call("existentialFiberHull", q, admitted));

        return Disp(Seq(
            Open, descent, Close, Sp, Leftrightarrow, Sp, constant,
            Sp, Leftrightarrow, Sp, boundary,
            Sp, Leftrightarrow, Sp, Open, coreHull, Close, Dot));
    }
}
