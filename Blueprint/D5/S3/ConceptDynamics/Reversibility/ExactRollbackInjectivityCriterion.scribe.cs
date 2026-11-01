using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Reversibility;

internal sealed class ExactRollbackInjectivityCriterionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact rollback from a joint update-log record is equivalent to injectivity.",
        H("Exact Rollback and Joint-Record Injectivity"),
        Blocks(
            Paragraph(Text(
                "For a fixed root of a typed named graph, let P be all finite legal words "
                    + "from that root, including the empty word. Apply the criterion with "
                    + "X equal to P, Y the residual vertex set, M the nonnegative reals, "
                    + "U the endpoint and L the descended accumulated duration. The empty "
                    + "word supplies nonemptiness even when no positive-length execution "
                    + "exists. Exact recovery then means injectivity of this same joint "
                    + "endpoint-duration map on the entire legal word language.")),
            Paragraph(Text(
                "The possible observations are the actual image of that map. A total left "
                    + "inverse on the product restricts to its inverse on the image; an "
                    + "inverse on the image can be extended outside it using the empty "
                    + "word. This extension adds no realizable observations and imposes "
                    + "no independence assumption on the endpoint and duration fields.")),
            Paragraph(Text(
                "Fix one strictly positive real duration for each actual named arrow before "
                    + "choosing words. If native one-step durations equal these values at "
                    + "every representative in a common unit and calibration, and the "
                    + "descended duration is zero on the empty word and additive under "
                    + "concatenation, induction identifies it with the sum of the actual "
                    + "arrow durations. Arrow-dependent path weights keep parallel names "
                    + "separate. This accounting identity and the rollback criterion do "
                    + "not require rationality, rational independence or equal edge values.")),
            Paragraph(Text(
                "The criterion does not decide when this joint map is injective. For a "
                    + "finite strongly connected named multigraph with at least one edge, "
                    + "equivalence with one exhaustive directed cycle is a separate graph "
                    + "statement. Its noncycle direction must produce distinct legal words "
                    + "with both the same endpoint and the same duration, and its converse "
                    + "must retain every finite stopping point, the empty word and the "
                    + "single-loop cycle. No acquisition procedure, arbitrary-real decoding "
                    + "algorithm, physical clock or resource optimum follows from the "
                    + "set-theoretic inverse.")),
            Describe.Lean(
                DescribeId.Create("exact-rollback-iff-joint-record-injective"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Reversibility/ExactRollbackInjectivityCriterion."
                        + "exact_rollback_iff_joint_record_injective"),
                H("Exact rollback criterion"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The joint record is the canonical product readout of the update and log "
                            + "channels. An exact rollback map is precisely a left inverse of this "
                            + "readout.")),
                    Paragraph(Text(
                        "Pinned Mathlib equates existence of a left inverse with injectivity. "
                            + "Applying that equivalence gives both directions of the criterion."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula CriterionFormula()
    {
        Formula state = F.Id("X");
        Formula updateOutput = F.Id("Y");
        Formula logOutput = F.Id("M");
        Formula update = F.Id("U");
        Formula log = F.Id("L");
        Formula rollback = F.Id("R");
        Formula x = F.Id("x");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula joint = Call("conceptJoin", update, log);
        Formula product = Seq(updateOutput, Sp, Times, Sp, logOutput);
        Formula exactRollback = Seq(
            Exists, Sp, Typed(rollback, Arrow(product, state)), Comma, Sp,
            Forall, Sp, Typed(x, state), Comma, Sp,
            Apply(rollback, Apply(joint, x)), Sp, Eq, Sp, x);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, Typed(Seq(state, Comma, Sp, updateOutput, Comma, Sp, logOutput), type),
            Comma, RowBreak, Grp(),
            Call("Nonempty", state), Sp, Rightarrow, RowBreak, Grp(),
            Forall, Sp, Typed(update, Arrow(state, updateOutput)), Comma, Sp,
            Typed(log, Arrow(state, logOutput)), Comma, RowBreak, Grp(),
            Open, exactRollback, Close, Sp, Iff, Sp, Call("Injective", joint), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
