using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.MoralLuck;

internal sealed class EffectiveMaximalControlCompatibleEvaluationDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/MoralLuck/EffectiveMaximalControlCompatibleEvaluation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical common coarsening is the maximal control-compatible evaluation.",
        H("Effective Maximal Control-Compatible Evaluation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("maximal-control-compatible-evaluation"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "maximal_control_compatible_evaluation"),
                H("The common coarsening is maximal among control-compatible evaluations"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Evaluation, control, and candidate are effective concepts: each readout "
                            + "is surjective onto its coordinate carrier. This is the effective "
                            + "quotient context of the common-coarsening construction and does not "
                            + "require the source carrier to be inhabited.")),
                    Paragraph(Text(
                        "The public fair evaluation is the imported canonical quotient by the "
                            + "supremum of the evaluation and control kernel relations. The first "
                            + "two conjuncts state its factorization through each input readout.")),
                    Paragraph(Text(
                        "The final public conjunct keeps the two candidate assumptions grouped. "
                            + "Reverse kernel inclusion turns them into the two bounds whose "
                            + "supremum proves the maximal factorization.")),
                    Paragraph(Text(
                        "The proof directly applies the concept-family reverse-kernel criterion, "
                            + "the canonical common-coarsening primitive, and the pinned setoid "
                            + "complete-lattice laws."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Refines(Formula coarse, Formula fine) =>
        Seq(coarse, Sp, Leq, Sp, fine);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula evaluation = Seq(F.Id("E"), Underscore, F.Id("J"));
        Formula control = Seq(F.Id("C"), Underscore, Grp(F.Id("ctl")));
        Formula candidate = F.Id("K");
        Formula evaluationReadout = Call("readout", evaluation);
        Formula controlReadout = Call("readout", control);
        Formula candidateReadout = Call("readout", candidate);
        Formula fair = Call("commonCoarsening", evaluationReadout, controlReadout);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Colon, Sp, Operatorname, Grp(F.Id("Type")),
            Comma, RowBreak, Grp(),
            evaluation, Comma, Sp, control, Comma, Sp, candidate, Sp, InMacro, Sp,
            Call("EffectiveConcept", state), Comma, RowBreak, Grp(),
            Refines(fair, evaluationReadout), Sp, Land, RowBreak, Grp(),
            Refines(fair, controlReadout), Sp, Land, RowBreak, Grp(),
            Open, Open, Refines(candidateReadout, evaluationReadout), Sp, Land, Sp,
            Refines(candidateReadout, controlReadout), Close, Sp, Rightarrow, Sp,
            Refines(candidateReadout, fair), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
