using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Trust;

internal sealed class ReputationSufficiencyCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reputation determines a target exactly by canonical target refinement.",
        H("Reputation Sufficiency Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reputation-sufficiency-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Trust/ReputationSufficiencyCriterion."
                        + "reputation_sufficiency_criterion"),
                H("Reputation sufficiency is target-relative factorization"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Full history, the score map, and future trustworthiness are independent "
                            + "source channels. Reputation is constructed publicly as the score "
                            + "map composed with full history.")),
                    Paragraph(Text(
                        "Exact determination exposes a predictor from score coordinates into the "
                            + "realized target image. Pointwise agreement of that predictor is "
                            + "equivalent to refinement of the canonical target readout by reputation.")),
                    Paragraph(Text(
                        "A pair with the same reputation and different future trustworthiness "
                            + "publicly refutes target sufficiency and proves that reputation and "
                            + "the target induce different kernels.")),
                    Paragraph(Text(
                        "The public construction R := r composed with H states directly that the "
                            + "score is a history compression. Its adequacy is relative to the "
                            + "chosen trustworthiness target.")),
                    Paragraph(Text(
                        "The exact family collision theorem is applied directly. Repository and "
                            + "pinned-library searches found no theorem combining the target-image "
                            + "predictor, collision, and compression clauses."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula historyType = Seq(F.Id("B"), Underscore, Grp(F.Id("H")));
        Formula scoreType = F.Id("S");
        Formula targetType = F.Id("Y");
        Formula history = F.Id("H");
        Formula score = F.Id("r");
        Formula target = F.Id("T");
        Formula reputation = F.Id("R");
        Formula predictor = F.Id("p");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula targetConcept = Call("canonicalTargetReadout", target);
        Formula targetRefinement = Call("Refines", targetConcept, reputation);
        Formula predictorAgreement = Seq(
            Exists, Sp, predictor, Colon, Sp,
            Arrow(scoreType, Call("TargetImage", target)), Comma, Sp,
            Forall, Sp, left, Comma, Sp,
            Call("val", Apply(predictor, Apply(reputation, left))), Sp, Eq, Sp,
            Apply(target, left));
        Formula collision = Seq(
            Exists, Sp, left, Comma, Sp, right, Comma, Sp,
            Apply(reputation, left), Sp, Eq, Sp, Apply(reputation, right), Sp,
            Land, Sp, Apply(target, left), Sp, Neq, Sp, Apply(target, right));
        Formula obstruction = Seq(
            Open, collision, Close, Sp, Rightarrow, Sp,
            Open, Neg, targetRefinement, Sp, Land, Sp,
            Call("ker", reputation), Sp, Neq, Sp, Call("ker", target), Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, historyType, Comma, Sp, scoreType,
            Comma, Sp, targetType, Colon, Sp, type, Comma, RowBreak, Grp(),
            history, Colon, Sp, Arrow(stateType, historyType), Comma, Sp,
            score, Colon, Sp, Arrow(historyType, scoreType), Comma, Sp,
            target, Colon, Sp, Arrow(stateType, targetType), Comma, RowBreak, Grp(),
            reputation, Sp, Colon, Eq, Sp, score, Sp, Circ, Sp, history, Comma,
            RowBreak, Grp(),
            Open, Open, predictorAgreement, Close, Sp, Leftrightarrow, Sp,
            targetRefinement, Close, Sp, Land, RowBreak, Grp(),
            Open, obstruction, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
