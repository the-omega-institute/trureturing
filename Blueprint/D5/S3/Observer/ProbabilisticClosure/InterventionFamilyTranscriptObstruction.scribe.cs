using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class InterventionFamilyTranscriptObstructionDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Repeated sampling and adaptive or randomized processing cannot separate two models "
            + "that have the same law under every intervention in the allowed family.",
        H("Intervention-Family Transcript Obstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("repeated-intervention-family-kernel-obstruction"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/"
                        + "InterventionFamilyTranscriptObstruction."
                        + "repeated_intervention_family_kernel_obstruction"),
                H("Repeated use of one intervention family cannot cross its kernel"),
                StatementSource.FromAuthor(ObstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The profile jointReadout(law) is the canonical tuple of all allowed "
                            + "intervention laws. Equality of every family member makes this "
                            + "complete profile equal at the two models.")),
                    Paragraph(Text(
                        "At the law level, an adaptive transcript constructor may use arbitrary "
                            + "repeat and sample counts, and the final law may undergo arbitrary "
                            + "randomized postprocessing. Both are functions of the same family "
                            + "profile, so their final laws remain equal.")),
                    Paragraph(Text(
                        "If both final laws were exact, their equality would force the two "
                            + "target values to agree, contradicting the source distinction."))),
                DescribeRole.Theorem))));

    private static Formula ObstructionFormula()
    {
        Formula type = F.Id("Type");
        Formula intervention = F.Id("Intervention");
        Formula model = F.Id("Model");
        Formula lawType = F.Id("Law");
        Formula transcriptType = F.Id("TranscriptLaw");
        Formula decisionType = F.Id("DecisionLaw");
        Formula nat = F.Id("Nat");
        Formula law = F.Id("law");
        Formula target = F.Id("target");
        Formula firstModel = F.Id("M");
        Formula secondModel = F.Id("N");
        Formula repetitions = F.Id("repetitions");
        Formula sampleSize = F.Id("sampleSize");
        Formula transcript = F.Id("adaptiveTranscriptLaw");
        Formula postprocess = F.Id("randomizedPostprocess");

        Formula lawTypeSignature = Arrow(intervention, Arrow(model, lawType));
        Formula targetTypeSignature = Arrow(model, decisionType);
        Formula transcriptSignature =
            Arrow(nat, Arrow(nat, Arrow(model, transcriptType)));
        Formula postprocessSignature = Arrow(transcriptType, decisionType);
        Formula profileM = Call("jointReadout", law, firstModel);
        Formula profileN = Call("jointReadout", law, secondModel);
        Formula transcriptM = Apply(transcript, repetitions, sampleSize, firstModel);
        Formula transcriptN = Apply(transcript, repetitions, sampleSize, secondModel);
        Formula decisionM = Apply(postprocess, transcriptM);
        Formula decisionN = Apply(postprocess, transcriptN);

        Formula sameFamilyLaw = Equal(profileM, profileN);
        Formula differentTarget = NotEqual(
            Apply(target, firstModel),
            Apply(target, secondModel));
        Formula familyFactorization = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("repetitions", nat),
                Bound("sampleSize", nat),
                Bound("M", model),
                Bound("N", model),
            ],
            Implies(
                Equal(profileM, profileN),
                Equal(transcriptM, transcriptN)));
        Formula exactAtBoth = And(
            Equal(decisionM, Apply(target, firstModel)),
            Equal(decisionN, Apply(target, secondModel)));
        Formula protocolConclusion = And(
            Equal(decisionM, decisionN),
            new Formula.Not(exactAtBoth));
        Formula allProtocols = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("repetitions", nat),
                Bound("sampleSize", nat),
                Bound("randomizedPostprocess", postprocessSignature),
            ],
            protocolConclusion);

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Intervention", type),
                Bound("Model", type),
                Bound("Law", type),
                Bound("TranscriptLaw", type),
                Bound("DecisionLaw", type),
                Bound("law", lawTypeSignature),
                Bound("target", targetTypeSignature),
                Bound("M", model),
                Bound("N", model),
                Bound("adaptiveTranscriptLaw", transcriptSignature),
            ],
            Implies(
                And(differentTarget, And(sameFamilyLaw, familyFactorization)),
                allProtocols)));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
