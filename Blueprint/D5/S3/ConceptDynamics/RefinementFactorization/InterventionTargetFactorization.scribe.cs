using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementFactorization;

internal sealed class InterventionTargetFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula intervention = F.Id("A");
        Formula model = F.Id("M");
        Formula targetType = F.Id("Y");
        Formula lawFamily = F.Id("L");
        Formula law = F.Id("law");
        Formula target = F.Id("T");
        Formula action = F.Id("a");
        Formula factor = F.Id("f");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula lawAtAction = new Formula.Subscript(lawFamily, action);
        Formula profile = Call("jointReadout", law);
        Formula causalImage = Call("range", profile);
        Formula causalProjection = Call("rangeFactorization", profile);
        Formula uniqueFactorization = Seq(
            Exists, Bang, Sp, factor, Colon, Sp, causalImage, Sp, To, Sp,
            targetType, Comma, Sp, target, Sp, Eq, Sp,
            factor, Sp, Circ, Sp, causalProjection);
        Formula kernelInclusion = Seq(
            Call("ker", profile), Sp, Subseteq, Sp, Call("ker", target));
        Formula statement = Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, intervention, Comma, Sp, model, Comma, Sp,
            targetType, Colon, Sp, type, Comma, RowBreak, Grp(),
            lawFamily, Colon, Sp, intervention, Sp, To, Sp, type, Comma,
            RowBreak, Grp(),
            law, Colon, Sp, Forall, Sp, action, Colon, Sp, intervention,
            Comma, Sp, model, Sp, To, Sp, lawAtAction, Comma,
            RowBreak, Grp(),
            target, Colon, Sp, model, Sp, To, Sp, targetType, Comma,
            RowBreak, Grp(),
            Open, uniqueFactorization, Close, Sp, Leftrightarrow, Sp,
            Open, kernelInclusion, Close, Dot,
            End, Grp(F.Id("gathered"))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Allowed-intervention law kernels characterize unique target descent "
                + "through the realized causal image.",
            H("Intervention Target Factorization"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("intervention-target-factorization"),
                    DeclarationHandle.Create(
                        "D5/S3/ConceptDynamics/RefinementFactorization/"
                            + "InterventionTargetFactorization."
                            + "intervention_target_factorization"),
                    H("The causal image carries exactly the identifiable targets"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Each allowed intervention supplies a law-valued readout on the "
                                + "same model carrier. The canonical joint readout constructs "
                                + "their complete dependent profile, and its realized range is "
                                + "the causal image named in the theorem.")),
                        Paragraph(Text(
                            "Kernel containment says that models with the same complete "
                                + "intervention profile must have the same target value. The "
                                + "public statement exposes the resulting unique factor and its "
                                + "commuting equation directly on that realized image.")),
                        Paragraph(Text(
                            "The pinned realized-image representative chooses a source model for "
                                + "each profile in the causal image. Kernel containment makes the "
                                + "resulting target value representative-independent, while "
                                + "surjectivity of the canonical range map proves uniqueness."))),
                    DescribeRole.Theorem))));
    }

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
}
