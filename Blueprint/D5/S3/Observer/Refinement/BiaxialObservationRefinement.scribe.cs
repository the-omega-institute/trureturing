using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Refinement;

internal sealed class BiaxialObservationRefinementDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint refinement enlarges the observation schedule and shrinks its indistinguishability relation.",
        H("Biaxial Observation Refinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("biaxial-observation-refinement"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Refinement/BiaxialObservationRefinement."
                        + "biaxial_observation_refinement"),
                H("Both observation axes refine in their natural directions"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The observation schedule is the existing set of index-time pairs whose "
                            + "index lies in the finite set and whose time is below the horizon.")),
                    Paragraph(Text(
                        "Containment of index sets and ordering of horizons first include the "
                            + "smaller schedule in the larger schedule. This is the source's first "
                            + "public set relation.")),
                    Paragraph(Text(
                        "The imported biaxial monotonicity theorem then reverses inclusion of the "
                            + "associated indistinguishability relations, providing the second "
                            + "public set relation without restating its proof."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula output = F.Id("O");
        Formula smaller = F.Id("J");
        Formula larger = F.Id("K");
        Formula shorter = F.Id("m");
        Formula longer = F.Id("n");
        Formula readout = F.Id("readout");
        Formula transition = F.Id("T");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula finiteNaturals = Call("Finset", naturals);

        Formula smallSchedule = Call("observationSchedule", smaller, shorter);
        Formula largeSchedule = Call("observationSchedule", larger, longer);
        Formula smallIndist = Call("Indist", smaller, shorter, readout, transition);
        Formula largeIndist = Call("Indist", larger, longer, readout, transition);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(state, type), Comma, Sp, Typed(output, type), Comma),
            Seq(
                Typed(smaller, finiteNaturals), Comma, Sp,
                Typed(larger, finiteNaturals), Comma, Sp,
                Typed(shorter, naturals), Comma, Sp, Typed(longer, naturals), Comma),
            Seq(
                Typed(readout, Arrow(naturals, Arrow(state, output))), Comma, Sp,
                Typed(transition, Arrow(state, state)), Comma),
            Seq(
                smaller, Sp, Subseteq, Sp, larger, Sp, Land, Sp,
                shorter, Sp, Leq, Sp, longer, Sp, Rightarrow),
            Seq(
                smallSchedule, Sp, Subseteq, Sp, largeSchedule, Sp, Land),
            Seq(
                largeIndist, Sp, Subseteq, Sp, smallIndist, Dot),
        ]));
    }
}
