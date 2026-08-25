using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Information;

internal sealed class CanonicalRefinementImpurityMonotonicityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Information/CanonicalRefinementImpurityMonotonicity."
            + "canonical_refinement_impurity_monotone";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical joint-fiber masses witness impurity monotonicity under refinement.",
        H("Canonical Refinement Lowers Conditional Impurity"),
        Blocks(Describe.Lean(
            DescribeId.Create("canonical-refinement-impurity-monotone"),
            DeclarationHandle.Create(Declaration),
            H("Refinement cannot increase conditional impurity"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Each target-conditioned mass is the canonical fiber mass of the joint "
                        + "concept-target readout.")),
                Paragraph(Text(
                    "The countable Cauchy inequality compares coarse and refined collision "
                        + "terms; the complementary disagreement identity gives the displayed "
                        + "impurity inequality."))),
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

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula coarseCarrier = F.Id("C");
        Formula refinedCarrier = F.Id("D");
        Formula targetCarrier = F.Id("A");
        Formula mu = F.Id("mu");
        Formula coarse = F.Id("coarse");
        Formula refined = F.Id("refined");
        Formula target = F.Id("target");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Comma, Sp, coarseCarrier, Comma, Sp,
            refinedCarrier, Comma, Sp, targetCarrier,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            mu, Colon, Sp, Operatorname, Grp(F.Id("PMF")), Open, state, Close,
            Comma, RowBreak, Grp(),
            coarse, Colon, Sp, state, Sp, To, Sp, coarseCarrier, Comma, Sp,
            refined, Colon, Sp, state, Sp, To, Sp, refinedCarrier,
            Comma, RowBreak, Grp(),
            target, Colon, Sp, state, Sp, To, Sp, targetCarrier,
            Comma, RowBreak, Grp(),
            Call("Refines", coarse, refined), Sp, Rightarrow, RowBreak, Grp(),
            Call("conditionalLogicalImpurity", mu, refined, target),
            Sp, Leq, Sp,
            Call("conditionalLogicalImpurity", mu, coarse, target), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
