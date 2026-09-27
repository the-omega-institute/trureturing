using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class InverseLimitFeasibleMinimumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nearest feasible completed law.",
        H("A nearest feasible completed law"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("feasible-minimum"),
                DeclarationHandle.Create("D5/S3/Estimation/DataProcessing/InverseLimitFeasibleMinimum.exists_feasible_minimum_eq_iSup"),
                H("A nearest feasible completed law"),
                StatementSource.FromAuthor(Disp(new Formula.Aligned([
                    Seq(Exists, Sp, F.Id("mu"), Comma, Sp, F.Id("d"), Comma, Sp, F.Id("Q"), Colon, Sp,
                        Call("extendsMarginals", F.Id("mu")), Comma, Sp,
                        Call("finiteMinima", F.Id("d")), Comma, Sp, Call("Monotone", F.Id("d")), Comma, Sp,
                        Call("boundedByOne", F.Id("d"))),
                    Seq(Call("feasible", F.Id("Q")), Comma, Sp,
                        Call("TV", F.Id("P"), F.Id("Q")), Sp, Eq, Sp, Call("sup", F.Id("d"))),
                    Seq(Forall, Sp, F.Id("R"), Comma, Sp, Call("feasible", F.Id("R")), Sp, Rightarrow, Sp,
                        Call("TV", F.Id("P"), F.Id("Q")), Sp, Le, Sp,
                        Call("TV", F.Id("P"), F.Id("R"))),
                ]))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take a tower of finite nonempty discrete Borel alphabets with surjective bonding maps and commuting permutations. Legal joint supports are preserved by the coordinatewise bonding maps. Fix a compatible family of finite marginal probabilities and suppose that every finite feasible set is nonempty.")),
                    Paragraph(Text("The comparison probability on the completed tuple space is arbitrary. Each finite total-variation minimum is attained, and these minimum values lie between zero and one and increase with the level. There is one completed feasible law whose total-variation distance from the comparison probability equals the supremum of the finite minimum values and is no larger than the distance of any completed feasible law.")),
                    Paragraph(Text("Finite feasible sets are closed subsets of compact probability spaces: support, marginal equalities and zero expected excess are closed conditions. One-cut support transports zero excess through the bonding maps, while event pullbacks contract total variation.")),
                    Paragraph(Text("Intersect each feasible set with the ball of the same radius, the supremum of the finite minima. These nonempty compact sets form an inverse system. A common thread of laws extends to a Borel probability; the proved feasibility correspondence and full-event total-variation identity establish attainment.")),
                    Paragraph(Text("The completed marginal probability is constructed from the given finite marginal tower and has exactly those projections. No surjectivity of feasible-law maps, compatibility of separately selected minimizers, uniqueness of the nearest law or measurable selection is asserted."))),
                DescribeRole.Theorem))));
}
