using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParityProfileRegionDocument : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/ConceptDynamics/Attribution/ParityProfileRegion.attainable_iff";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The common true-flag masses for opposite three-bit parity laws form a tetrahedron.",
        H("Coupling opposite parity rows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("parity-profile-region"),
                DeclarationHandle.Create(Result),
                H("Exact region of simultaneous common flag masses"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The first row is uniform on the four even three-bit profiles. "
                        + "The second is uniform on the four odd profiles. For real masses a, b and c, "
                        + "let F(a,b,c) assert the existence of a nonnegative coupling with these row "
                        + "marginals whose three true-in-both-rows probabilities are a, b and c.")),
                    Paragraph(Text("Both marginals are fair in each coordinate, so each agreement "
                        + "probability is twice its true-in-both-rows probability. The difference of "
                        + "the coupled profiles can flip one coordinate or all three. Its four masses "
                        + "are nonnegative and sum to one, which gives the listed inequalities.")),
                    Paragraph(Text("Conversely, choose the single-coordinate flips with probabilities "
                        + "b+c-a, c+a-b and a+b-c. Choose the triple flip with the remaining probability "
                        + "1-a-b-c. Applying the sampled flip to an independent uniform even profile "
                        + "gives a uniform odd profile and the prescribed common masses."))),
                DescribeRole.Theorem))));

    private static Formula Statement() => Disp(Seq(
        F.Id("F"), Open, F.Id("a"), Comma, F.Id("b"), Comma, F.Id("c"), Close,
        Sp, Iff, Sp,
        D(0), Sp, Leq, Sp, F.Id("a"), Sp, Land, Sp, D(0), Sp, Leq, Sp, F.Id("b"),
        Sp, Land, Sp, D(0), Sp, Leq, Sp, F.Id("c"),
        Sp, Land, Sp, F.Id("a"), Sp, Leq, Sp, F.Id("b"), Sp, Plus, Sp, F.Id("c"),
        Sp, Land, Sp, F.Id("b"), Sp, Leq, Sp, F.Id("c"), Sp, Plus, Sp, F.Id("a"),
        Sp, Land, Sp, F.Id("c"), Sp, Leq, Sp, F.Id("a"), Sp, Plus, Sp, F.Id("b"),
        Sp, Land, Sp, F.Id("a"), Sp, Plus, Sp, F.Id("b"), Sp, Plus, Sp, F.Id("c"),
        Sp, Leq, Sp, D(1)));
}
