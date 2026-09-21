using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class ColoredPrivateResidualDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ColoredPrivateResidual.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let G be any finite simple graph with a proper coloring c:V->Fin(3). A vertex is mixed when it has two neighbors of different colors. Its reciprocal debt is 1/6-(1/2)sum_{x in N_G(w)}1/(degree_G(x)+1), in rational arithmetic. Deleting a nonempty set of positive-debt private mixed vertices preserves the mixed-degree condition and excludes singleton color leaves.",
        H("Residual graphs after positive private deletion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-private-residual"),
                DeclarationHandle.Create(Prefix + "positive_private_residual"),
                H("Mixed degrees and singleton color leaves"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume every mixed vertex of G has degree two. Let W be a nonempty finite set of mixed vertices, each with strictly positive debt. For every w in W and every neighbor x of w, assume x is nonmixed and that every mixed neighbor u of x equals w. Write G' for the induced graph on the subtype of vertices outside W, with the restricted coloring. Then every mixed vertex of G' has degree two. Moreover, for every vertex v of G', if its color class is exactly {v}, its degree in G' is not one. The ambient graph has arbitrary finite size and may contain isolated vertices. No separate surjectivity assumption is needed: the hypotheses imply that all three colors occur.")),
                    Paragraph(Text("A mixed vertex of G' is already mixed in G. If it were adjacent to a selected vertex, privacy at that selected vertex would make it nonmixed in G. Hence all its ambient neighbors survive, and the induced-neighborhood equality preserves its degree of two.")),
                    Paragraph(Text("Choose w in W. Its two neighbors r,z have different colors; properness gives three pairwise distinct colors at w,r,z, exhausting Fin(3). Positive debt gives 1/(degree_G(r)+1)+1/(degree_G(z)+1)<1/3. Each summand is positive, so each is strictly less than 1/3. Thus both degrees are strictly greater than two, hence at least three.")),
                    Paragraph(Text("Privacy makes r and z nonmixed, so they survive. Their only neighbor in W is w: any such neighbor is mixed and therefore equals w. Consequently each loses exactly one neighbor, leaving degree at least two in G'. Since r is nonmixed and adjacent to w, every surviving neighbor of r has color c(w). The at least two members of this residual neighborhood make that color class nonsingleton. Each other color contains r or z, a vertex of residual degree at least two. A singleton class of either color must therefore have degree at least two as well."))),
                DescribeRole.Theorem))));
}
