using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CrownOrderPolytopeCycleIntervalsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cutting outside a proper block turns it into a linear interval.",
        H("Proper crown blocks as cyclic intervals"),
        Blocks(
            Paragraph(Text("This formal interval argument expands the consecutive-block observation in source Lemma 3.2; source and scope: "), Ref("D5/L/Combinatorics/lundstrom2025crown")),
            Paragraph(Text("For a connected compatible partition of the augmented crown at n at least two, an original block disjoint from the endpoints is connected in the cycle. If a vertex lies outside that block, cutting the cycle at this vertex gives an injective linear rank on the remaining vertices. The block occupies one interval in that rank. This module supplies internal interval lemmas for the subsequent parity and endpoint-recovery arguments; it declares no public theorem."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Geometry/CrownOrderPolytopeEnumeration"))
        ]));
}
