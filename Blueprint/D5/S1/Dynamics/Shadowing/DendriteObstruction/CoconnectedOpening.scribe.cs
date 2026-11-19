using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing.DendriteObstruction;

internal sealed class DendriteObstructionCoconnectedOpeningDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/DendriteObstruction/CoconnectedOpening.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Small openings with connected complements.",
        H("DendriteObstruction - CoconnectedOpening"), Blocks(
        Describe.Lean(DescribeId.Create("compact-path-small-opening"),
            DeclarationHandle.Create(Owner + "compact_path_small_opening"),
            H("Small openings with connected complements"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("In every nondegenerate compact metric space joined by actual continuous interval paths, for every eta>0 there is a nonempty compact connected proper subset Q whose nonempty open complement has diameter strictly below eta.")),
                Paragraph(Text("Take a finite cover by balls of radius eta/8 and repeat it periodically. Expand each current proper continuum inside a proper continuum neighbourhood. When the current cover element has a point outside such a neighbourhood, remove precisely its difference from that neighbourhood; otherwise remove the whole complement. The component of the resulting closed carrier containing the neighbourhood is the next continuum. Each continuum is contained in the interior of the next. Their union G is open and proper by compactness; its complement K is nonempty compact.")),
                Paragraph(Text("Choose a path from the initial point to K and its first K-hit e. Every cover element meeting K must have e in its closure. Otherwise a terminal path segment avoids that element, a compact initial segment is absorbed into a finite stage, and a late repeat of the element makes the entire path lie in a single component avoiding the removed open set. This puts e in G, a contradiction. Thus K lies in the closed eta/4 ball about e. Compactness absorbs the complement of the open eta/3 ball into one finite continuum Q. Its complement lies in that ball and has diameter at most 2eta/3<eta.")),
                Paragraph(Text("This is classical continuum theory attributed to Krasinkiewicz and Minc, Continua and their open subsets with connected complements, Fundamenta Mathematicae 102, pages 129-136, DOI 10.4064/fm-102-2-129-136. Heath and Nall, Centers of a dendroid, DOI 10.4064/fm189-2-6, page 180, state the small co-connected-open property for dendroids. The proof here supplies the component, folding and finite-cover arguments directly; no cited theorem is used as an axiom."))), DescribeRole.Theorem))));
}
