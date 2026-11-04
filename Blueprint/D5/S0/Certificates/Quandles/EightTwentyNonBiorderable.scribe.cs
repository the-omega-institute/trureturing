using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Quandles;

internal sealed class EightTwentyNonBiorderableDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S0/Certificates/Quandles/EightTwentyNonBiorderable.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Certificates/gupta2025biorderability");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact eight-relation presented quandle admits no full-domain biorder.",
        H("The 8_20 presentation: candidate full-domain non-biorderability"),
        Blocks(
            Node("arcs", "Eight original arcs", "Arc", DescribeRole.Definition,
                "The labels a,b,c,d,e,f,g,h are exactly those of the primary source's oriented Figure fig8_20."),
            Node("crossings", "All eight crossings", "Crossing", DescribeRole.Definition,
                "The relations are b*e=a, c*g=b, d*g=e, g*e=h, f*d=g, d*a=c, a*c=h, f*c=e. Every paper product x*y is represented as Mathlib Shelf.act y x. Relations 1 and 2 remain in the presentation and are checked by the coloring, though the strict-order obstruction uses only 3 through 8."),
            Node("quotient", "The full presented carrier", "KnotQuandle", DescribeRole.Definition,
                "This is PresentedQuandle.Carrier Crossing, the quotient of unrestricted action and inverse-action terms by exactly the quandle axioms and all crossings. Its universal property is proved in the dependency module. Identifying this algebraic presentation with the fundamental quandle of the oriented knot is an EXTERNAL SOURCE MAP from the original diagram and presentation, not a formal theorem of ambient isotopy or knot recognition. The independent fidelity review remains decisive for that boundary."),
            Node("generators", "Actual generator classes", "arc", DescribeRole.Definition,
                "Each arc is its class in the entire quotient. Separation is proved by evaluation rather than imposed as an axiom."),
            Node("convention", "The paper operation", "op", DescribeRole.Definition,
                "op x y is Shelf.act y x. The dihedral instance matches 2*y-x directly. Mathlib's group conjugation convention would need inverse action for the paper's group example; no conjugation-group replacement is used."),
            Node("coloring", "The exact mod-nine coloring", "color", DescribeRole.Definition,
                "The primary paper's tuple is (7,6,5,0,2,8,1,3). Kernel-safe finite reduction checks every original equation. The target is the existing Mathlib dihedral quandle, used only for separation."),
            Node("homomorphism", "Coloring of the entire presented quandle", "colorHom", DescribeRole.Definition,
                "The universal evaluation property supplies a genuine ShelfHom on every quotient class. Evaluating d and g gives 0 and 1, so their actual classes differ. This assumes neither that the coloring is injective nor that its finite target is ordered."),
            Node("claim", "One order on the whole carrier", "claim", DescribeRole.Definition,
                "The closed proposition asserts existence of one LinearOrder on the complete presented quandle with both strict translation laws. It does not restrict the quantifiers to generators or terms of bounded length. Every D2 extension would satisfy this order-existence claim, so its negation excludes that author possibility without trusting table exhaustiveness."),
            Node("refutation", "Closed negation of full-domain biorderability", "result", DescribeRole.Theorem,
                "A hypothetical whole-domain biorder makes the generic six-relation obstruction force d=g. The constructed coloring separates them, giving a contradiction. The result is literally Not claim, with no homomorphism, generator-distinctness or desired conclusion hidden in its hypotheses. This implementation is repo-prior-exposed and a candidate only. Independent source fidelity, current literature status and final review are pending; no solved-original, priority, unique, official-acceptance or KPI claim is made.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Certificates/Quandles/PresentedQuandle")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Certificates/Quandles/SixRelationObstruction"))]));

    private static DocumentBlock Node(string id, string title, string name, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
