using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class EquiprobablePgmLoadingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/EquiprobablePgmLoading.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete loading domain and the global complement", H("The complete loading domain and the global complement"), Blocks(
            Node("loading_classification", "Full physical domain and closed activity boundary",
                "Fix 0<kappa<1 and K>1. For every t>0 with t^2<1-kappa^2 and K t^2<1, the actual symmetric matrices a=1-t^2,b=kappa t,c=1-K t^2 are strictly positive and trace one. The actual piecewise optimal POVM is feasible and uniquely maximizes success over every complex finitePOVM. Its actual nonzero-effect label set is {0,1} exactly in the closed region t<=kappa/(K-1); above it all three labels are active. Equality belongs to the two-active regime. The physical conditions here are the entire strict admissible loading domain."),
            Node("spectral_ratio", "Exact spectral ratio on the physical interval",
                "For every t>0 with t^2<1, the ratio D/q for a=1-t^2 and c=1-Kt^2 is 3(K+2)-(K+2)(K-1)t^2/(1-t^2). This identity is consumed by the global nonviolation theorem, where positivity and the full actual failure iff supply its semantic significance."),
            Node("global_nonviolation", "Global nonviolation through the sharp boundary",
                "For every 0<kappa<1, 1<K<=10/3 and every admissible t>0, use the actual optimalPovm and its nonzero-effect set A. Then (|A|-1)(P_A-1/3)<=2(P_all-1/3). This includes K=10/3 and both activity regimes. The full strict failure criterion and D/q<=16 exclude violation; in the three-active region the comparison is equality."),
            Paragraph(Text("Attribution remains separate: anonymous mechanism; old literal byline Wenlin Zhang and Haobo / trureturing; new note Haobo Ma then Wenlin Zhang. Hyunho Cha is credited for the symmetric score, qubit slice and commuting constructions. CC BY 4.0 applies only to the new note. Active means nonzero effects, including rank-one effects; the source wording about positive definite effects is ambiguous. No priority or publication claim is made."))
        ), []));

    private static DocumentBlock Node(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("equiprobablepgmloading-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/mazhang2026pgmratio")),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
