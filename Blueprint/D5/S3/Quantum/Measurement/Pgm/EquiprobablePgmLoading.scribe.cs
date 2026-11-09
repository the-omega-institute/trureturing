using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Pgm;

internal sealed class EquiprobablePgmLoadingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmLoading.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete loading domain and the global complement", H("The complete loading domain and the global complement"), Blocks(
            Node("loading_classification", "Full physical domain and closed activity boundary",
                "Fix 0<kappa<1 and K>1. For every t>0 with t^2<1-kappa^2 and K t^2<1, the actual symmetric matrices a=1-t^2,b=kappa t,c=1-K t^2 are strictly positive and trace one. The actual piecewise optimal POVM is feasible and uniquely maximizes success over every complex finitePOVM. Its actual nonzero-effect label set is {0,1} exactly in the closed region t<=kappa/(K-1); above it all three labels are active. Equality belongs to the two-active regime. The physical conditions here are the entire strict admissible loading domain."),
            Node("spectral_ratio", "Exact spectral ratio on the physical interval",
                "For every t>0 with t^2<1, the ratio D/q for a=1-t^2 and c=1-Kt^2 is 3(K+2)-(K+2)(K-1)t^2/(1-t^2). This identity is consumed by the global nonviolation theorem, where positivity and the full actual failure iff supply its semantic significance."),
            Node("global_nonviolation", "Global nonviolation through the sharp boundary",
                "For every 0<kappa<1, 1<K<=10/3 and every admissible t>0, use the actual optimalPovm and its nonzero-effect set A. Then (|A|-1)(P_A-1/3)<=2(P_all-1/3). This includes K=10/3 and both activity regimes. The full strict failure criterion and D/q<=16 exclude violation; in the three-active region the comparison is equality."),
            Node("states", "Actual loading density family", "The actual matrices are rho(1-t^2,kappa t,1-Kt^2), with the exact full-domain conditions stated in loading_classification.", DescribeRole.Definition),
            Node("sharp_threshold", "Sharp small-parameter threshold", "For every fixed 0<kappa<1 and K>1, an entire sufficiently small positive interval consists of actual PD states, has the actual active pair, and strictly violates the actual score comparison if and only if K>10/3. The converse consumes global_nonviolation and includes equality K=10/3.", DescribeRole.Theorem),
            Node("strict_stability", "Strict violation persists under symmetric perturbations", "At every 0<a,c<1, b>0, b^2<a(1-a), |c-a|<b with strict actual CFC violation, all sufficiently nearby triples retain actual PD states, strict inactivity, the unique actual pair optimum among all complex POVMs, and strict actual violation. The neighborhood quantifier ranges over all three symmetric-model coordinates.", DescribeRole.Theorem),
            Node("asymptotics", "Actual loading gap through cubic remainder", "For each fixed 0<kappa<1,K>1 as t decreases to zero, the actual gap equals (2kappa^2/3)(1-4/sqrt(3(K+2)))t-[4(K-1)^2/(9(K+2))]t^2+O(t^3), in filter-based IsBigO form. Eventual full admissibility and exact actual scores justify the expansion.", DescribeRole.Theorem),
            Paragraph(Text("Attribution remains separate: anonymous mechanism; old literal byline Wenlin Zhang and Haobo / trureturing; new note Haobo Ma then Wenlin Zhang. Hyunho Cha is credited for the symmetric score, qubit slice and commuting constructions. CC BY 4.0 applies only to the new note. Active means nonzero effects, including rank-one effects; the source wording about positive definite effects is ambiguous. No priority or publication claim is made."))
        ), []));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("equiprobablepgmloading-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/mazhang2026pgmratio")),
        Blocks(Paragraph(Text(prose))), role);
}
