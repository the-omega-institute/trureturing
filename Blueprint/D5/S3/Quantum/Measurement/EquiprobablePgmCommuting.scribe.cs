using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;
internal sealed class EquiprobablePgmCommutingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/EquiprobablePgmCommuting.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal actual-object PGM control", H("EquiprobablePgmCommuting"), Blocks(
            Node("every_optimum", "Every actual optimum on the five-dimensional support",
                "For every 0<epsilon<7/18, the first four states have populations (1-epsilon)e0+epsilon e_i, i=1..4, and the fifth (1-2epsilon)e0+(epsilon/2)sum_(i=1..4)e_i. These actual diagonal trace-one PSD matrices commute. An actual POVM attains (1+3epsilon)/5. Every optimal complex POVM, including competitors with off-diagonal entries, has this score and precisely the first four nonzero effects. Complementary products with the diagonal dual slack force the fifth effect to vanish and each rare coordinate to be assigned to its unique maximizing label. This theorem is on the complete five-dimensional joint support."),
            Node("scores_and_gap", "The complete commuting interval and exact CFC scores",
                "On every 0<epsilon<7/18, actual P_A=(1+3epsilon)/5=P_opt and P_all=1/5+32epsilon/75+4epsilon^2/[25(5-6epsilon)]. For centered eta_A=P_A-1/5 and eta=P_all-1/5 the exact gap is 3eta_A-4eta=epsilon(7-18epsilon)/[15(5-6epsilon)]>0. The endpoints are excluded. The diagonal Moore-Penrose score theorem evaluates actual CFC objects, including the zeros in individual states."),
            Node("nonunique", "Nonuniqueness of the optimal measurement",
                "For every epsilon>0 the displayed score optimization has two distinct actual optimal finitePOVMs, obtained by allocating the common coordinate wholly to two different first-four labels. On the physical interval they are optimal discrimination POVMs for the stated density ensemble. The common-coordinate tie explains nonuniqueness. No every-optimum activity claim is made about effects living entirely in an unused ambient kernel."),
            Paragraph(Text("The construction and symmetric calculations are credited to Hyunho Cha. Mechanism attribution remains anonymous; old literal byline Wenlin Zhang and Haobo / trureturing; new note Haobo Ma then Wenlin Zhang. CC BY 4.0 applies to the new note only. The original nonzero-effect interpretation of activity is retained, including rank-one effects; the source wording about positive definite effects is ambiguous. General all-pure and positive-spectral-floor comparisons remain open."))
        ), []));
    private static DocumentBlock Node(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("equiprobablepgmcommuting-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/anonymous2026pgmmechanism")),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
