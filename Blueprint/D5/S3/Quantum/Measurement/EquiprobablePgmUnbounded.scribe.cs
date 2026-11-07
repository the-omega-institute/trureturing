using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class EquiprobablePgmUnboundedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/EquiprobablePgmUnbounded.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unbounded centered ratios for actual mixed qubit states", H("Unbounded centered ratios for actual mixed qubit states"), Blocks(
            Node("family", "The complete fixed-dimension family",
                "For every real 0<epsilon<=1/8, states are rho_+/-=[[1-epsilon^6,+/-epsilon^3/2],[+/-epsilon^3/2,epsilon^6]] and rho_3=diag(1-epsilon^4,epsilon^4). All are strictly positive and trace one, so in dimension two they are mixed. The actual unique optimal finitePOVM is (Q+,Q-,0), active set {0,1}, and success=(1+epsilon^3)/3. With H=(1+2epsilon^2)(3-epsilon^4(1+2epsilon^2))>3, actual eta_A=epsilon^3/(6sqrt(1-epsilon^6)) and eta_all=epsilon^4[1/(3sqrt(H))+2(1-epsilon^2)^2/(3H)]. These are identities for the existing CFC pgmScore, not definitions of surrogate scores."),
            Node("uniform_ratio", "A uniform quantitative estimate",
                "On the entire interval 0<epsilon<=1/8, the actual full centered advantage is positive and eta_A/eta_all>=3/[2(2+sqrt(3))epsilon]>3/(8epsilon). The bound is uniform; no finite sample is used."),
            Node("every_constant", "Every positive real constant at fixed (2,3,2)",
                "For every real C>0 there exists 0<epsilon<=1/8 with actual strictly positive trace-one qubit states, the actual unique optimum (Q+,Q-,0), exactly two nonzero effects, eta_all>0 and eta_A>C eta_all. The proof chooses epsilon=min(1/8,3/(8C))/2 and applies the uniform estimate. Dimension, number of labels and number of active labels are fixed throughout."),
            Node("score_limits", "Centered divergence and the raw-score limit",
                "As epsilon tends to zero through positive reals, both actual centered advantages tend to zero, the raw score ratio P_A/P_all tends to one, and the centered ratio tends to positive infinity. This says nothing against a quantitative positive spectral-floor estimate or the general all-pure comparison, both of which remain open in the supplied sources."),
            Paragraph(Text("Attribution remains separate: anonymous mechanism; old literal byline Wenlin Zhang and Haobo / trureturing; new note Haobo Ma then Wenlin Zhang. Hyunho Cha is credited for the symmetric score, qubit slice and commuting constructions. CC BY 4.0 applies only to the new note. Active means nonzero effects, including rank-one effects; the source wording about positive definite effects is ambiguous. No priority or publication claim is made."))
        ), []));

    private static DocumentBlock Node(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("equiprobablepgmunbounded-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/mazhang2026pgmratio")),
        Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
