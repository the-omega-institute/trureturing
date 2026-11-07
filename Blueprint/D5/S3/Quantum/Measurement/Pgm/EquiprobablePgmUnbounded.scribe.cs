using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement.Pgm;

internal sealed class EquiprobablePgmUnboundedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/Pgm/EquiprobablePgmUnbounded.";

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
            Node("states", "Actual fixed-size mixed-state family", "The three actual qubit matrices are rho(1-epsilon^6,epsilon^3/2,1-epsilon^4), with original prior 1/3 and 0<epsilon<=1/8.", DescribeRole.Definition),
            Node("H", "Actual score denominator polynomial", "H(epsilon)=(1+2epsilon^2)(3-epsilon^4(1+2epsilon^2)); the family theorem proves H>3 on the physical interval and uses H in its actual score formula.", DescribeRole.Definition),
            Node("spectral_minima", "Actual average spectral minima", "For every 0<epsilon<=1/8, the actual original-prior pair average has least real spectral value 2epsilon^6/3 and the actual full average has least real spectral value (epsilon^4+2epsilon^6)/3. Membership and minimality are both proved by diagonal spectral calculus, with no assumed evaluation bridge.", DescribeRole.Theorem),
            Node("spectral_floor_limits", "Actual spectral infima tend to zero", "The infima of the actual pair and full average spectra tend to zero as epsilon decreases to zero. The proof consumes spectral_minima on an entire eventual physical interval. The construction supplies no positive uniform spectral floor, and does not settle comparisons with a quantitative floor.", DescribeRole.Theorem),
            Paragraph(Text("Attribution remains separate: anonymous mechanism; old literal byline Wenlin Zhang and Haobo / trureturing; new note Haobo Ma then Wenlin Zhang. Hyunho Cha is credited for the symmetric score, qubit slice and commuting constructions. CC BY 4.0 applies only to the new note. Active means nonzero effects, including rank-one effects; the source wording about positive definite effects is ambiguous. No priority or publication claim is made."))
        ), []));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("equiprobablepgmunbounded-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/mazhang2026pgmratio")),
        Blocks(Paragraph(Text(prose))), role);
}
