using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class OwnClockAttainmentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/OwnClockAttainment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same literal Robin interpolation attains its minimum",
        H("The same literal Robin interpolation attains its minimum"),
        Blocks(
            Paragraph(Text("The exponent domain is the closed orthant a_p>=1 in the finite real Pi-space S->R. extend a equals a on S and one outside S. Every objective occurrence is the exact imported phi S (extend a); no surrogate objective or second infimum is defined. eulerNormalization is sum_S log(1-p^(-1)), the normalization already in the actual Euler factors. This finite chart is essential: natural-indexed representatives have arbitrary invisible coordinates outside S. The value of the minimum and its sign are separate questions.")),
            Paragraph(Text("The actual upstream benefit derivative is reused directly from ContinuousPrimeMaximum. Log arguments remain positive because theta>1 gives L>1 and log L>0 on the actual orthant. Each benefit is at most -log(1-p^(-1)), giving Phi>=EulerGamma+log(log L)+eulerNormalization. Thus Phi<=M forces L<=H_M=exp(exp(M-EulerGamma-eulerNormalization)) and 1<=a_p<=H_M/log p. Since log p>=log 2>=1/2, norm(a)<=2H_M on that sublevel, an explicit coercive bound. The orthant and each literal sublevel are closed. A closed bounded sublevel is compact in this finite-dimensional real Pi-space. The all-ones sublevel is nonempty; the extreme-value theorem gives a global minimum there, and all points outside have greater objective. Existence therefore precedes the KKT argument. The original realInfimum is identified using exactly its unchanged realValues image set.")),
            Paragraph(Text("Supplier audit: Real.log_pos is applied to the actual clock>1 before ContinuousOn.log and each log_le_iff_le_exp; clock positivity alone is not treated as log positivity. Finset.sum_coe_sort converts the original supported sums to finite coordinates. IsClosed.isClosed_le consumes closedness of the orthant and continuity within that orthant. IsCompact.of_isClosed_subset places the literal sublevel in a compact finite-Pi closed ball. IsCompact.exists_isMinOn receives a nonempty sublevel and continuity restricted to it. Finally csInf_le and le_csInf use explicit bounded-below and membership witnesses for the original realValues. These image-set witnesses retain the constant-one admissible vector.")),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockattainment-extend-apply"),
                DeclarationHandle.Create(Prefix + "extend_apply"), H("Finite coordinates are preserved exactly"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The extension agrees with every supported coordinate. This is a consumed coordinate-chart identity, not a new objective."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockattainment-extend-admissible"),
                DeclarationHandle.Create(Prefix + "extend_admissible"), H("The chart preserves the original domain"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite orthant vector extends to an admissible original vector. This consumed helper supplies the consumed theta_le_clock_of_naturalSupport helper and the original image-set witness."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockattainment-clock-coordinates"),
                DeclarationHandle.Create(Prefix + "clock_coordinates"), H("The original clock in finite coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The imported clock equals sum_(p:S) a_p log p. Finset.sum_coe_sort is reused exactly. The identity is consumed by continuity, coordinate differentiation and the scalar fixed-point bridge."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockattainment-phi-coordinates"),
                DeclarationHandle.Create(Prefix + "phi_coordinates"), H("The exact objective in finite coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The imported Phi equals EulerGamma+log(log(sum_(p:S) a_p log p))-sum_(p:S) benefit(p,a_p). This consumed identity is used by the literal coordinate derivative, with no change to benefits or normalization."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockattainment-phi-restrict"),
                DeclarationHandle.Create(Prefix + "phi_restrict"), H("No original objective value is lost"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every x:N->R, extending its restriction to S leaves phi S x unchanged. Hence the finite chart retains the complete original realValues set, including every admissible real vector."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockattainment-phi-continuous-on"),
                DeclarationHandle.Create(Prefix + "phi_continuousOn"), H("Continuity on the actual closed orthant"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite clock is continuous, its two logarithms have positive arguments because theta>1, and the actual benefit is continuous by its upstream derivative. This proves ContinuousOn of the literal Phi, rather than of an auxiliary bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockattainment-coercive-lower"),
                DeclarationHandle.Create(Prefix + "coercive_lower"), H("A growing lower bound for the literal Phi"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the orthant, EulerGamma+log(log L)+eulerNormalization<=Phi. Only the total benefits are bounded; the exact terminal cost remains free to grow."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockattainment-sublevel-box"),
                DeclarationHandle.Create(Prefix + "sublevel_box"), H("Every sublevel has an explicit double-exponential box"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Phi<=M implies L<=H_M and every 1<=a_p<=H_M/log p. The proof pays positivity of L, log L and every support weight before exponentiating or dividing."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockattainment-phi-coercive"),
                DeclarationHandle.Create(Prefix + "phi_coercive"), H("Concrete coercivity in the finite-Pi norm"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real M, outside radius 2H_M within the orthant the actual Phi is strictly greater than M. The proof uses the actual coordinate masses and the pinned logarithm lower bound, not an assumed norm-equivalence or coercivity premise."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockattainment-compact-sublevel"),
                DeclarationHandle.Create(Prefix + "compact_sublevel"), H("Compact literal sublevels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The orthant is an intersection of closed coordinate halfspaces. ContinuousOn and IsClosed.isClosed_le give closed sublevels; phi_coercive puts each inside a compact finite-dimensional closed ball. Empty sublevels are allowed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockattainment-minimum-attained"),
                DeclarationHandle.Create(Prefix + "minimum_attained"), H("A genuine global minimizer exists"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compact sublevel through the all-ones vector is nonempty. IsCompact.exists_isMinOn supplies a minimizer; comparison with the sublevel threshold extends it to the whole unbounded orthant. No stationarity or optimizer existence hypothesis is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ownclock-ownclockattainment-infimum-of-minimum"),
                DeclarationHandle.Create(Prefix + "infimum_of_minimum"), H("Equality with the unchanged upstream infimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A genuine minimizer bounds every value in the original realValues image, because phi_restrict covers every old representative. Its own value belongs to that image. Conditional infimum inequalities then give realInfimum S=phi S (extend a)."))), DescribeRole.Theorem))));
}
