using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class DivisorAssociationDirichletDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/DivisorAssociationDirichlet.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite association quotient has a genuine nonnegative Dirichlet energy whose kernel is exactly the q-measurable source data.",
        H("Dirichlet Energy of the Association Fibers"),
        Blocks(
            Paragraph(Text("For a finite exponent box, form the finite set of ordered source pairs "
                + "with equal observed position q. The pairwise energy sums the squared source-value "
                + "differences over those pairs. It is a finite quadratic form, so its positivity is "
                + "checked directly in Lean and does not use an RH equivalence.")),
            Entry("sameFiberPairs", "Equal-observation source pairs",
                "The ordered pairs of box sources whose q-images agree.", DescribeRole.Definition),
            Entry("fiberEnergy", "Pairwise fiber Dirichlet energy",
                "The sum over equal-q pairs of (u(s)-u(t))².", DescribeRole.Definition),
            Entry("fiberEnergy_nonneg", "Energy positivity",
                "Every finite-box fiber energy is nonnegative by termwise square positivity.",
                DescribeRole.Theorem),
            Entry("fiberEnergy_eq_zero_iff", "Kernel characterization",
                "The energy vanishes exactly when the source function is constant on every q-fiber "
                    + "inside the box. This is the finite Fisher/Dirichlet kernel statement.",
                DescribeRole.Theorem),
            Entry("fiberEnergy_pullback_zero", "q-measurable pullbacks are in the kernel",
                "Any position function pulled back along q has zero fiber energy.",
                DescribeRole.Theorem),
            Entry("fiberEnergy_pos_of_collision", "Collision witness",
                "A single equal-q pair with distinct source values forces strictly positive energy.",
                DescribeRole.Theorem),
            Entry("fiberEnergy_5040_hidden_pos", "5040 hidden-label defect",
                "On the (4,2,1,1) exponent box corresponding to 5040, the fourth-exponent "
                    + "potential has positive energy because (1,0,0,1) and (2,0,1,0) share q "
                    + "but have different hidden labels. This is a finite exact witness, not an "
                    + "assertion of Robin's inequality or RH.", DescribeRole.Theorem),
            Paragraph(Text("The construction is deliberately source-complete at the finite-box level: "
                + "the kernel statement records precisely which information is lost by q. Connecting "
                + "this quadratic form to the original Robin N_p, S_X or I_X requires an additional "
                + "source lift and is not claimed by this module."))
        )));

    private static DocumentBlock Entry(string selector, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(selector.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
