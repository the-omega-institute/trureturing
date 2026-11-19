using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BKMActualMetricHeatDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/BKMActualMetricHeat.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite BKM compressions of one physical heat evolution have a factored two-step defect difference.",
        H("Finite BKM heat compression"),
        Blocks(
            Entry("relative-projection", "relativeProjection", "Projection for a coercive form",
                "On a finite-dimensional complex Hilbert space, compress a coefficient Z to the " +
                "visible subspace. Its strictly positive lower operator bound makes the Gram " +
                "compression injective and hence invertible. Applying its inverse to P Z gives " +
                "the relative projection into that same subspace.", DescribeRole.Definition),
            Entry("relative-projection-fix", "relativeProjection_fix", "Visible vectors are fixed",
                "Applied to a visible vector, the right-hand side of the Gram equation is exactly " +
                "the Gram compression of that vector."),
            Entry("relative-projection-orthogonal", "relativeProjection_orthogonal",
                "Orthogonality of the residual",
                "The Gram equation says that the coefficient applied to the residual is orthogonal " +
                "to every visible vector."),
            Entry("visible-coordinates", "visibleCoordinates", "One physical visible subspace",
                "The reference square-root coordinate map sends the physical matrix subspace B " +
                "onto V. Both compressions use V.", DescribeRole.Definition),
            Entry("changed-projection", "changedProjection", "Projection for the changed BKM form",
                "Use the relative BKM operator as the coefficient Z. The density sandwich " +
                "supplies the positive lower bound in reference coordinates.", DescribeRole.Definition),
            Entry("bkm-orthogonality", "changedProjection_bkm_orthogonal", "Physical BKM orthogonality",
                "Pull the changed projection back to matrix space through the reference coordinates. " +
                "Its residual pairs to zero with every member of B in the BKM form at a."),
            Entry("reference-generator", "referenceGenerator", "Generator in reference coordinates",
                "Conjugate the bounded physical generator L by the square-root coordinates of b.",
                DescribeRole.Definition),
            HeatComparison())));

    private static DocumentBlock Entry(string id, string declaration, string title, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static DocumentBlock HeatComparison() => Describe.Lean(
        DescribeId.Create("heat-defect-comparison"),
        DeclarationHandle.Create(Module + "bkm_heat_defect_comparison"),
        H("Physical heat defect identity and bound"),
        StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(
            Paragraph(Text(
                "Let a and b be positive definite matrices with l b ≤ a ≤ u b and 0 < l ≤ u. " +
                "For a complex matrix subspace B, work on its image V in the square-root " +
                "coordinates of b. Write P for the reference orthogonal projection and R for the " +
                "projection induced by the BKM form at a. Both are maps into V.")),
            Paragraph(Text(
                "For any bounded complex-linear physical generator L and real time t, use its " +
                "single conjugate in the reference coordinates to define the operators T at " +
                "time t and T₂ at time 2t. With i the inclusion of V, define E = R T i and " +
                "E₀ = P T i. The defect difference is the two-step defect of R minus that of P.")),
            Paragraph(Math(DefectDifference())),
            Paragraph(Text(
                "Let K be the restriction of R to the reference orthogonal complement, W the " +
                "hidden-to-hidden block of T, and C its visible-to-hidden block. For every complex " +
                "scalar c, the difference satisfies the following identity and estimate in operator " +
                "norms induced by the reference BKM form.")),
            Paragraph(Math(F.Disp(Equal(Id("D"), Compose(
                Parenthesized(Subtract(Compose(Id("K"), Id("W")), Compose(Id("E"), Id("K")))),
                Id("C"))))),
            Paragraph(Math(DefectBound()))),
        DescribeRole.Theorem);

    private static Formula DefectBound()
    {
        var scale = F.Seq(F.Frac, F.Grp(Subtract(Id("u"), Id("l"))),
            F.Grp(Multiply(F.D(2), F.Seq(F.Sqrt, F.Grp(Multiply(Id("u"), Id("l")))))));
        var shift = Multiply(Id("c"), Id("I"));
        var blockNorms = Parenthesized(Add(
            new Formula.Norm(Subtract(Id("W"), shift)),
            new Formula.Norm(Subtract(Id("E"), shift))));
        return F.Disp(F.Seq(new Formula.Norm(Id("D")), F.Sp, F.Leq, F.Sp,
            Multiply(Multiply(scale, blockNorms), new Formula.Norm(Id("C")))));
    }

    private static Formula DefectDifference()
    {
        var doubleTime = Subscript(Id("T"), F.D(2));
        var changed = Subtract(Compose(Id("R"), doubleTime, Id("i")), Square(Id("E")));
        var reference = Subtract(Compose(Id("P"), doubleTime, Id("i")), Square(Subscript(Id("E"), F.D(0))));
        return F.Disp(Equal(Id("D"), Subtract(Parenthesized(changed), Parenthesized(reference))));
    }

    private static Formula Compose(params Formula[] maps)
    {
        var factors = new List<Formula>();
        foreach (var map in maps)
        {
            if (factors.Count > 0)
                factors.AddRange([F.Sp, F.Circ, F.Sp]);
            factors.Add(map);
        }
        return F.Seq([.. factors]);
    }

    private static Formula Parenthesized(Formula value) => F.Seq(F.Open, value, F.Close);
    private static Formula Subscript(Formula value, Formula index) => F.Seq(value, F.Underscore, F.Grp(index));
    private static Formula Square(Formula value) => F.Seq(value, F.Caret, F.Grp(F.D(2)));
}
