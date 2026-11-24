using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.BRST;

internal sealed class ActualLeechOrbifoldRelativeNormTwoCohomologyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/VertexAlgebra/BRST/ActualLeechOrbifoldRelativeNormTwoCohomology.";

    private static DocumentBlock Theorem(string name, string id, string title, string statement) =>
        Describe.Lean(DescribeId.Create("actual-leech-orbifold-relative-norm-two-cohomology-" + id),
            DeclarationHandle.Create(Module + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual norm-two relative BRST quotient is one-dimensional in ghost degree one.",
        H("Actual Leech orbifold norm-two relative BRST cohomology"), Blocks(
            Paragraph(Text("For each integral ghost degree, the cochains are the corresponding "
                + "eigenspace of ghost number on the relative shell. The differential restricts the "
                + "actual BRST charge Q. Cohomology quotients its kernel by the range of the preceding "
                + "differential, which lands in the kernel by Q² = 0.")),
            Describe.Lean(DescribeId.Create("actual-leech-orbifold-relative-norm-two-cohomology-one"),
                DeclarationHandle.Create(Module + "cohomologyOne"), H("Degree-one equivalence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In degree one the coefficient ρ of a cycle induces a complex "
                    + "linear equivalence from the quotient to ℂ."))), DescribeRole.Definition),
            Theorem("cohomologyOne_psiClass", "generator-value", "Value on the distinguished class",
                "The equivalence sends the class of the relative generator ψ to 1."),
            Theorem("psiClass_ne_zero", "generator-nonzero", "Nonzero cohomology class",
                "The class of ψ is nonzero in the degree-one quotient."),
            Theorem("cohomology_vanishes", "other-degrees", "Vanishing in all other degrees",
                "For every integer q different from one, the degree-q relative BRST quotient is a subsingleton."))));
}
