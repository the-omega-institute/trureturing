using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold;

internal sealed class FixedSourceIsingHighestWeightDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/VertexAlgebra/TwistedGround/Orbifold/FixedSourceIsingHighestWeight.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Null coefficients on odd Ising highest-weight vectors",
        H("Null coefficients on odd Ising highest-weight vectors"),
        Blocks(
            Paragraph(Text("Take a charge a with ⟨a, a⟩ = 4 and a parameter s with s² = 1. "
                + "Given hu : IsUnit D.G.det, let x in the actual odd sector paritySpace D hu (-1) "
                + "satisfy L(0)x = h · x and L(n)x = 0 for every positive integer n. "
                + "The null coefficient recursion uses fixed lattice descendants "
                + "and the action of their fields on the odd sector.")),
            Entry("fourth-null-coefficient", "nullState_fourth_mode", "Fourth null coefficient",
                "Coefficient four acts on x by 6(2h − 1)(16h − 1) times L(−1)x."),
            Entry("third-null-coefficient", "nullState_third_mode", "Third null coefficient",
                "Coefficient three acts on x by 3(64h + 7)L(−1)²x + 24h(8h − 17)L(−2)x."),
            Entry("highest-weight-null-constraint", "highest_weight_null_constraint", "First-descendant constraint",
                "Vanishing of the fourth null coefficient makes 6(2h − 1)(16h − 1)L(−1)x zero."),
            Entry("weight-zero-first-descendant", "highest_weight_zero_level_one", "Weight zero",
                "The first descendant L(−1)x vanishes at weight zero."),
            Entry("weight-half-second-descendant", "highest_weight_half_level_two", "Weight one half",
                "At weight one half the third null coefficient gives L(−2)x = (3/4)L(−1)²x."),
            Entry("weight-sixteenth-second-descendant", "highest_weight_sixteenth_level_two", "Weight one sixteenth",
                "At weight one sixteenth the third null coefficient gives L(−2)x = (4/3)L(−1)²x."))));

    private static DocumentBlock Entry(string id, string declaration, string heading, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
