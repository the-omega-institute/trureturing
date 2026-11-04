using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class EulerNineSquareDissectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/EulerNineSquareDissection.";
    private static readonly LibraryNoteRef Question = LibraryNoteRef.Create("D5/L/Fourier/bringmann2024periodic");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cubic residue extraction and positive decompositions control every squared section.", H("EulerNineSquareDissection"), Blocks(
            Paragraph(Text("Write A=Q4, B9=Q2, C=Q1, and use the actual coloured partition product D from EulerNineComparison. The residue-two section of R^3 vanishes by the existing cubic theta dissection. Expanding the proved R dissection and cancelling the constant-one unit A gives B9^2=AC+qCD. Hence W=2AC-B9^2=(1-q)AC+q(AC-CD). Both summands are nonnegative by the paid restricted-product comparisons and exact AD=B9C multiplicities. This proves the difficult lower bounds without division of an inequality. The sole auxiliary degree-one hole is removed by ordinary partition smoothing in EtaSignK10.")),
            Node("0", "restricted_cubic_relation", "B9^2=AC+qCD is derived from actual theta suppliers and unit cancellation.", DescribeRole.Theorem),
            Node("1", "U", "The positive first squared section A^2+2qB9C.", DescribeRole.Definition),
            Node("2", "V", "The signed second squared section 2AB9-qC^2.", DescribeRole.Definition),
            Node("3", "W", "The difficult third squared section 2AC-B9^2.", DescribeRole.Definition),
            Node("4", "coeff_U_ge_one", "Every natural coefficient of U is at least one.", DescribeRole.Theorem),
            Node("5", "coeff_V_ge_one", "Every natural coefficient of V is at least one by a positive exact decomposition.", DescribeRole.Theorem),
            Node("6", "W_positive_decomposition", "W equals the lower reciprocal product plus q times the nonnegative difference AC-CD.", DescribeRole.Theorem),
            Node("7", "coeff_W_nonnegative", "Every coefficient of W is nonnegative.", DescribeRole.Theorem),
            Node("8", "W_initial", "W has constant coefficient one and degree-one coefficient zero.", DescribeRole.Theorem),
            Node("9", "coeff_W_ge_one", "Every W coefficient at degree zero or at least two is at least one.", DescribeRole.Theorem),
            Node("10", "R_square_dissection", "The actual squared quotient is U(q^3)-qV(q^3)-q^2W(q^3).", DescribeRole.Theorem)
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("eulerninesquaredissection-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Question),
            Blocks(Paragraph(Text(text))), role);
}
