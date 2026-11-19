using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiSeventhHeightRangeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CharacterSums/PascadiSeventhHeightRange.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual singular-cover constants combine into one seventh-height constant. Real numerical implications recover the old cutoff range, supply small-coordinate bounds, and discharge the new height gap for every fixed area exponent below 26/7. These are numerical inputs to the actual counting pipeline; they do not count endpoints or assert the arbitrary-modulus conjecture.",
        H("The actual seventh-height range"),
        Blocks(
            Describe.Lean(DescribeId.Create("pascadi-seventh-height-constant"),
                DeclarationHandle.Create(Prefix + "seventhHeightConstant"), H("The actual elimination constant"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("K7=max(10368·3^9, max(14256, 24·(8·18)^4)) combines the cubic residual, actual quadratic and mixed quadratic-factor constants with the literal original pencil height 18. It equals 24·(8·18)^4."))),
                DescribeRole.Definition),
            Node("seventh_height_gap_of_old_cutoffs", "Recover seventh height from the earlier cutoffs",
                "For real p>0 and B>=1, the conditions B^5<=M^5*p^3 and (24·(8·18)^4)^5*M^40<p imply K7*B^7<p^5. The proof first gives the previous eighth-height bound, then uses B>=1. No sign assumption on M or endpoint realization is added."),
            Node("seventh_height_basic_bounds", "Small-coordinate consequences of seventh height",
                "For real p>0 and 1<=J<=I, K7*(I*J)^7<p^5 implies 18<=p, 8*I*J<p, 6*I^3<p^3 and I<=p. These bounds supply the coordinate separations used by the zero-reduction branch and the enlarged algebraic-value envelope."),
            Node("seventh_area_height_cutoff", "Every strict exponent below twenty-six sevenths",
                "For real alpha<26/7 and C>=1 there exists one positive threshold P, chosen before p and A, such that P<p, 0<=A and A<=C*p^alpha imply K7*(32*(A/p^3))^7<p^5. The positive margin is 26−7*alpha; equality alpha=26/7 is not asserted. Primality is not needed for this numerical statement."),
            Paragraph(Text("The original six-return-word problem and its LQ pencil are due to Pascadi. The constants here come from the proved structural resultant and factor-height modules. Passing from these inequalities to actual singular partners, complete original tuples, scalar centers or a final asymptotic range requires the corresponding counting theorems.")))));

    private static DocumentBlock Node(string name, string title, string statement) =>
        Describe.Lean(DescribeId.Create("pascadi-seventh-height-range-" + name.Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
