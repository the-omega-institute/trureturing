using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta;

internal sealed class QuadraticLValueSquareDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/CharacterSums/chensun2024doublecharacters");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two genuine primitive functional equations for a nonprincipal character eliminate its root number in the product with the inverse character. Nonvanishing at one permits cancellation. For odd characters the Gamma factors yield L(0,chi)L(0,inverse chi)=N*L(1,chi)L(1,inverse chi)/pi squared; the retained self-dual square formulas follow as live specializations.", H("QuadraticLValueSquare"), Blocks(
            Paragraph(Text("Two genuine primitive functional equations for a nonprincipal character eliminate its root number in the product with the inverse character. Nonvanishing at one permits cancellation. For odd characters the Gamma factors yield L(0,chi)L(0,inverse chi)=N*L(1,chi)L(1,inverse chi)/pi squared; the retained self-dual square formulas follow as live specializations.")),
            Paragraph(Text("Four-slot escape registrations are unfinished, tracked at https://github.com/the-omega-institute/trureturing/issues/26321. No declared_validated status is claimed. This registration debt is separate from the native mathematical proof.")),
            Paragraph(Text("The inverse-character extension serves the historical Merca quartic-character argument. It does not evaluate the sign of a quadratic Gauss sum and does not itself establish a number-field class-number formula. The new public product targets have unfinished four-slot audits at https://github.com/the-omega-institute/trureturing/issues/27629; no validated registration is claimed.")),
            Describe.Lean(DescribeId.Create("quadraticlvaluesquare-completed-zero-mul-inverse"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/QuadraticLValueSquare.completed_zero_mul_inverse"), H("completed_zero_mul_inverse"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The same primitive functional equation at zero and one relates the actual completed inverse-character products. Nonvanishing at one makes the common root-number cancellation valid, without a self-duality premise."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticlvaluesquare-zero-mul-inverse"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/QuadraticLValueSquare.zero_mul_inverse"), H("zero_mul_inverse"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every primitive nonprincipal odd character the inverse character is also odd. The actual Gamma factors at zero and one give the uncompleted product identity with N and pi squared."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticlvaluesquare-completed-zero-sq"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/QuadraticLValueSquare.completed_zero_sq"), H("completed_zero_sq"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Two applications of the functional equation eliminate the root number without choosing its sign. This is an equality for the actual completed L-functions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadraticlvaluesquare-zero-sq"),
                DeclarationHandle.Create("D5/S3/Analytic/Zeta/QuadraticLValueSquare.zero_sq"), H("zero_sq"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For odd characters the two Gamma factors are 1 and the reciprocal of pi. No root-number evaluation is used in this uncompleted L-value identity."))), DescribeRole.Theorem))));
}
