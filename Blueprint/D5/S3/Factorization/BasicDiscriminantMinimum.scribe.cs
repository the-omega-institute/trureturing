using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class BasicDiscriminantMinimumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five is the least member of the explicit positive odd squarefree discriminant class.",
        H("Minimum of the Basic Discriminant Class"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("five-basic-discriminant"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/BasicDiscriminantMinimum.five_basic_discriminant"),
                H("Five is a basic discriminant"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("BasicDiscriminant"), Open, D(5), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The number five is greater than one, squarefree, and congruent to one modulo four, "
                    + "so it belongs to the explicit basic-discriminant class."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("basic-discriminant-minimum"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/BasicDiscriminantMinimum.basic_discriminant_minimum"),
                H("Every basic discriminant is at least five"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("d"), InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("BasicDiscriminant"), Open, F.Id("d"), Close, Sp,
                    Rightarrow, Sp, D(5), Sp, Leq, Sp, F.Id("d")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A basic discriminant is a natural number d satisfying 1 < d, squarefreeness, "
                        + "and d congruent to 1 modulo 4. The elementary arithmetic inequalities force "
                        + "every such d to satisfy 5 <= d.")),
                    Paragraph(Text(
                        "Together with the preceding witness at d = 5, this proves that five is the least "
                        + "positive member of the stated odd squarefree discriminant class. No broader claim "
                        + "about fundamental discriminants is made."))),
                DescribeRole.Theorem
            )),
        []));
}
