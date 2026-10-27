using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.HypergeometricShiftTuran;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/kalmykovkarp2017pfq");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A family of negative first Turanian coefficients.",
        H("Half shifts with repeated denominator parameters"), Blocks(
            Describe.Lean(DescribeId.Create("half-parameter-family-negative"),
                DeclarationHandle.Create("D5/S3/Analytic/HypergeometricShiftTuran/Result.half_parameter_family_neg"),
                H("Every multiplicity at least six"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take no numerator parameters, q denominator parameters all equal to one half, base parameter mu=1, and shifts alpha=beta=1/2. For every natural q at least six, the coefficient of x in the shifted Turanian is strictly negative.")),
                    Paragraph(Text("Here c(t)=Gamma(t+1/2) raised to the power -q. The two terms in the first Cauchy coefficient give delta(1)=2(1/2)^q-(16/(9 pi))^q-(16/(15 pi))^q. The half-integer Gamma formula gives Gamma(3/2)Gamma(7/2)=15 pi/16 and Gamma(5/2) squared equal to 9 pi/16; Gamma(2)=1 and Gamma(3)=2.")),
                    Paragraph(Text("The bound pi<3.15 implies 32/(9 pi)>640/567>1. The sixth power of 640/567 is greater than two. Monotonicity in the exponent therefore gives (32/(9 pi))^q>2 for q at least six. Multiplication by (1/2)^q makes the middle term larger than the positive leading term, and the final term is strictly positive before subtraction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hypergeometric-shift-coefficient-refutation"),
                DeclarationHandle.Create("D5/S3/Analytic/HypergeometricShiftTuran/Result.result"),
                H("Refutation of the coefficient assertion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Set q=6 in the negative coefficient family. The empty numerator vector has positive entries vacuously, every denominator entry is positive, and p=0 makes the symmetric ratio chain vacuous. The parameters mu=1 and alpha=beta=1/2 satisfy all shift restrictions, including alpha at most beta+1. Universal coefficient nonnegativity would require this strictly negative first coefficient to be nonnegative.")),
                    Paragraph(Text("The coefficient conclusion in the p at most q branch is therefore false, and so is the conjecture asserting all conclusions in this parameter range. The argument concerns a power-series coefficient and makes no claim about the sign of the Turanian as a function on the nonnegative real axis."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kalmykov-karp-pfq-conjecture-one-coefficients"),
                    ResolutionKind.Refuted)))));
}
