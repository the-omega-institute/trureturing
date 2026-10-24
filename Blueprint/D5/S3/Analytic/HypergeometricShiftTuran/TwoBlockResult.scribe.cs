using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.HypergeometricShiftTuran;

internal sealed class TwoBlockResultDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/kalmykovkarp2017pfq");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Negative first Turanian coefficients with a nonempty shifted numerator.",
        H("A counterexample family for Conjecture 2"), Blocks(
            Describe.Lean(DescribeId.Create("two-block-half-parameter-family-negative"),
                DeclarationHandle.Create("D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.half_parameter_family_neg"),
                H("Every multiplicity at least seven"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Take empty unshifted blocks a1 and b1, the shifted numerator a2=(1), and q shifted denominator entries all equal to one half. At mu=1 and alpha=beta=1/2, the coefficient of x is strictly negative for every natural q at least seven.")),
                    Paragraph(Text("Empty rising factorial products are one, so this Cauchy sum equals Defs.turanCoeff for the shifted blocks. With c(t)=Gamma(1+t)/Gamma(1/2+t)^q, its first coefficient is 2c(3/2)c(5/2)-c(2)^2-c(1)c(3). The integer and half-integer Gamma formulas give delta(1)=(45 pi/16)(1/2)^q-4(16/(9 pi))^q-6(16/(15 pi))^q.")),
                    Paragraph(Text("The bound pi<3.15 gives 32/(9 pi)>640/567>1. Exact rational arithmetic gives (640/567)^7>45 times 3.15 divided by 64. Monotonicity in the exponent therefore yields (32/(9 pi))^q>45 pi/64 for every q at least seven. Multiplication by 4(1/2)^q makes the middle term exceed the positive leading term, and the final term is strictly positive before subtraction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("conjecture-two-coefficient-refutation"),
                DeclarationHandle.Create("D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult.result"),
                H("Refutation of the coefficient clause"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Set q=7 in the negative coefficient family. Both unshifted blocks are empty, so their positivity requirements and condition (13) are vacuous. The shifted numerator contains the positive entry one, and the shifted denominator contains seven positive halves. The finite elementary symmetric sum for n repeated entries x in degree k is choose(n,k) times x to the power k. Hence the shifted ratio chain is (1/2)^7 at most 7(1/2)^6, with numerator symmetric values e1=1 and e0=1. All dimension, positivity and shift requirements hold.")),
                    Paragraph(Text("Universal coefficient nonnegativity would make the negative coefficient of x nonnegative. Thus the coefficient clause of Conjecture 2 is false. The shifted numerator is nonempty as required in equation (3); this differs from a counterexample with an empty shifted numerator. The result makes no assertion about the sign of the full Turanian or log-concavity at a fixed nonnegative x."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kalmykov-karp-pfq-conjecture-two-coefficients"),
                    ResolutionKind.Refuted)))));
}
