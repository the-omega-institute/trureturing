using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Zeros.ActualZeroGeometryDocument;
using static StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability.CanonicalLiGrowthZeroFreeDocument;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability;

internal sealed class CanonicalLiCurvatureZeroFreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Probability/CanonicalLiCurvatureZeroFree.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual canonical Li curvature has a direct finite-matrix-to-growth-to-zero-freeness implication.",
        H("CanonicalLiCurvatureZeroFree"), Blocks(
            Describe.Lean(DescribeId.Create("canonical-li-curvature"),
                DeclarationHandle.Create(Prefix + "canonicalLiCurvature"), H("Actual normalized second differences"),
                StatementSource.FromAuthor(All("n", new Formula.Integers(),
                    And(Imp(Equal(Id("n"), Num(0)), Equal(Call("canonicalLiCurvature", Id("n")), Num(1))),
                        Imp(NotEqual(Id("n"), Num(0)), Equal(Call("canonicalLiCurvature", Id("n")),
                            Div(Difference("canonicalLiCoefficient", Call("natAbs", Id("n"))), Multiply(Num(2), Li(Num(1))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The curvature is explicitly derived from the existing real canonical coefficients, embedded in Complex, with value one at zero and an even integer extension. NatSub is truncated natural subtraction and natAbs is the natural absolute value of an integer."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("canonical-li-curvature-zero"),
                DeclarationHandle.Create(Prefix + "canonical_li_curvature_zero"), H("Normalization at the origin"),
                StatementSource.FromAuthor(Equal(Call("canonicalLiCurvature", Num(0)), Num(1))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original Toeplitz diagonal normalization is fixed by the definition."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quadratic-of-bounded-second-difference"),
                DeclarationHandle.Create(Prefix + "quadratic_of_bounded_second_difference"), H("Two finite inductions control every coefficient"),
                StatementSource.FromAuthor(All("L", Function(Natural, Real), All("a", Real,
                    Imp(Equal(Call("L", Num(0)), Num(0)), Imp(Le(Abs(Call("L", Num(1))), Id("a")),
                        Imp(All("n", Natural, Imp(Le(Num(1), Id("n")),
                            Le(Abs(Difference("L", Id("n"))), Multiply(Num(2), Id("a"))))),
                            All("n", Natural, Le(Abs(Call("L", Id("n"))), Multiply(Id("a"), Pow(Id("n"), Num(2))))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Bounded second differences first give a linear bound on increments, then an absolute quadratic bound on the original sequence. Coefficient positivity is unnecessary."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("canonical-li-second-difference-bound-implies-rh"),
                DeclarationHandle.Create(Prefix + "canonical_li_second_difference_bound_implies_rh"), H("A uniform arithmetic difference condition suffices"),
                StatementSource.FromAuthor(Imp(SecondBound, RH)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The canonical initial values and the proved scalar induction supply the all-index growth bound consumed by actual xi analytic continuation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("canonical-curvature-second-difference-bound"),
                DeclarationHandle.Create(Prefix + "canonical_curvature_second_difference_bound"), H("Extract the bound from the original finite matrix"),
                StatementSource.FromAuthor(Imp(AllPositive, SecondBound)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Compress to indices zero and n and test the plus and minus vectors. Positivity of the canonical first coefficient justifies the normalized denominator."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("canonical-curvature-possemidef-implies-rh"),
                DeclarationHandle.Create(Prefix + "canonical_curvature_posSemidef_implies_rh"), H("Canonical curvature positivity implies actual RH"),
                StatementSource.FromAuthor(Imp(AllPositive, RH)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sole arithmetic premise is positivity at every original Toeplitz order. No supplied Li criterion, arbitrary recurrence, representing measure or zero-measure identity is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("not-rh-forces-canonical-curvature-failure"),
                DeclarationHandle.Create(Prefix + "not_rh_forces_canonical_curvature_failure"), H("A finite-order obstruction under failure of RH"),
                StatementSource.FromAuthor(Imp(new Formula.Not(RH), Exists("N", Natural,
                    new Formula.Not(Positive)))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The contrapositive guarantees a failing finite matrix order without supplying a cutoff or turning finite successful tests into a proof."))), DescribeRole.Theorem))));
    private static Formula Difference(string sequence, Formula n) => Add(
        Subtract(Call(sequence, Add(n, Num(1))), Multiply(Num(2), Call(sequence, n))),
        Call(sequence, Call("NatSub", n, Num(1))));
    private static Formula SecondBound => All("n", Natural, Imp(Le(Num(1), Id("n")),
        Le(Abs(Difference("canonicalLiCoefficient", Id("n"))), Multiply(Num(2), Li(Num(1))))));
    private static Formula Positive => Call("PosSemidef", Call("toeplitzMatrix", Id("canonicalLiCurvature"), Id("N")));
    private static Formula AllPositive => All("N", Natural, Positive);
}
