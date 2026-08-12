using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class ReferenceFrameTaxDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The flat and sine reference vectors have exact values for the reduced zero-boundary nearest-neighbour quadratic form, with an explicit one-level erratum and no claim of physical reduction or global optimality.",
        H("Reduced Reference-Frame Tax Identities"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-nearest-neighbour-quadratic-form-has-zero-boundary-values"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumBounds/ReferenceFrameTax.nearestNeighborQuadratic"),
                H("The nearest-neighbour quadratic form has zero boundary values"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Id("Q"), F.Underscore, F.Grp(F.Id("N")), F.Open, F.Id("c"), F.Close,
                    F.Eq,
                    F.Sum, F.Underscore, F.Grp(F.Id("m"), F.Sp, F.InMacro, F.Sp,
                        F.Operatorname, F.Grp(F.Id("Fin")), F.Open, F.Id("N"), F.Close), F.Sp,
                    F.Open,
                    F.Frac,
                    F.Grp(
                        F.Mathbf, F.Grp(F.D(1)), F.Underscore,
                            F.Grp(F.D(0), F.Lt, F.Id("m")), F.Sp,
                        F.Id("c"), F.Underscore, F.Grp(F.Id("m"), F.Minus, F.D(1)),
                        F.Plus,
                        F.Mathbf, F.Grp(F.D(1)), F.Underscore,
                            F.Grp(F.Id("m"), F.Plus, F.D(1), F.Lt, F.Id("N")), F.Sp,
                        F.Id("c"), F.Underscore, F.Grp(F.Id("m"), F.Plus, F.D(1))),
                    F.Grp(F.D(2)),
                    F.Close, F.Caret, F.Grp(F.D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a real vector indexed by Fin N, this definition sums the squares "
                        + "of the averages of the two neighbouring coordinates. A missing left "
                        + "or right neighbour contributes zero through the two dependent "
                        + "boundary tests. In the displayed presentation, each bold 1 is the "
                        + "indicator of its subscripted condition, so it is one exactly when "
                        + "the corresponding Lean branch supplies a coordinate and zero "
                        + "otherwise.")),
                    Paragraph(Text(
                        "This is only the reduced finite real quadratic form. The module does "
                        + "not model or prove the reduction from an excitation-exchange "
                        + "unitary, a conservation-ladder reference, or entanglement fidelity "
                        + "to this expression; no certification of that physical reduction is "
                        + "claimed here."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("the-flat-reference-has-tax-three-over-two-n-above-one-level"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumBounds/ReferenceFrameTax.flat_reference_frame_tax"),
                H("The flat reference has tax three over two N above one level"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Forall, F.Sp, F.Id("N"), F.Sp, F.InMacro, F.Sp,
                        F.Mathbb, F.Grp(F.Id("N")), F.Comma, F.Esc,
                    F.D(2), F.Leq, F.Sp, F.Id("N"), F.Sp, F.Rightarrow, F.Sp,
                    F.D(1), F.Minus,
                    F.Id("Q"), F.Underscore, F.Grp(F.Id("N")), F.Open,
                        F.Open, F.Frac, F.Grp(F.D(1)),
                            F.Grp(F.Sqrt, F.Grp(F.Id("N"))), F.Close,
                        F.Underscore, F.Grp(F.Id("m"), F.Sp, F.InMacro, F.Sp,
                            F.Operatorname, F.Grp(F.Id("Fin")),
                            F.Open, F.Id("N"), F.Close),
                    F.Close,
                    F.Eq,
                    F.Frac, F.Grp(F.D(3)), F.Grp(F.D(2), F.Id("N"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural N with 2 <= N, the vector whose coordinates are all "
                    + "1 / sqrt(N) has one minus its nearest-neighbour quadratic value equal "
                    + "to 3 / (2N). The lower bound on N is part of the theorem and cannot be "
                    + "dropped."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-one-level-flat-reference-has-tax-one"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumBounds/ReferenceFrameTax.flat_reference_frame_tax_one"),
                H("The one-level flat reference has tax one"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.D(1), F.Minus,
                    F.Id("Q"), F.Underscore, F.Grp(F.D(1)), F.Open,
                        F.Open, F.Frac, F.Grp(F.D(1)),
                            F.Grp(F.Sqrt, F.Grp(F.D(1))), F.Close,
                        F.Underscore, F.Grp(F.Id("m"), F.Sp, F.InMacro, F.Sp,
                            F.Operatorname, F.Grp(F.Id("Fin")), F.Open, F.D(1), F.Close),
                    F.Close,
                    F.Eq, F.D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At N = 1 both neighbours are boundary zeros, so the quadratic value "
                        + "is zero and the tax is 1. It is not 3/2.")),
                    Paragraph(Text(
                        "The source atom stated the flat formula without restricting N. This "
                        + "compiled boundary theorem records the resulting counterexample "
                        + "instead of silently narrowing the prose claim: the exception is a "
                        + "kernel-checked erratum. This is precisely what formalization is for: "
                        + "a boundary case that reads as harmless in prose does not survive "
                        + "the kernel."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-box-sine-vector-satisfies-the-coordinate-recurrence"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumBounds/ReferenceFrameTax.sine_reference_eigenvector"),
                H("The box sine vector satisfies the coordinate recurrence"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Forall, F.Sp, F.Id("N"), F.Sp, F.InMacro, F.Sp,
                        F.Mathbb, F.Grp(F.Id("N")), F.Comma, F.Esc,
                    F.Forall, F.Sp, F.Id("m"), F.Sp, F.InMacro, F.Sp,
                        F.Operatorname, F.Grp(F.Id("Fin")), F.Open, F.Id("N"), F.Close,
                        F.Comma, F.Esc,
                    F.Theta, F.Colon, F.Eq,
                        F.Frac, F.Grp(F.Pi), F.Grp(F.Id("N"), F.Plus, F.D(1)),
                        F.Comma, F.Esc,
                    F.Id("c"), F.Underscore, F.Grp(F.Id("i")), F.Colon, F.Eq,
                        F.Sin, F.Open, F.Open, F.Id("i"), F.Plus, F.D(1), F.Close,
                            F.Theta, F.Close, F.Comma, F.Esc,
                    F.Frac,
                    F.Grp(
                        F.Mathbf, F.Grp(F.D(1)), F.Underscore,
                            F.Grp(F.D(0), F.Lt, F.Id("m")), F.Sp,
                        F.Id("c"), F.Underscore, F.Grp(F.Id("m"), F.Minus, F.D(1)),
                        F.Plus,
                        F.Mathbf, F.Grp(F.D(1)), F.Underscore,
                            F.Grp(F.Id("m"), F.Plus, F.D(1), F.Lt, F.Id("N")), F.Sp,
                        F.Id("c"), F.Underscore, F.Grp(F.Id("m"), F.Plus, F.D(1))),
                    F.Grp(F.D(2)),
                    F.Eq,
                    F.Operatorname, F.Grp(F.Id("cos")), F.Open, F.Theta, F.Close,
                        F.Id("c"), F.Underscore, F.Grp(F.Id("m"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For theta = pi / (N+1), the coordinate vector sin((i+1) theta) is an "
                    + "eigenvector of zero-boundary nearest-neighbour averaging with "
                    + "eigenvalue cos(theta). The statement includes both dependent boundary "
                    + "tests and holds at every coordinate m in Fin N."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-box-sine-vector-has-the-eigenvalue-quadratic-value"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumBounds/ReferenceFrameTax.sine_reference_quadratic_witness"),
                H("The box sine vector has the eigenvalue quadratic value"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Forall, F.Sp, F.Id("N"), F.Sp, F.InMacro, F.Sp,
                        F.Mathbb, F.Grp(F.Id("N")), F.Comma, F.Esc,
                    F.Theta, F.Colon, F.Eq,
                        F.Frac, F.Grp(F.Pi), F.Grp(F.Id("N"), F.Plus, F.D(1)),
                        F.Comma, F.Esc,
                    F.Id("Q"), F.Underscore, F.Grp(F.Id("N")), F.Open,
                        F.Open,
                            F.Sin, F.Open, F.Open, F.Id("m"), F.Plus, F.D(1), F.Close,
                                F.Theta, F.Close,
                        F.Close,
                        F.Underscore, F.Grp(F.Id("m"), F.Sp, F.InMacro, F.Sp,
                            F.Operatorname, F.Grp(F.Id("Fin")),
                            F.Open, F.Id("N"), F.Close),
                    F.Close,
                    F.Eq,
                    F.Operatorname, F.Grp(F.Id("cos")), F.Open, F.Theta, F.Close,
                        F.Caret, F.Grp(F.D(2)), F.Sp,
                    F.Sum, F.Underscore, F.Grp(F.Id("m"), F.Sp, F.InMacro, F.Sp,
                        F.Operatorname, F.Grp(F.Id("Fin")), F.Open, F.Id("N"), F.Close), F.Sp,
                    F.Sin, F.Open, F.Open, F.Id("m"), F.Plus, F.D(1), F.Close,
                        F.Theta, F.Close, F.Caret, F.Grp(F.D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Summing the squared coordinate recurrence gives the nearest-neighbour "
                    + "quadratic value of the unnormalized sine vector as cos(theta)^2 times "
                    + "the sum of sin((m+1) theta)^2. This is a witness equality, not an upper "
                    + "bound for arbitrary vectors."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("a-unit-sine-reference-attains-the-cosine-squared-value"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumBounds/ReferenceFrameTax.exists_unit_sine_reference_witness"),
                H("A unit sine reference attains the cosine-squared value"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Forall, F.Sp, F.Id("N"), F.Sp, F.InMacro, F.Sp,
                        F.Mathbb, F.Grp(F.Id("N")), F.Comma, F.Esc,
                    F.D(1), F.Leq, F.Sp, F.Id("N"), F.Sp, F.Rightarrow, F.Sp,
                    F.Theta, F.Colon, F.Eq,
                        F.Frac, F.Grp(F.Pi), F.Grp(F.Id("N"), F.Plus, F.D(1)),
                        F.Comma, F.Esc,
                    F.Exists, F.Sp, F.Id("c"), F.Colon,
                        F.Operatorname, F.Grp(F.Id("Fin")), F.Open, F.Id("N"), F.Close,
                        F.To, F.Sp, F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.Esc,
                    F.Open,
                        F.Sum, F.Underscore, F.Grp(F.Id("i"), F.Sp, F.InMacro, F.Sp,
                            F.Operatorname, F.Grp(F.Id("Fin")),
                            F.Open, F.Id("N"), F.Close), F.Sp,
                        F.Id("c"), F.Underscore, F.Grp(F.Id("i")),
                            F.Caret, F.Grp(F.D(2)),
                        F.Eq, F.D(1),
                    F.Close,
                    F.Sp, F.Land, F.Sp,
                    F.Id("Q"), F.Underscore, F.Grp(F.Id("N")), F.Open, F.Id("c"), F.Close,
                    F.Eq,
                    F.Operatorname, F.Grp(F.Id("cos")), F.Open, F.Theta, F.Close,
                        F.Caret, F.Grp(F.D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For 1 <= N, normalizing the box sine vector produces a real vector c "
                        + "with sum_i c_i^2 = 1 and nearest-neighbour quadratic value "
                        + "cos(pi/(N+1))^2. The theorem name says witness because it proves "
                        + "attainment only.")),
                    Paragraph(Text(
                        "The missing half is the universal inequality asserting that every "
                        + "unit vector c satisfies Q(c) <= cos(pi/(N+1))^2. No packaged "
                        + "mathlib theorem was found for the required path-adjacency or "
                        + "tridiagonal operator norm. Consequently this module proves neither "
                        + "an IsGreatest statement nor the claimed optimal tax identity, and it "
                        + "does not prove the claimed two-dimensional degeneracy of the "
                        + "optimum."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-flat-and-sine-taxes-coincide-at-two-levels"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumBounds/ReferenceFrameTax.flat_sine_tax_coincide_two"),
                H("The flat and sine taxes coincide at two levels"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.D(1), F.Minus,
                    F.Id("Q"), F.Underscore, F.Grp(F.D(2)), F.Open,
                        F.Open, F.Frac, F.Grp(F.D(1)),
                            F.Grp(F.Sqrt, F.Grp(F.D(2))), F.Close,
                        F.Underscore, F.Grp(F.Id("m"), F.Sp, F.InMacro, F.Sp,
                            F.Operatorname, F.Grp(F.Id("Fin")), F.Open, F.D(2), F.Close),
                    F.Close,
                    F.Eq,
                    F.Sin, F.Open,
                        F.Frac, F.Grp(F.Pi), F.Grp(F.D(2), F.Plus, F.D(1)),
                    F.Close, F.Caret, F.Grp(F.D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At N = 2, the compiled flat tax equals sin(pi/3)^2, hence 3/4. This "
                    + "checks coincidence with the sine-witness formula; by itself it does not "
                    + "establish global optimality."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-flat-and-sine-taxes-coincide-at-three-levels"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumBounds/ReferenceFrameTax.flat_sine_tax_coincide_three"),
                H("The flat and sine taxes coincide at three levels"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.D(1), F.Minus,
                    F.Id("Q"), F.Underscore, F.Grp(F.D(3)), F.Open,
                        F.Open, F.Frac, F.Grp(F.D(1)),
                            F.Grp(F.Sqrt, F.Grp(F.D(3))), F.Close,
                        F.Underscore, F.Grp(F.Id("m"), F.Sp, F.InMacro, F.Sp,
                            F.Operatorname, F.Grp(F.Id("Fin")), F.Open, F.D(3), F.Close),
                    F.Close,
                    F.Eq,
                    F.Sin, F.Open,
                        F.Frac, F.Grp(F.Pi), F.Grp(F.D(3), F.Plus, F.D(1)),
                    F.Close, F.Caret, F.Grp(F.D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At N = 3, the compiled flat tax equals sin(pi/4)^2, hence 1/2. As in the "
                    + "two-level case, the theorem exercises the exact formulas without "
                    + "supplying the absent universal upper bound."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-sine-tax-is-strictly-smaller-than-the-flat-tax-at-four-levels"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumBounds/ReferenceFrameTax.sine_tax_lt_flat_tax_four"),
                H("The sine tax is strictly smaller than the flat tax at four levels"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Sin, F.Open,
                        F.Frac, F.Grp(F.Pi), F.Grp(F.D(4), F.Plus, F.D(1)),
                    F.Close, F.Caret, F.Grp(F.D(2)),
                    F.Lt,
                    F.D(1), F.Minus,
                    F.Id("Q"), F.Underscore, F.Grp(F.D(4)), F.Open,
                        F.Open, F.Frac, F.Grp(F.D(1)),
                            F.Grp(F.Sqrt, F.Grp(F.D(4))), F.Close,
                        F.Underscore, F.Grp(F.Id("m"), F.Sp, F.InMacro, F.Sp,
                            F.Operatorname, F.Grp(F.Id("Fin")), F.Open, F.D(4), F.Close),
                    F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At N = 4, sin(pi/5)^2 is strictly smaller than the flat tax, which is "
                        + "3/8. Numerically the sine tax is approximately 0.3454915, so the separation "
                        + "appears immediately after the two compiled coincidence cases.")),
                    Paragraph(Text(
                        "These small cases keep both formulas exercised rather than merely "
                        + "stated. They show that the flat reference does not generally attain "
                        + "the sine-witness value, while making no unproved claim that the sine "
                        + "value is globally optimal.")),
                    Paragraph(Text(
                        "Before formalization, the flat and sine formulas were compared "
                        + "numerically at N = 2, 3, 4, 6, and 10 to about 1e-16. Those checks "
                        + "remain external diagnostics, not certified statements in this "
                        + "document; the compiled N = 2, 3, and 4 declarations are the exact "
                        + "small-case results recorded here."))),
                DescribeRole.Theorem
            ))));
}
