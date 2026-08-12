using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class ReferenceFrameTaxOptimalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp scale-free upper bound completes the sine reference witness as the greatest value of the reduced zero-boundary nearest-neighbour quadratic form and yields the optimal-tax identity, without claiming the physical reduction to that form.",
        H("Optimal Reduced Reference-Frame Tax"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("the-cosine-squared-value-is-a-universal-scale-free-upper-bound"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumBounds/ReferenceFrameTaxOptimal.nearestNeighborQuadratic_le_cos_sq"),
                H("The cosine-squared value is a universal scale-free upper bound"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Forall, F.Sp, F.Id("N"), F.Sp, F.InMacro, F.Sp,
                        F.Mathbb, F.Grp(F.Id("N")), F.Comma, F.Esc,
                    F.Forall, F.Sp, F.Id("c"), F.Colon,
                        F.Operatorname, F.Grp(F.Id("Fin")), F.Open, F.Id("N"), F.Close,
                        F.To, F.Sp, F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.Esc,
                    F.Id("Q"), F.Underscore, F.Grp(F.Id("N")),
                        F.Open, F.Id("c"), F.Close,
                    F.Leq, F.Sp,
                    F.Operatorname, F.Grp(F.Id("cos")), F.Open,
                        F.Frac, F.Grp(F.Pi), F.Grp(F.Id("N"), F.Plus, F.D(1)),
                    F.Close, F.Caret, F.Grp(F.D(2)), F.Sp,
                    F.Sum, F.Underscore, F.Grp(F.Id("i"), F.Sp, F.InMacro, F.Sp,
                        F.Operatorname, F.Grp(F.Id("Fin")),
                        F.Open, F.Id("N"), F.Close), F.Sp,
                    F.Id("c"), F.Underscore, F.Grp(F.Id("i")),
                        F.Caret, F.Grp(F.D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural N and every real vector c indexed by Fin N, the "
                        + "nearest-neighbour quadratic value is at most cos(pi/(N+1))^2 times "
                        + "the sum of the squared coordinates. There is no hypothesis on N. "
                        + "The statement is scale-free and therefore stronger than the unit-"
                        + "vector inequality needed for optimality.")),
                    Paragraph(Text(
                        "The proof is elementary and deliberately avoids operator norms and "
                        + "diagonalisation: mathlib supplies no packaged path-graph or "
                        + "tridiagonal norm result for this form. For each averaged pair it "
                        + "applies weighted Cauchy-Schwarz in the form ((a+b)/2)^2 <= "
                        + "((u+v)/4)(a^2/u+b^2/v), with positive sine weights.")),
                    Paragraph(Text(
                        "The frozen sine recurrence (w_(m-1)+w_(m+1))/2 = cos(theta) w_m "
                        + "turns the local prefactor into cos(theta) w_m / 2. The two shifted "
                        + "sums are then re-indexed by bijections between their nonzero "
                        + "summands. Thus unmatched endpoint terms vanish through the zero "
                        + "extension instead of requiring separate endpoint calculations. "
                        + "The recurrence reduces the re-indexed double sum to 2 cos(theta) "
                        + "times the squared norm, and the bound collapses to cos(theta)^2 "
                        + "times that norm."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-cosine-squared-value-is-the-greatest-unit-quadratic-value"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumBounds/ReferenceFrameTaxOptimal.reference_frame_tax_isGreatest"),
                H("The cosine-squared value is the greatest unit quadratic value"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Forall, F.Sp, F.Id("N"), F.Sp, F.InMacro, F.Sp,
                        F.Mathbb, F.Grp(F.Id("N")), F.Comma, F.Esc,
                    F.D(1), F.Leq, F.Sp, F.Id("N"), F.Sp, F.Rightarrow, F.Sp,
                    F.Operatorname, F.Grp(F.Id("IsGreatest")), F.Open,
                        F.Left, F.OpenBrace,
                            F.Id("q"), F.Sp, F.InMacro, F.Sp,
                                F.Mathbb, F.Grp(F.Id("R")), F.Sp, F.Mid, F.Sp,
                            F.Exists, F.Sp, F.Id("c"), F.Colon,
                                F.Operatorname, F.Grp(F.Id("Fin")),
                                F.Open, F.Id("N"), F.Close,
                                F.To, F.Sp, F.Mathbb, F.Grp(F.Id("R")),
                                F.Comma, F.Esc,
                            F.Open,
                                F.Sum, F.Underscore, F.Grp(F.Id("i"), F.Sp,
                                    F.InMacro, F.Sp,
                                    F.Operatorname, F.Grp(F.Id("Fin")),
                                    F.Open, F.Id("N"), F.Close), F.Sp,
                                F.Id("c"), F.Underscore, F.Grp(F.Id("i")),
                                    F.Caret, F.Grp(F.D(2)),
                                F.Eq, F.D(1),
                            F.Close, F.Sp, F.Land, F.Sp,
                            F.Id("Q"), F.Underscore, F.Grp(F.Id("N")),
                                F.Open, F.Id("c"), F.Close,
                            F.Eq, F.Id("q"),
                        F.Right, F.CloseBrace,
                        F.Comma, F.Esc,
                        F.Operatorname, F.Grp(F.Id("cos")), F.Open,
                            F.Frac, F.Grp(F.Pi),
                                F.Grp(F.Id("N"), F.Plus, F.D(1)),
                        F.Close, F.Caret, F.Grp(F.D(2)),
                    F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For 1 <= N, cos(pi/(N+1))^2 belongs to the set of quadratic values "
                        + "attained by unit real vectors and bounds every member of that set "
                        + "from above. The predecessor module proved that the normalized sine "
                        + "reference attains this value but explicitly did not prove that no "
                        + "unit vector exceeds it. Specializing the scale-free upper bound to "
                        + "unit vectors supplies exactly that missing half. This IsGreatest "
                        + "theorem therefore closes the gap named in the previous document."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("the-optimal-tax-is-the-sine-squared-value"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumBounds/ReferenceFrameTaxOptimal.reference_frame_tax_optimal_identity"),
                H("The optimal tax is the sine-squared value"),
                StatementSource.FromAuthor(F.Disp(F.Seq(
                    F.Forall, F.Sp, F.Id("N"), F.Sp, F.InMacro, F.Sp,
                        F.Mathbb, F.Grp(F.Id("N")), F.Comma, F.Esc,
                    F.D(1), F.Leq, F.Sp, F.Id("N"), F.Sp, F.Rightarrow, F.Sp,
                    F.D(1), F.Minus,
                    F.Operatorname, F.Grp(F.Id("cos")), F.Open,
                        F.Frac, F.Grp(F.Pi),
                            F.Grp(F.Id("N"), F.Plus, F.D(1)),
                    F.Close, F.Caret, F.Grp(F.D(2)),
                    F.Eq,
                    F.Sin, F.Open,
                        F.Frac, F.Grp(F.Pi),
                            F.Grp(F.Id("N"), F.Plus, F.D(1)),
                    F.Close, F.Caret, F.Grp(F.D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For 1 <= N, one minus the greatest quadratic value is "
                        + "sin(pi/(N+1))^2. Combined with the IsGreatest theorem, this is the "
                        + "source's stated identity 1 - F_e^opt = sin(pi/(N+1))^2 for the "
                        + "reduced finite real quadratic-form problem.")),
                    Paragraph(Text(
                        "As in the predecessor, no physical reduction is claimed. This module "
                        + "does not model or prove a passage from an excitation-exchange "
                        + "unitary and a conservation-ladder reference to the finite real "
                        + "quadratic form; its optimality conclusion begins only after that "
                        + "form has been specified."))),
                DescribeRole.Theorem
            ))));
}
