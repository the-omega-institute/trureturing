using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class CanonicalRelativeModularModelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual supported modular coordinates are shared by the original DPI and fixed Petz equality.",
        H("Actual relative modular model"), Blocks(
            Describe.Lean(
                DescribeId.Create("diagonal-quadratic-form"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/CanonicalRelativeModularModel.diagonal_quadratic_form"),
                H("The real quadratic form of a real diagonal matrix"),
                StatementSource.FromAuthor(FormulaDsl.Disp(
                    new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("n"),
                        FormulaDsl.Seq(Id("Type"), FormulaDsl.Sp, Id("u")),
                        FormulaDsl.Seq(
                            FormulaDsl.OpenBracket, Call("Fintype", Id("n")),
                            FormulaDsl.CloseBracket, FormulaDsl.Sp,
                            FormulaDsl.OpenBracket, Call("DecidableEq", Id("n")),
                            FormulaDsl.CloseBracket, FormulaDsl.Sp,
                            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("d"),
                                new Formula.TypeArrow(Id("n"),
                                    FormulaDsl.Seq(FormulaDsl.Mathbb, FormulaDsl.Grp(Id("R")))),
                                new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("y"),
                                    new Formula.TypeArrow(Id("n"),
                                        FormulaDsl.Seq(FormulaDsl.Mathbb, FormulaDsl.Grp(Id("C")))),
                                    Equal(
                                        FormulaDsl.Seq(FormulaDsl.Open,
                                            Call("dotProduct", Call("star", Id("y")),
                                                new Formula.Apply(
                                                    FormulaDsl.Seq(Id("Matrix"), FormulaDsl.Dot,
                                                        Id("mulVec")),
                                                    [new Formula.Apply(
                                                        FormulaDsl.Seq(Id("Matrix"), FormulaDsl.Dot,
                                                            Id("diagonal")),
                                                        [FormulaDsl.Seq(Id("fun"), FormulaDsl.Sp,
                                                            Id("i"), FormulaDsl.Sp, FormulaDsl.Mapsto,
                                                            FormulaDsl.Sp, FormulaDsl.Open,
                                                            new Formula.Apply(Id("d"), [Id("i")]), FormulaDsl.Colon,
                                                            FormulaDsl.Seq(FormulaDsl.Mathbb,
                                                                FormulaDsl.Grp(Id("C"))),
                                                            FormulaDsl.Close)]), Id("y")])),
                                            FormulaDsl.Close, FormulaDsl.Dot, Id("re")),
                                        FormulaDsl.Seq(FormulaDsl.Sum, FormulaDsl.Underscore,
                                            FormulaDsl.Grp(Id("i")), FormulaDsl.Sp,
                                            Multiply(new Formula.Apply(Id("d"), [Id("i")]),
                                                new Formula.Power(new Formula.Norm(new Formula.Apply(Id("y"), [Id("i")])),
                                                    Num(2))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every finite index type, real weights and complex vector, "
                        + "the real part of the diagonal quadratic form is the weighted sum of squared norms. "
                        + "The weights need not be nonnegative, and the index type may be empty.")),
                    Paragraph(Text("∀ {n : Type u} [Fintype n] [DecidableEq n] "
                        + "(d : n → ℝ) (y : n → ℂ), "
                        + "(star y ⬝ᵥ (Matrix.diagonal (fun i => (d i : ℂ)) *ᵥ y)).re "
                        + "= ∑ i, d i * ‖y i‖ ^ 2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("supported-relative-modular-model"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/CanonicalRelativeModularModel.supported_relative_modular_model"),
                H("Actual supported relative modular model"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the same actual Phi, rho and sigma with input support containment, this constructor "
                        + "returns their relative modular coordinates, output support, exact same fixed Kraus family, "
                        + "both Schwarz inequalities, trace pairing, norm saturation and exact canonical entropy "
                        + "readouts. These facts are proved by the original DPI construction. The original DPI "
                        + "consumes this model and retains its original statement; CanonicalPetzEquality consumes it "
                        + "to derive recovery. This struct does not assume entropy equality or recovery."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-kraus-representation"),
                DeclarationHandle.Create("D5/S3/Quantum/Divergence/CanonicalRelativeModularModel.actual_kraus_representation"),
                H("Choose Kraus coordinates once from the channel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This actual finite Kraus representation is chosen as a function only of Phi, before any "
                        + "density states. It carries both the Gram normalization and the full-matrix action. The "
                        + "construction was extracted once from the original DPI proof and is consumed by that DPI "
                        + "and the fixed-reference Petz theorem."))),
                DescribeRole.Definition))));
}
