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
                DescribeRole.Definition),
            Paragraph(Text("Faithful symmetric weights. Let a and b be arbitrary finite complex matrix carriers, "
                + "Phi an actual completely positive trace-preserving channel, sigma a strictly positive density "
                + "matrix, and tau=Phi(sigma) strictly positive. All matrix powers below are the real continuous "
                + "functional calculus, so their eigenvalues are the corresponding scalar powers. The norm is "
                + "the Frobenius, or Hilbert-Schmidt, norm, and star denotes conjugate transpose. Let T(X) "
                + "denote the sandwiched channel map in the display. The following consequence uses the original model "
                + "at rho=sigma and the original matrix Jensen results.")),
            Paragraph(Math(WeightedContraction())),
            Paragraph(Text("Write Psi for the actual Kraus trace adjoint in supported_relative_modular_model "
                + "Phi sigma sigma. In its spectral coordinates put A=diag(sigma_j/sigma_i), "
                + "B=diag(tau_l/tau_k), and retain its actual matrix V. The model supplies V*V<=I, "
                + "V*AV<=B, the coordinate action of V, and exact trace pairing with Phi. Operator convexity "
                + "of minus square root gives V*sqrt(A)V<=sqrt(V*AV)<=sqrt(B). For the first inequality, "
                + "the original isometry_jensen applies to W formed by stacking V and sqrt(I-V*V), "
                + "and to diag(A,0); W*W=I. The original cfc_intertwining identifies the block square root. "
                + "The second inequality is square-root monotonicity.")),
            Paragraph(Text("For every complex matrix Y, choose x_(l,k)=sqrt(tau_k)<w_l,Yw_k>. "
                + "Faithfulness makes all spectral indices positive and the original spectral resolution "
                + "of the identity reconstructs Y=spectralX(x). The original coordinateAction then gives "
                + "(Vx)_(j,i)=sqrt(sigma_i)<v_j,Psi(Y)v_i>. The original full_spectral_parseval, "
                + "cfc_mulVec_basis and basis_pair_cfc identify its sqrt(A) quadratic form with "
                + "||sigma^(1/4) Psi(Y) sigma^(1/4)||_HS^2. The sqrt(B) quadratic form is exactly "
                + "||tau^(1/4) Y tau^(1/4)||_HS^2. Here the weights are sqrt(sigma_j sigma_i), "
                + "rather than a one-sided inverse-reference weight.")),
            Paragraph(Text("Define S(Y)=sigma^(1/4) Psi(tau^(-1/4) Y tau^(-1/4)) sigma^(1/4). "
                + "The preceding inequality and cancellation of faithful quarter powers give ||S(Y)||_HS<=||Y||_HS. "
                + "The actual tracePair and adjointStar fields give Tr(Y* T(X))=Tr(S(Y)* X). "
                + "Taking Y=T(X), the original traceNorm_eq_max_re_tr_U and traceNorm_mul_le_hsSq "
                + "bound ||T(X)||_HS^2 by ||S(T(X))||_HS ||X||_HS, hence by ||T(X)||_HS ||X||_HS. "
                + "This proves the displayed bound, with the zero output handled without division. "
                + "No self-adjointness, invertibility or nonzero condition is imposed on X; singular and "
                + "zero inputs are included. No common eigenbasis for the reference, X or the channel "
                + "coefficients is assumed. This consequence asserts neither recovery nor equality characterization.")))));

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Power(Formula value, bool inverse = false) => new Formula.Power(value,
        inverse ? new Formula.Negate(new Formula.Fraction(Num(1), Num(4)))
            : new Formula.Fraction(Num(1), Num(4)));
    private static Formula WeightedContraction()
    {
        Formula a = Id("a"), b = Id("b"), phi = Id("Phi"), sigma = Id("sigma"), x = Id("X");
        Formula tau = new Formula.Apply(phi, [sigma]);
        Formula sx = Multiply(Multiply(Power(sigma), x), Power(sigma));
        Formula tx = Multiply(Multiply(Power(tau, true), new Formula.Apply(phi, [sx])), Power(tau, true));
        Formula bound = new Formula.Relation(new Formula.Norm(tx),
            FormulaRelationOperator.LessThanOrEqual, new Formula.Norm(x));
        Formula faithful = new Formula.Logic(Call("PosDef", sigma), FormulaLogicOperator.And,
            Call("PosDef", tau));
        return FormulaDsl.Disp(All("a", Call("FiniteTypes"), All("b", Call("FiniteTypes"),
            All("Phi", Call("QuantumChannel", a, b), All("sigma", Call("DensityState", a),
                new Formula.Logic(faithful, FormulaLogicOperator.Implies,
                    All("X", Call("Matrix", a, a, Id("Complex")), bound)))))));
    }
}
