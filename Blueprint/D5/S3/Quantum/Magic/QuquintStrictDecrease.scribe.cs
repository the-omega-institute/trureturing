using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class QuquintStrictDecreaseDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Magic/QuquintStrictDecrease.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact normalized variation and strict mana decrease on the constrained tangent family.",
        H("Ququint Strict Directional Decrease"),
        Blocks(
            Claim("normalizedPerturbation", "Normalized perturbation",
                Seq(BindDirection, BindParameter, Perturbed, Eq,
                    Norm(Unnormalized), Caret, Grp(Seq(Minus, D(1))), Cdot, Parenthesized(Seq( Unnormalized))),
                "The inverse norm is real scalar multiplication on the complex Euclidean state space.",
                DescribeRole.Definition),
            Claim("perturbation_norm_sq", "The normalization denominator",
                Seq(BindDirection, BindParameter, Norm(Unnormalized), Caret, Grp(D(2)), Eq, Denominator),
                "The orthogonality field of tangent removes the cross term. The exact norm of psi is one; "
                    + "the denominator is positive for every real parameter."),
            Claim("normalized_wigner", "Every normalized Wigner entry",
                Seq(BindDirection, BindParameter,
                    Forall, Sp, Q, Sp, P, Colon, Name("Fin"), Sp, D(5), Comma,
                    Wigner(Perturbed), Eq, Frac,
                    Grp(Seq(Wigner(Geo("psi")), Plus, E, Cdot, Coefficient,
                        Plus, E, Caret, Grp(D(2)), Cdot, Wigner(StateValue))), Grp(Denominator)),
                "wigner_expand supplies the exact quadratic numerator. Real homogeneity and "
                    + "perturbation_norm_sq supply the denominator."),
            Claim("exact_change", "The exact local change",
                Seq(BindDirection, Call(Seq(Name("Filter"), Dot, Name("Eventually")),
                    Seq(Parenthesized(Seq( Parenthesized(Seq( E, Colon, RealType)), Mapsto, ExactChange))),
                    Call(Name("nhds"), Seq(Parenthesized(Seq( D(0), Colon, RealType)))))),
                "Continuity keeps the sign fixed at each nonzero Wigner entry near zero. "
                    + "At zeroPoints the tangent constraint leaves a squared parameter times the absolute "
                    + "quadratic coefficient. first_coefficient_zero consumes gradient_psi to cancel the "
                    + "summed linear term. The remaining coefficient is exactly secondVariation."),
            Claim("directional_decrease", "Strict decrease of the norm sum and mana",
                Seq(BindDirection, V, Neq, D(0), Implies,
                    Exists, Sp, F.Id("delta"), Colon, RealType, Comma,
                    D(0), Lt, F.Id("delta"), Sp, Land, Sp,
                    Parenthesized(Seq(BindParameter,
                    D(0), Lt, Call(Name("abs"), E), Implies,
                    Call(Name("abs"), E), Lt, F.Id("delta"), Implies,
                    Parenthesized(Seq(ExactChange, Sp, Land, Sp,
                    LOne(Perturbed), Lt, LOne(Geo("psi")), Sp, Land, Sp,
                    Log(LOne(Perturbed)), Lt, Log(LOne(Geo("psi")))))))),
                "second_variation_negative consumes negativity_iff, the finite sign maximum identity, "
                    + "and all thirty-two LDL certificates. A nonzero real parameter has positive square. "
                    + "Positivity near zero allows Real.log_lt_log to give strict mana decrease."),
            Paragraph(Text("This result concerns only the specified dimension-five state and nonzero "
                + "directions in tangent. It does not classify other directions, dimensions or critical "
                + "points, solve general mana extremisation, identify Claim C as an author-verbatim "
                + "conjecture, or assert global novelty beyond the recorded search.")))));

    private static DocumentBlock Claim(string name, string title, Formula formula, string explanation,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("ququint-decrease-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Module + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/erewgoldstein2025magic")),
        Blocks(Paragraph(Text(explanation))), role);

    private static Formula ExactChange => Seq(LOne(Perturbed), Minus, LOne(Geo("psi")), Eq,
        Frac, Grp(Seq(E, Caret, Grp(D(2)), Cdot,
            Call(Qualified("QuquintFiniteMaximum", "secondVariation"), StateValue))), Grp(Denominator));
    private static Formula Denominator => Seq(D(1), Plus, E, Caret, Grp(D(2)), Cdot,
        Norm(StateValue), Caret, Grp(D(2)));
    private static Formula Coefficient => Seq(Parenthesized(Seq( D(2), Cdot,
        Call(Seq(Name("Complex"), Dot, Name("re")),
            Call(Name("dotProduct"), Call(Name("star"), Call(Seq(Name("WithLp"), Dot, Name("ofLp")), Geo("psi"))),
                Call(Seq(Name("Matrix"), Dot, Name("mulVec")), Call(Geo("phasePoint"), Q, P),
                    Call(Seq(Name("WithLp"), Dot, Name("ofLp")), StateValue)))), Slash, D(5))));
    private static Formula BindDirection => Seq(Forall, Sp, V, Colon, Geo("tangent"), Comma);
    private static Formula BindParameter => Seq(Forall, Sp, E, Colon, RealType, Comma);
    private static Formula StateValue => Seq(Parenthesized(Seq( V, Colon, Geo("State"))));
    private static Formula Unnormalized => Seq(Geo("psi"), Plus, E, Cdot, StateValue);
    private static Formula Perturbed => Call(Name("normalizedPerturbation"), V, E);
    private static Formula Wigner(Formula v) => Call(Geo("wigner"), v, Q, P);
    private static Formula LOne(Formula v) => Call(Geo("lOne"), v);
    private static Formula Norm(Formula v) => Call(Seq(Name("Norm"), Dot, Name("norm")), v);
    private static Formula Log(Formula v) => Call(Seq(Name("Real"), Dot, Name("log")), v);
    private static Formula RealType => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula V => F.Id("v");
    private static Formula E => F.Id("e");
    private static Formula Q => F.Id("q");
    private static Formula P => F.Id("p");
    private static Formula Geo(string name) => Qualified("QuquintWignerCriticalGeometry", name);
    private static Formula Qualified(string module, string name) => Seq(Name("D5"), Dot,
        Name("S3"), Dot, Name("Quantum"), Dot, Name("Magic"), Dot, Name(module), Dot, Name(name));
    private static Formula Call(Formula f, params Formula[] args) => Seq(f, Parenthesized(Seq(
        Seq(args.SelectMany((arg, i) => i == 0 ? new[] { arg } : new[] { Comma, arg }).ToArray()))));
    private static Formula Name(string name) => Seq(Mathrm, Grp(F.Id(name)));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
