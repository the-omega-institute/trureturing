using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.SequentialDecisionRisk;

internal sealed class NonintegerForwardDifferenceSignalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/SequentialDecisionRisk/NonintegerForwardDifferenceSignal.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite differences detect a noninteger power.",
        H("Finite differences detect a noninteger power"),
        Blocks(
            Paragraph(Text("For real functions write Delta_t^R f(x) for R iterations of u -> f(u+t)-f(u), evaluated at x, and D^R f for the iterated real derivative. The mean-value and real-power derivative formulas are classical finite-difference tools. Their square-root-scale application isolates the nonaffine part of the target.")),
            Describe.Lean(
                DescribeId.Create("nonintegerforwarddifferencesignal-has-deriv-at-fwd-diff-iter"),
                DeclarationHandle.Create(Prefix + "has_deriv_at_fwd_diff_iter"),
                H("Differentiate at all finite-difference nodes"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/nist2010interpolation")),
                Blocks(Paragraph(Text("For every real t,x, natural n and real functions f,fprime, if HasDerivAt f (fprime(x+i t)) (x+i t) for every natural i<=n, then HasDerivAt (Delta_t^n f) (Delta_t^n fprime(x)) x. Neither positivity of t nor differentiability away from the finitely many nodes is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonintegerforwarddifferencesignal-exists-fwd-diff-iter-eq-iterated-deriv"),
                DeclarationHandle.Create(Prefix + "exists_fwd_diff_iter_eq_iterated_deriv"),
                H("The derivative is evaluated inside the original interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/nist2010interpolation")),
                Blocks(Paragraph(Text("For every real f, natural R, real x and t>0, assume D^k f is differentiable at every y in [x,x+Rt] for every natural k<R. There exists y in this same closed interval such that Delta_t^R f(x)=t^R D^R f(y). The statement includes R=0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonintegerforwarddifferencesignal-abs-fwd-diff-iter-le"),
                DeclarationHandle.Create(Prefix + "abs_fwd_diff_iter_le"),
                H("A derivative budget controls the difference"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/nist2010interpolation")),
                Blocks(Paragraph(Text("For every real f, natural R, real x,D and t>0, under the preceding differentiability hypothesis and |D^R f(y)|<=D for every y in [x,x+Rt], |Delta_t^R f(x)|<=t^R D. D is an arbitrary real bound; the hypotheses supply any necessary nonnegativity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonintegerforwarddifferencesignal-iterated-deriv-rpow-pos"),
                DeclarationHandle.Create(Prefix + "iterated_deriv_rpow_pos"),
                H("Real powers on the positive half-line"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/roos2026positivepower")),
                Blocks(Paragraph(Text("For every real p and natural n, D^n(u -> u^p) agrees on (0,infinity) with u -> [product_{i<n}(p-i)] u^(p-n). This positive-half-line formula is ported from the pinned Apache-licensed LeanSpherical source identified in the literature note."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonintegerforwarddifferencesignal-rpow-fwd-diff-iter-ne-zero"),
                DeclarationHandle.Create(Prefix + "rpow_fwd_diff_iter_ne_zero"),
                H("No difference order annihilates a nonintegral power"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/nist2010interpolation")),
                Blocks(Paragraph(Text("For every real beta, natural R, and real x,t>0, if beta differs from every natural number, Delta_t^R(u -> u^beta)(x) is nonzero. No assumption beta>0 is imposed. The derivative product has no zero factor on the positive interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonintegerforwarddifferencesignal-unit-signal-pos"),
                DeclarationHandle.Create(Prefix + "unit_signal_pos"),
                H("The unit-step signal is strictly positive"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/nist2010interpolation")),
                Blocks(Paragraph(Text("For every real beta differing from every natural number and every natural R, |Delta_1^R(u -> u^beta)(1)|>0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonintegerforwarddifferencesignal-rpow-fwd-diff-iter-scale"),
                DeclarationHandle.Create(Prefix + "rpow_fwd_diff_iter_scale"),
                H("Homogeneity of the power difference"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/nist2010interpolation")),
                Blocks(Paragraph(Text("For every real beta, natural R and real t>0, Delta_t^R(u -> u^beta)(t)=t^beta Delta_1^R(u -> u^beta)(1)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonintegerforwarddifferencesignal-affine-fwd-diff-iter-eq-zero"),
                DeclarationHandle.Create(Prefix + "affine_fwd_diff_iter_eq_zero"),
                H("Orders at least two kill affine functions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/nist2010interpolation")),
                Blocks(Paragraph(Text("For all real a,b,t and natural R>=2, Delta_t^R(u -> a+b u) is the zero function, as an equality of functions. No sign assumption on t is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonintegerforwarddifferencesignal-affine-power-fwd-diff-iter"),
                DeclarationHandle.Create(Prefix + "affine_power_fwd_diff_iter"),
                H("The affine part disappears exactly"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Estimation/nist2010interpolation")),
                Blocks(Paragraph(Text("For all real a,b,c,beta, natural R>=2 and real t>0, Delta_t^R(u -> a+b u-c u^beta)(t)=-c t^beta Delta_1^R(u -> u^beta)(1)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonintegerforwarddifferencesignal-target-signal-scaled"),
                DeclarationHandle.Create(Prefix + "target_signal_scaled"),
                H("The exact square-root-scale target signal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Estimation/nist2010interpolation")),
                Blocks(Paragraph(Text("For all real B,C,beta,rho, natural R>=2, rho>0 and beta differing from every natural number, S=rho^beta |Delta_1^R(u -> u^beta)(1)|/16 is strictly positive. For every real n>0, |Delta_{rho/sqrt(n)}^R(u -> (1-u/C)/(2B)-u^beta/16)(rho/sqrt(n))|=S n^(-beta/2). There are no sign or nonzero hypotheses on B or C: real division is the totalized Lean operation, and the corresponding term is affine for all their values."))),
                DescribeRole.Theorem))));
}
