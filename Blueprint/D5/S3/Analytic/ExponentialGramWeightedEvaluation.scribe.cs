using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class ExponentialGramWeightedEvaluationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The squared norm of evaluation at zero on a finite span of distinct exponential modes has sharp constant h times the number of modes for the energy with weight exp(-hs).",
        H("Sharp weighted evaluation of finite exponential sums"),
        Blocks(Describe.Lean(
            DescribeId.Create("exponential-gram-weighted-evaluation-least-constant"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/ExponentialGramWeightedEvaluation.weighted_evaluation_least_constant"),
            H("The least weighted evaluation constant"),
            StatementSource.FromAuthor(Disp(
                Call("IsLeast", F.Id("A"), Seq(F.Id("h"), Sp, Call("card", F.Id("iota")))))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let iota be a nonempty finite index type, let the real frequencies omega(i) be distinct, and let h be positive. For complex coefficients a, set f_a(s) to the sum of a(i) exp(i omega(i) s). The set A consists of the real constants C for which the squared norm of f_a(0) is at most C times the integral of exp(-hs) times the squared norm of f_a(s) over [0, infinity), for every a. The displayed value belongs to A and is at most every member of A.")),
                Paragraph(Text(
                    "Mathlib's complex Laplace integral identifies the energy with the Gram quadratic form. Zero energy forces the exponential sum to vanish on the positive real axis. Mathlib's analytic uniqueness theorem extends this vanishing to the complex plane. ExponentialBlockIndependence.block_evaluation_injective then forces every coefficient to vanish by taking the exponents i omega(i) and the constant polynomial blocks a(i). For the positive definite Gram matrix G and diagonal differentiation matrix D, the matrix identity hG minus the all-ones outer product equals GD plus the adjoint of D times G. Multiplication by the inverse of G and cyclicity of trace give the inverse Gram readout h times card(iota). DetectorSensorDickeOptimality.psd_cauchy_schwarz gives the bound, and applying the inverse Gram matrix to the all-ones vector attains it with positive energy."))),
            DescribeRole.Theorem))));
}
