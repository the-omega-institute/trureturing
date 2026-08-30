using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.GoldenEuler;

internal sealed class LocalEulerTailVanishingDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeForms/GoldenEuler/LocalEulerTailVanishing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "Finite local Euler factors carry an exact geometric residual that vanishes inside the unit disk.",
            H("Local Euler Tail Vanishing"),
            Blocks(
                Theorem(
                    "finite-local-euler-factor-has-an-exact-tail",
                    "local_euler_partial_residual",
                    "Finite Local Euler Factor Has an Exact Tail",
                    "Multiplication by one minus the local variable leaves exactly one minus the omitted power."),
                Theorem(
                    "the-local-euler-residual-vanishes-in-the-unit-disk",
                    "local_euler_residual_tendsto_zero",
                    "The Local Euler Residual Vanishes in the Unit Disk",
                    "A strict norm bound below one forces the geometric tail to converge to zero."),
                Theorem(
                    "the-normalized-local-factor-converges-to-one",
                    "normalized_local_euler_partial_tendsto_one",
                    "The Normalized Local Factor Converges to One",
                    "The exact residual identity and geometric decay make the normalized truncation converge to one."),
                Theorem(
                    "the-local-euler-truncation-converges-to-the-inverse-denominator",
                    "local_euler_partial_tendsto_inv",
                    "The Local Euler Truncation Converges to the Inverse Denominator",
                    "Inside the unit disk, finite geometric Euler factors converge to the usual inverse local denominator."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        string title,
        string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(paragraph)),
                Paragraph(Text(
                    "This is a one-place completion theorem. It does not justify exchanging a "
                        + "limit with an infinite product over primes."))),
            DescribeRole.Theorem);
}
