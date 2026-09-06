using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.HilbertGeometry;

internal sealed class VectorPathDerivativeIntegrabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/HilbertGeometry/VectorPathDerivativeIntegrability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bochner integrability of the totalized derivative of a vector path.",
        H("Vector Path Derivative Integrability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bounded-variation-vector-derivative-integrability"),
                DeclarationHandle.Create(Prefix + "bounded_variation_interval_integrable_deriv"),
                H("Bounded variation gives an integrable derivative"),
                StatementSource.FromAuthor(IntegrabilityFormula(false)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every complete real normed vector space F, every path f and all real "
                    + "endpoints a,b, bounded variation on the unordered closed interval implies "
                    + "Bochner interval integrability of deriv f with respect to Lebesgue measure. "
                    + "The proof bounds derivative norms by the derivative of the scalar "
                    + "accumulated variation and applies the monotone integrability theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("absolutely-continuous-vector-derivative-integrability"),
                DeclarationHandle.Create(Prefix + "absolutely_continuous_interval_integrable_deriv"),
                H("Absolute continuity supplies derivative integrability"),
                StatementSource.FromAuthor(IntegrabilityFormula(true)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same conclusion follows directly from AbsolutelyContinuousOnInterval "
                    + "through its bounded-variation theorem. This prerequisite has no "
                    + "dimension, separability, smoothness, or assumed reconstruction condition. "
                    + "The derivative is totalized to zero at nondifferentiable points. "
                    + "Almost-everywhere differentiability in Hilbert space, integral reconstruction, "
                    + "and the minimum and unique affine minimizer of path energy remain "
                    + "separate obligations; neither theorem here asserts them."))),
                DescribeRole.Theorem))));

    private static Formula IntegrabilityFormula(bool absolutelyContinuous)
    {
        Formula space = F.Id("F");
        Formula real = F.Id("Real");
        Formula path = F.Id("f");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula hypothesis = absolutelyContinuous
            ? Call("AbsolutelyContinuousOnInterval", path, a, b)
            : Call("BoundedVariationOn", path, Call("uIcc", a, b));
        return Disp(Seq(
            Forall, Sp, space, Colon, Sp, F.Id("Type"), Comma, Sp,
            OpenBracket, Call("NormedAddCommGroup", space), CloseBracket, Comma, Sp,
            OpenBracket, Call("NormedSpace", real, space), CloseBracket, Comma, Sp,
            OpenBracket, Call("CompleteSpace", space), CloseBracket, Comma,
            RowBreak, Grp(),
            Forall, Sp, path, Colon, Sp, real, Sp, To, Sp, space, Comma, Sp,
            Forall, Sp, a, Comma, Sp, b, Colon, Sp, real, Comma, Sp,
            hypothesis, Sp, Implies, Sp,
            Call("IntervalIntegrable", Call("deriv", path), F.Id("volume"), a, b), Dot));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
