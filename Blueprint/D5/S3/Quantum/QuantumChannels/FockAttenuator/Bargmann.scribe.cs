using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;

internal sealed class BargmannDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/FockAttenuator/Bargmann.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The completed occupation space has an injective entire Bargmann transform with Gaussian control on every bounded disk.",
        H("Bargmann analysis on the completed Fock space"),
        Blocks(
            Result("transform", "transform", "The completed transform",
                "H is lp over the natural numbers with complex coordinates and exponent two. "
                + "The transform of a at z is the inner product of the exponential vector at conjugate z with a. "
                + "The inner product is conjugate linear in its first argument. No finite support or energy assumption is imposed.",
                Call("Bargmann", F.Id("a"), F.Id("z")), DescribeRole.Definition),
            Result("series", "has_fpower_series", "An entire factorial series",
                "For every a in H, the full formal multilinear power series at zero has infinite radius and sums to the transform. "
                + "Its coefficient of degree n is a(n) divided by sqrt(n!). This is a theorem about the actual completed vector.",
                Call("HasEntireFactorialSeries", F.Id("a"))),
            Result("entire", "entire", "Entire evaluation",
                "The transform of every completed vector is complex differentiable at every complex point. "
                + "An arbitrary entire function is not thereby assigned a vector in H.",
                Call("Differentiable", F.Id("Bargmann"), F.Id("a"))),
            Result("radial-bound", "tsum_radial_le", "Absolute radial control",
                "For every nonnegative real radius R, the sum over all n of norm(a(n))*R^n/sqrt(n!) is at most "
                + "norm(a)*exp(R^2/2). The proof applies lp Holder to the actual exponential vector, whose squared norm is exp(R^2). "
                + "The sum includes all coordinates, including at R=0.",
                Call("GaussianAbsoluteRadialBound", F.Id("a"), F.Id("R"))),
            Result("injective", "injective", "Recovery of every coordinate",
                "Equality of two transforms as functions on the whole complex plane implies equality of their original H vectors. "
                + "Uniqueness of the convergent power series recovers each factorial-normalized coordinate.",
                Call("Injective", F.Id("Bargmann"))),
            Result("uniform", "uniform_of_tendsto", "Hilbert limits give local uniform limits",
                "For every index type, every filter, every net u converging to a in the H norm, and every nonnegative radius R, "
                + "the transforms of u converge uniformly to the transform of a on the closed disk of radius R. "
                + "The Gaussian difference bound supplies one estimate for all points of that disk.",
                Call("LocallyUniformOfHilbertConvergence", F.Id("u"), F.Id("a"))),
            Result("total", "exponential_dense_span", "Totalness in the completion",
                "The topological closure of the complex span of all actual exponential vectors is all of H. "
                + "A vector in its orthogonal complement has zero transform and therefore every coordinate zero. "
                + "This supplies the density used in the later coefficient-operator reconstruction; no assertion about entropy is made here.",
                Call("DenseExponentialSpan", F.Id("H"))))));

    private static DocumentBlock Result(string id, string declaration, string title,
        string prose, Formula formula, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("fock-bargmann-" + id),
            DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
