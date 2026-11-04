using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class InfiniteGaussianSewingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianSewing.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "InfiniteGaussianSewing", H("InfiniteGaussianSewing"), Blocks(
            Paragraph(Text("Finite Gaussian sewing extends to arbitrary internal mode types by absolute convergence and a common finite-subset limit. The effective kernel retains the ordered inverses of BA and AB and the trace-log normalization of AB.")),
            N("coefficient_finite_inclusion","Exact finite coefficient stabilization","Any finite injective set of coordinates computes the same actual coefficient as its zero extension. The proof uses the existing coefficient_on_block and gaussianCoefficient_enlarge theorems on the actual finite image, including all repeated occupations."),
            N("cutoff_sewing","Finite sewing on coordinate supports","Reindex every occupation supported in F through the actual restriction and extension equivalence. Apply FiniteGaussianSewing.finite_sewing to the exact principal blocks and mixed coordinate restrictions. The scalar is identified with the true traceLog(cutoffProduct A B F) by the positive-power trace identity."),
            N("cutoffKernel_tendsto","The three effective block limits","Let N=(1-BA)^-1 and V=(1-AB)^-1. The diagonal effective entries tend to P+R N B R^t and Q+S^t V A S. The finite mixed entry is R N_F S-R(1-P_F)S, and therefore tends to R N S. Matrix transpose algebra identifies the opposite mixed block with its bilinear coordinate transpose. The argument uses the same finite-subset net as the actual occupation cutoffs."),
            N("sewing","Complete infinite external Gaussian sewing","For arbitrary internal index I, finite X,Y, transpose-symmetric Hilbert-Schmidt strict contractions A,B, arbitrary finite symmetric P,Q and arbitrary finite families of l2 mixed rows R_x and columns S_y, the actual coefficient contraction is absolutely summable for every d,e and equals exp(traceLog(AB)) times the ordinary Gaussian coefficient of the ordered effective kernel. The first source kernel is [[P,R],[R^t,A]] on X+I and the second is [[B,S],[S^t,Q]] on I+Y. The proof applies the actual finite identity at every F, proves both genuine limits and uses uniqueness. The trace-log is the positive-power series of the original trace-class product AB, not a cutoff-defined trace. Empty I gives c_P(d)c_Q(e) with normalization one, rather than generally one. This is classical Gaussian/Fock sewing, not a claim of a completed VOA, string theory or AdS/CFT construction.")), []));

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("infinitegaussiansewing-" + name.Replace(".", "-").Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
