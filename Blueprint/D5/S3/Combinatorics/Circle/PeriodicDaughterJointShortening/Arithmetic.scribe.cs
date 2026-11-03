using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.PeriodicDaughterJointShortening;

internal sealed class ArithmeticDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Circle/PeriodicDaughterJointShortening/Arithmetic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer charge identities for the periodic daughter transport",
        H("Arithmetic for the periodic daughter construction"),
        Blocks(
            Paragraph(Text(
                "This helper module gives the integer arithmetic used by the existing "
                    + "PeriodicDaughterJointShortening.Construction proof. The definitions "
                    + "name the old length, repeated seed, geometric scale factors and native "
                    + "digit phases; the theorems below are the exact source, centered-value and "
                    + "cross-modulus identities consumed by regular_block, top_block and "
                    + "daughter_order.")),
            Node("length", "The shortened physical length",
                "length d r is (d+1)*r-1, the old physical modulus length after one globally fresh daughter label is removed.", DescribeRole.Definition),
            Node("seed", "The repeated seed",
                "seed d w r is w multiplied by geom (d+1) r; Construction uses it as the old source and twice this value as the daughter source.", DescribeRole.Definition),
            Node("q", "The daughter row base",
                "q d is the integer power 2^(d+1).", DescribeRole.Definition),
            Node("n", "The old modulus parameter",
                "n d is the integer 2^d-1, the old two-run modulus.", DescribeRole.Definition),
            Node("H", "The lower geometric scale",
                "H d r is geom (d+1) (r-1), the scale of the complete lower old blocks.", DescribeRole.Definition),
            Node("R", "The top geometric scale",
                "R d r is q d raised to r-1, the scale of the shortened top block.", DescribeRole.Definition),
            Node("G", "The daughter geometric scale",
                "G d r is geom (d+1) r, the scale of each complete daughter block.", DescribeRole.Definition),
            Node("N", "The old actual modulus",
                "N d r is modulus (length d r), the actual integer modulus used by the old source.", DescribeRole.Definition),
            Node("ScaleFacts", "The scalar arithmetic package",
                "ScaleFacts d w r records the exact length, geometric, positivity, half-modulus, modulus, margin and daughter-capacity identities needed for the construction. Its fields include length_succ, q_eq, q_ge, H_ge, R_ge, G_ge, w_nonneg, w_bound, G_eq, modulus_eq, top_power, top_modulus, old_half, base_half, daughter_half, new_modulus, regular_margin, top_margin and daughter_margin.", DescribeRole.Definition),
            Node("scale_facts", "All scalar identities at the actual modulus",
                "For 2≤d, w≤2^(d-1)-1 and 2≤r, scale_facts constructs ScaleFacts d w r. Construction uses this package in every regular, top and daughter block estimate.", DescribeRole.Theorem),
            Node("alpha", "The extended old phase",
                "alpha d w i is the native actualSource d w digit at i when i<d and is w at the distinct final local-ear phase.", DescribeRole.Definition),
            Node("e", "The extended native charge",
                "e d w i is charge d w at old digits and w at the final local-ear phase.", DescribeRole.Definition),
            Node("beta", "The daughter phase",
                "beta d w is actualSource (d+1) (2*w), the actual daughter phase function.", DescribeRole.Definition),
            Node("phase_data", "Phase and charge identities",
                "For 2≤d, w≤2^(d-1)-1 and every i: e is nonnegative; alpha equals 2^i*w-n*e; beta equals 2*alpha-e; beta also equals 2^(i+1)*w-(q-1)*e; and beta lies between -n and n. Construction uses these bounds for all prefix and centered estimates.", DescribeRole.Theorem),
            Node("phase_fresh", "The fresh phase value",
                "Under the old dimension and width bounds, beta d w (Fin.last d)=w.", DescribeRole.Theorem),
            Node("phase_cast", "The old phase cast",
                "For every old digit i, beta d w i.castSucc = 2*actualSource d w i-charge d w i.", DescribeRole.Theorem),
            Node("phase_charge_sum", "The extended charge sum",
                "Under the old dimension and width bounds, the sum of e over Fin (d+1) is 2*w.", DescribeRole.Theorem),
            Node("defect", "The nonnegative cross-modulus defect",
                "defect d w j i is 2^(i+1)*w*geom (d+1) j+e d w i; it carries the integer discrepancy of a regular repeated block without division or parity choices.", DescribeRole.Definition),
            Node("regularValue", "The regular block value",
                "regularValue d w r j i is 2^d*H*beta plus alpha plus 2^i*w*geom (d+1) j, with all factors at d,w,r.", DescribeRole.Definition),
            Node("topValue", "The top block value",
                "topValue d w r i is R*actualSource d w i+H*beta d w i.castSucc.", DescribeRole.Definition),
            Node("defect_data", "Defect positivity and total",
                "For every phase i, defect is nonnegative, and its sum over Fin (d+1) is 2*w*q^j. Construction uses this exact total in regular_block.", DescribeRole.Theorem),
            Node("regular_double", "The regular doubled-value identity",
                "For every regular block index j and phase i, 2*regularValue d w r j i = G*beta d w i+defect d w j i. Construction uses it to transfer the daughter prefix bounds to each old block.", DescribeRole.Theorem),
            Node("regular_source", "The actual regular source value",
                "For j<r-1 and a valid physical label j*(d+1)+i.val below length d r, actualSource (length d r) (seed d w r) at that label equals regularValue d w r j i. Construction uses this live equality in regular_block.", DescribeRole.Theorem),
            Node("top_source", "The actual top source value",
                "For a valid top label (r-1)*(d+1)+i.val below length d r, actualSource at the repeated seed equals topValue d w r i. Construction uses this live equality in top_block.", DescribeRole.Theorem),
            Node("daughter_source", "The actual periodic daughter source",
                "For every daughter block j and phase i at a valid label below length d r+1, actualSource (length d r+1) (2*seed d w r) equals G*daughter phase beta d w i. Construction uses this live equality in daughter_order.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("periodic-daughter-arithmetic-" + CanonicalId(name)),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static string CanonicalId(string name) => name switch
    {
        "n" => "old-modulus-parameter",
        "N" => "actual-modulus",
        "H" => "lower-geometric-scale",
        "R" => "top-geometric-scale",
        "G" => "daughter-geometric-scale",
        _ => name.ToLowerInvariant().Replace('_', '-')
    };
}
