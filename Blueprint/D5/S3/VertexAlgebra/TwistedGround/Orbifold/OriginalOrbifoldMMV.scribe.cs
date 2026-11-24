using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Orbifold;

internal sealed class OriginalOrbifoldMMVDocument : IScribeDocumentDefinition
{
    private const string VertexAlgebra = "D5/S3/VertexAlgebra/";
    private const string Orbifold = VertexAlgebra + "TwistedGround/Orbifold/";
    private const string Jacobi = Orbifold + "OriginalOrbifoldJacobi.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Original Borcherds Identity with Two Twisted Sources and a Fixed Input",
        H("The Original Borcherds Identity with Two Twisted Sources and a Fixed Input"),
        Blocks(Describe.Lean(
            DescribeId.Create("defect-mmv"),
            DeclarationHandle.Create(Orbifold + "OriginalOrbifoldMMV.defect_mmv"),
            H("Vanishing of the MMV defect"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let D be rank-24 lattice data with unit Gram determinant and positive-definite "
                    + "real Gram form. For any two original negative twisted states u and v and any fixed "
                    + "state a, insert the three states into the original assembled carrier in the order "
                    + "(u, v, a). The Borcherds defect of the assembled field vanishes for every triple "
                    + "of integer indices (p, q, r).")),
                Paragraph(Text("The last-slot exchange uses lower truncation of the assembled modes, divided "
                    + "mode translation for u, and twisted-fixed skew for (v, a). The mode of u on v "
                    + "is fixed, so its iterate with a uses fixed-sector skew. The mode of u on a stays "
                    + "in the negative twisted sector, so the reverse iterate uses the skew law for "
                    + "originalI. Powers of assembled translation on the fixed inclusion are powers "
                    + "of fixed translation transported by that inclusion, which lifts both skew laws "
                    + "to the assembled carrier. See "),
                    Ref(Jacobi + "divided_mode_translation"), Text(", "),
                    Ref(Jacobi + "skew_mv"), Text(", "),
                    Ref(VertexAlgebra + "StateField/SkewSymmetry.skew_symmetry"), Text(", and "),
                    Ref(Orbifold + "OriginalMMSkew.originalI_skew"), Text(".")),
                Paragraph(Text("The exchange expresses the defect as a finite sum of signed divided "
                    + "translates of the defects in the order (u, a, v) at indices (r, q + j, p) for "
                    + "natural j. The MVM law gives zero at each such triple, so every translated "
                    + "summand vanishes. See "),
                    Ref(VertexAlgebra + "StateField/BorcherdsPermutations.defect_swap_last"), Text(" and "),
                    Ref(Jacobi + "defect_mvm"), Text("."))),
            DescribeRole.Theorem))));
}
