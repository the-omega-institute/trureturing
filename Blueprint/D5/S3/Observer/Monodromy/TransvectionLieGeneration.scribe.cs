using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Monodromy;

internal sealed class TransvectionLieGenerationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/Monodromy/TransvectionLieGeneration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Connectedness of the actual pairing graph and nondegeneracy force the "
            + "rank-one increments to generate the entire skew-adjoint Lie algebra. "
            + "A star admits explicit certificates of bracket length at most three.",
        H("Constructive Lie Generation from a Pairing Graph"),
        Blocks(
            Paragraph(Text(
                "Let K be a field and I a finite index type with decidable equality. "
                    + "For a matrix H with H(i,j)=-H(j,i), use the imported actual "
                    + "increment N_i=e_i H(i,*). Put C_ij=(E_ij+E_ji)H, including "
                    + "C_ii=2N_i. The pairing graph has edge i,j precisely when "
                    + "H(i,j) is nonzero. Connectivity means reflexive-transitive "
                    + "reachability in this relation, with no arbitrary graph labels.")),
            Describe.Lean(
                DescribeId.Create("generated-eq-skew-adjoint"),
                DeclarationHandle.Create(Prefix + "generated_eq_skewAdjoint"),
                H("The generated algebra is the full symplectic Lie algebra"),
                StatementSource.FromAuthor(Generation()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume det(H) is nonzero, 2 is nonzero in K, and the pairing "
                            + "graph is connected. The conclusion is equality of the "
                            + "standard Mathlib LieSubalgebra.lieSpan of the actual "
                            + "increments with skewAdjointMatricesLieSubalgebra(H). "
                            + "The latter consists of the actual matrices X satisfying "
                            + "transpose(X) H=-H X. No irreducibility or generation "
                            + "assumption is included in the input.")),
                    Paragraph(Text(
                        "Matrix multiplication proves [N_i,N_j]=H_ij C_ij and "
                            + "[C_ij,N_k]=H_jk C_ik+H_ik C_jk. The first formula "
                            + "produces each edge direction. The second propagates "
                            + "cross directions along an actual path, dividing only "
                            + "by its nonzero edge entries. Every skew-adjoint X is "
                            + "S H for a symmetric S=X H-inverse; the proof exhibits "
                            + "X as the double sum of (S_ij/2) C_ij. This proves "
                            + "both inclusions using the standard Lie closure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cross-cubic-certificate"),
                DeclarationHandle.Create(Prefix + "cross_cubic_certificate"),
                H("A star has a short explicit certificate for every cross direction"),
                StatementSource.FromAuthor(Cubic()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For any anchor a and indices i,j with H_ai and H_aj "
                            + "nonzero, C_ij equals -(H_ai H_aj)-inverse times "
                            + "[N_i,[N_a,N_j]] plus H_ij/(H_ai squared) times "
                            + "[N_a,N_i]. This is valid even when i=j and when "
                            + "the leaf-leaf entry H_ij vanishes. The displayed "
                            + "formula itself needs neither a determinant hypothesis "
                            + "nor division by two. Bracket length counts generator "
                            + "occurrences; it is not group word length.")),
                    Paragraph(Text(
                        "For a nondegenerate star in characteristic different from "
                            + "two, the increments, the anchor commutators, and one "
                            + "double commutator for each unordered leaf pair span "
                            + "the full algebra. The basis count and sharpness examples "
                            + "are proved in the companion theory text, not exported "
                            + "as additional Lean declarations by this module."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("recovered-generated-eq-skew-adjoint"),
                DeclarationHandle.Create(Prefix + "recovered_generated_eq_skewAdjoint"),
                H("The scalar-observation construction now comes with full Lie generation"),
                StatementSource.FromAuthor(Recovered()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Use the preceding modules' reconstructed matrix R and form "
                            + "J=diagonal(mu)R. Assume p_i is nonzero for i different "
                            + "from the anchor, t_ii=0, t_ij=-t_ji, det(R) is nonzero, "
                            + "and 2 is nonzero in K. The source proves that nonzero "
                            + "row rescaling preserves the generated Lie algebra, "
                            + "then applies the connected-graph theorem to J, whose "
                            + "anchor row has nonzero entries. Thus the actual "
                            + "increments of R generate the full J-skew-adjoint "
                            + "algebra. Merely storing an invariant form would "
                            + "not imply this conclusion."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Prior art: Yelton, arXiv:1703.10917v5, Proposition 3.1 and "
                    + "Remark 3.4, relates connected pairing graphs and their "
                    + "diameter to transvection generation in an l-adic setting. "
                    + "The characteristic-zero Zariski-density consequence uses "
                    + "the standard nilpotent-exponential argument, also explained "
                    + "by Detinko and de Graaf, arXiv:1905.01853v2, Proposition 3.1. "
                    + "Neither general principle is claimed as a new discovery.")),
            Paragraph(Text(
                "The ordinary algebraic-group consequence is separate from this "
                    + "Lean module. It requires characteristic zero. The Fano "
                    + "application still needs an actual geometric eight-dimensional "
                    + "lift and its comparison with the given 27-dimensional local "
                    + "system. This source does not settle that geometric obligation.")))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);

    private static Formula Generation() => Disp(Seq(
        Call("Skew", F.Id("H")), Sp, Land, Sp,
        Call("Nonzero", Call("det", F.Id("H"))), Sp, Land, Sp,
        Call("Nonzero", F.Id("2")), Sp, Land, Sp,
        Call("PairingConnected", F.Id("H")), Sp, Rightarrow, Sp,
        Eq(Call("generated", F.Id("H")),
            Call("skewAdjointMatricesLieSubalgebra", F.Id("H")))));

    private static Formula Cubic() => Disp(Seq(
        Call("Skew", F.Id("H")), Sp, Land, Sp,
        Call("Nonzero", Call("H", F.Id("a"), F.Id("i"))), Sp, Land, Sp,
        Call("Nonzero", Call("H", F.Id("a"), F.Id("j"))), Sp, Rightarrow, Sp,
        Eq(Call("C", F.Id("i"), F.Id("j")),
            Call("cubicCertificate", F.Id("H"), F.Id("a"), F.Id("i"), F.Id("j")))));

    private static Formula Recovered() => Disp(Seq(
        Call("NonzeroPairs", F.Id("p"), F.Id("a")), Sp, Land, Sp,
        Call("Alternating", F.Id("t")), Sp, Land, Sp,
        Call("Nonzero", Call("det", F.Id("R"))), Sp, Land, Sp,
        Call("Nonzero", F.Id("2")), Sp, Rightarrow, Sp,
        Eq(Call("generated", F.Id("R")),
            Call("skewAdjointMatricesLieSubalgebra", F.Id("J")))));
}
