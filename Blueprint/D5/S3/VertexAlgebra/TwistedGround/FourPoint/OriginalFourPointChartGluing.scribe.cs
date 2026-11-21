using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourPointChartGluingDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourPointChartGluing";
    private const string Prefix = Gid + ".";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identity-principle gluing on the three four-point chart domains",
        H("A common function on the twice-punctured plane"),
        Blocks(
            D("four-point-punctured-euler-slit", "Ω", "Native chart parameter domain",
                DescribeRole.Definition,
                Text("The native argument avoids zero and the real ray from one to infinity. "
                    + "The A, B and D substitutions are 1 − z⁻¹, z and z⁻¹.")),
            T("four-point-chart-cover", "U_A_union_U_B", "The A and B domains cover",
                Text("A excludes the nonpositive real ray and the point one. B excludes zero "
                    + "and the real ray starting at one. Their union is ℂ ∖ {0, 1}.")),
            T("four-point-chart-overlap", "U_A_inter_U_B", "The A and B overlap",
                Text("The overlap deletes both real rays, leaving the interval (0, 1) "
                    + "between them. The upper and lower half-planes join through this interval.")),
            T("four-point-inverse-chart-domain", "U_D_eq", "The inverse chart domain",
                Text("D is defined off the closed real segment [0, 1]. It lies in the "
                    + "twice-punctured plane and contains the exterior of the closed unit disk.")),
            T("four-point-chart-gluing", "exists_gluing", "Gluing A and B by the identity principle",
                Text("For holomorphic chart functions A and B, assume their equality "
                    + "holds arbitrarily close to a point of the overlap on its punctured "
                    + "neighborhood. The identity principle extends the equality on the "
                    + "preconnected double slit. The local functions thus give one holomorphic "
                    + "function whose restrictions agree with A and B. "),
                Ref(Prefix + "U_A_inter_U_B"), Text(", "), Ref(Prefix + "U_A_union_U_B")),
            T("four-point-chart-d-agreement", "eqOn_D_of_chart_overlap",
                "Extending a D comparison from either chart",
                Text("Let F be holomorphic on ℂ ∖ {0, 1} and let D be holomorphic on U_D. "
                    + "Assume F agrees with C on an open set U and C = D accumulates at a point "
                    + "of U ∩ U_D. The identity principle extends F = D throughout "
                    + "the preconnected domain U_D. "),
                Ref(Prefix + "U_D_eq")),
            T("four-point-chart-germs-from-restrictions", "germs_of_eqOn",
                "Restrictions give the three punctured germs",
                Text("Near one the A domain supplies the restriction, near zero the B domain "
                    + "supplies it, and near zero in the inverse coordinate the D domain supplies it.")),
            T("four-point-chart-common-germ", "exists_common_four_point_germ",
                "Gluing native channel functions with the B prefactor",
                Text("Let A, B and D be holomorphic on Ω. For integer k, suppose "
                    + "A(1 − z⁻¹) = 2¹² zᵏ B(z) accumulates at a point of the double slit. "
                    + "Suppose A(1 − z⁻¹) = D(z⁻¹) accumulates at a point of U_A ∩ U_D, or "
                    + "2¹² zᵏ B(z) = D(z⁻¹) accumulates at a point of U_B ∩ U_D. On the "
                    + "punctured neighborhood of native zero, assume A(t) agrees with raw A at −t, "
                    + "and B(t) and D(t) agree with raw B and raw D at t. There is then a common "
                    + "function holomorphic on ℂ ∖ {0, 1}. At one its punctured germ is raw A at "
                    + "(1 − z)/z. At zero its germ is 2¹² zᵏ times raw B at z. In the inverse "
                    + "coordinate z = u⁻¹ its germ at u = 0 is raw D at u. "),
                Ref(Prefix + "exists_gluing"), Text(", "), Ref(Prefix + "eqOn_D_of_chart_overlap"),
                Text(", "), Ref(Prefix + "germs_of_eqOn")))));

    private static DocumentBlock T(string id, string declaration, string title, params Inline[] content) =>
        D(id, declaration, title, DescribeRole.Theorem, content);

    private static DocumentBlock D(string id, string declaration, string title, DescribeRole role,
        params Inline[] content) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(content)), role);
}
