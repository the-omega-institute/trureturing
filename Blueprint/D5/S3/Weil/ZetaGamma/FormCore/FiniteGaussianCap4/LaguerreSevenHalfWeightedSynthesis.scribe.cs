using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4;

internal sealed class LaguerreSevenHalfWeightedSynthesisDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfWeightedSynthesis.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual weighted Laguerre synthesis",
        H("Actual weighted Laguerre synthesis"),
        Blocks(
            Paragraph(Text("Write w(k)=(k+1)^2 d(k), and assume w belongs to real ell2. The physical graph measure is (x^(7/2)+x^(15/2)) dx on x>0, and the absolute central Mellin measure is x^(5/4) dx on the same half-line. The construction uses the actual normalized alpha=7/2 Laguerre polynomials and physical functions already defined in the supplier modules.")),
            Describe.Lean(
                DescribeId.Create("laguerre-seven-half-synthesis-finite"),
                DeclarationHandle.Create(Owner + "synthesis_finite"),
                H("One finite function in both physical spaces"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every finitely supported weighted coefficient vector, the continuous synthesis agrees in both Lp spaces with the same actual finite polynomial/exponential function. The inclusion of finite vectors into ell2 is dense. This agreement is used by the infinite-sum theorem below."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("laguerre-seven-half-synthesis-norm"),
                DeclarationHandle.Create(Owner + "synthesis_norm_le"),
                H("Actual graph and absolute Mellin bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The finite graph norm is at most 649 times the ell2 norm of w. The finite Mellin L1 norm is at most 20 times the ell2 norm of (1/(k+1)) times the ell2 norm of w. Orthogonality proves the base quadratic identity, the Jacobi recurrence supplies the fourth graph estimate, and Holder's inequality proves absolute Mellin control. Dense extension gives a continuous linear map into the product of the two actual physical spaces, with the maximum of these constants."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("laguerre-seven-half-synthesis-sum"),
                DeclarationHandle.Create(Owner + "synthesis_hasSum"),
                H("Finite mode sums converge to the constructed image"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every square-summable weighted coefficient vector w, the actual finite single-mode syntheses have sum synthesis(w) in the physical product norm. This is convergence in the stated Lp spaces; identifying their infinite representatives pointwise is a subsequent bridge. No completeness of the Laguerre family, closedness of the synthesis image, or surjectivity onto an original RH form domain is assumed or concluded. The imported polynomial supplier retains its Apache-2.0 license and attribution. This construction is source-relative formal mathematics and makes no literature-priority or RH-resolution claim."))),
                DescribeRole.Theorem))));
}
