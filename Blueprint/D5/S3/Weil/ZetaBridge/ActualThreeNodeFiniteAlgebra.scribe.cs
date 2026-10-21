using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class ActualThreeNodeFiniteAlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual three-node FiniteAlgebra", H("Actual three-node FiniteAlgebra"),
        Blocks(
            Paragraph(Text("Write g=pi/4, mu=mean(c), a=arithmeticBoundarySymbol(c,n), r=n/N and h=g^2+mu. U,T,C,O are the exact physical finite-form coefficients; this module first states their polynomial identities for arbitrary real g,mu,a,r.")),
            Paragraph(Text("The even block has diagonal U/3,C/6 and off-diagonal T/sqrt(18). Its trace is 6h+4gar+4(a^2-h)r^2/3+2hr^4/5. Its determinant is the displayed exact polynomial of degrees two through six, with no root-distinctness assumption.")),
            Paragraph(Text("At a=0 the determinant is exactly 32h^2 r^4/45 and the trace is 6h-4hr^2/3+2hr^4/5. The different vanishing order is retained in the exceptional spectral branch.")),
            Describe.Lean(DescribeId.Create("u"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.U"),
                H("U"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def U (g mu a r : ℝ) : ℝ :=\n  18 * (g ^ 2 + mu) + 12 * g * a * r +\n    (8 * a ^ 2 / 3 - 4 * (g ^ 2 + mu)) * r ^ 2 -\n    2 * g * a * r ^ 3 + 2 * (g ^ 2 + mu) * r ^ 4 / 5"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("t"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.T"),
                H("T"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def T (g mu a r : ℝ) : ℝ :=\n  6 * g * a * r + (8 * a ^ 2 / 3 + 4 * (g ^ 2 + mu)) * r ^ 2 +\n    g * a * r ^ 3 - 4 * (g ^ 2 + mu) * r ^ 4 / 5"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("c"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.C"),
                H("C"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def C (g mu a r : ℝ) : ℝ :=\n  8 * a ^ 2 * r ^ 2 / 3 + 4 * g * a * r ^ 3 +\n    8 * (g ^ 2 + mu) * r ^ 4 / 5"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("o"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.O"),
                H("O"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def O (g mu a r : ℝ) : ℝ :=\n  4 * a ^ 2 + 4 * g * a * r + 4 * (g ^ 2 + mu) * r ^ 2 / 3"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("even-det"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.evenDet"),
                H("evenDet"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("def evenDet (g mu a r : ℝ) : ℝ :=\n  U g mu a r / 3 * (C g mu a r / 6) -\n    (T g mu a r / Real.sqrt 18) ^ 2"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-trace-identity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.finite_trace_identity"),
                H("finite trace identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("lemma finite_trace_identity (g mu a r : ℝ) :\n    U g mu a r / 3 + C g mu a r / 6 =\n      6 * (g ^ 2 + mu) + 4 * g * a * r +\n        4 / 3 * (a ^ 2 - (g ^ 2 + mu)) * r ^ 2 +\n        2 * (g ^ 2 + mu) * r ^ 4 / 5"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-determinant-identity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.finite_determinant_identity"),
                H("finite determinant identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("lemma finite_determinant_identity (g mu a r : ℝ) :\n    evenDet g mu a r =\n      (2 * a ^ 2 * (g ^ 2 + 4 * mu) / 3) * r ^ 2 +\n      (4 * g * a * (g ^ 2 + mu) / 3) * r ^ 3 +\n      (2 * a ^ 2 * g ^ 2 - 16 * a ^ 2 * (g ^ 2 + mu) / 9 +\n        32 * (g ^ 2 + mu) ^ 2 / 45) * r ^ 4 +\n      (4 * g * a * (g ^ 2 + mu) / 15) * r ^ 5 +\n      (a ^ 2 * (g ^ 2 + 16 * mu) / 30) * r ^ 6"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exceptional-trace-identity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.exceptional_trace_identity"),
                H("exceptional trace identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("lemma exceptional_trace_identity (g mu r : ℝ) :\n    U g mu 0 r / 3 + C g mu 0 r / 6 =\n      6 * (g ^ 2 + mu) - 4 * (g ^ 2 + mu) * r ^ 2 / 3 +\n        2 * (g ^ 2 + mu) * r ^ 4 / 5"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exceptional-determinant-identity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/ActualThreeNodeFiniteAlgebra.exceptional_determinant_identity"),
                H("exceptional determinant identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("lemma exceptional_determinant_identity (g mu r : ℝ) :\n    evenDet g mu 0 r = 32 * (g ^ 2 + mu) ^ 2 * r ^ 4 / 45"))), DescribeRole.Theorem))));
}
