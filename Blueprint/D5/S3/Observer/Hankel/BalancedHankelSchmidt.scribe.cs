using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Hankel;

internal sealed class BalancedHankelSchmidtDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced actual Gramians yield the complete Schmidt decomposition of the true infinite Hankel operator.",
        H("BalancedHankelSchmidt"),
        Blocks(
            Describe.Lean(DescribeId.Create("inverse-root-diagonal"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedHankelSchmidt.invRootDiagonal"),
                H("The inverse square-root diagonal"),
                StatementSource.FromAuthor(Disp(InverseRootFormula())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The diagonal consists of the reciprocals of the nonnegative real square roots of the weights."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("normalizedfuture"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedHankelSchmidt.normalizedFuture"), H("normalized Future"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Constructs an isometry by normalizing actual future trajectories with the diagonal Gramian; norm preservation is proved."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("leftisometry"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedHankelSchmidt.leftIsometry"), H("left Isometry"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual original-system future trajectories span the finite left Schmidt subspace."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rightisometry"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedHankelSchmidt.rightIsometry"), H("right Isometry"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual dual-system trajectories span the finite right Schmidt subspace."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hankel-isometric-factorization"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedHankelSchmidt.hankel_isometric_factorization"), H("hankel isometric factorization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Proves the full l2 operator equals the left isometry composed with the balancing diagonal and the right isometry adjoint."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("leftmode"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedHankelSchmidt.leftMode"), H("left Mode"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Constructs the left singular output trajectory associated with a standard state coordinate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("rightmode"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedHankelSchmidt.rightMode"), H("right Mode"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Constructs the right singular input trajectory associated with a standard state coordinate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("modes-orthonormal"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedHankelSchmidt.modes_orthonormal"), H("modes orthonormal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both trajectory families are orthonormal in their genuine infinite l2 spaces."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hankel-mode-equations"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedHankelSchmidt.hankel_mode_equations"), H("hankel mode equations"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Proves both forward and adjoint singular-vector equations for every positive balancing weight."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hankel-schmidt-expansion"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedHankelSchmidt.hankel_schmidt_expansion"), H("hankel schmidt expansion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Proves the complete finite Schmidt expansion for every l2 input, not only finite-support test inputs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hankel-kernel-iff"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedHankelSchmidt.hankel_kernel_iff"), H("hankel kernel iff"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Proves the nullspace is precisely the orthogonal complement of the constructed right singular modes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nonzero-squared-singular-value"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedHankelSchmidt.nonzero_squared_singular_value"), H("nonzero squared singular value"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Proves every nonzero eigenvalue of the actual Hankel adjoint-composition is a squared balancing weight. Repeated weights retain orthogonal modes."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("constructed-core-singular-values"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedHankelSchmidt.constructed_core_singular_values"), H("constructed core singular values"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Instantiates the existing finite Gramian singular-value theorem with actual positive square roots. It is supplementary to the separately proved infinite decomposition."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("constructed-hankel-schmidt"),
                DeclarationHandle.Create("D5/S3/Observer/Hankel/BalancedHankelSchmidt.constructed_hankel_schmidt"), H("constructed hankel schmidt"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("End-to-end identification from the original system: constructs actual Gramians and coordinates, proves orthonormal modes, full expansion, kernel characterization and Gramian-product characteristic polynomial. The finite singular multiset is not assumed sorted."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/Hankel/InfiniteHankelGramian")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/Hankel/BalancedRealizationTransport")), DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/LinearMemory/HankelGramianSingularValues"))]));
    private static Formula Call(string name, params Formula[] args)
    {
        var symbol = Seq(Operatorname, Grp(Seq(name.Split('.').SelectMany((part, i) => i == 0
            ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) }).ToArray())));
        return args.Length == 0 ? symbol : new Formula.Apply(symbol, [.. args]);
    }
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula InverseRootFormula()
    {
        var v = F.Id("V"); var w = F.Id("w"); var i = F.Id("i");
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var body = new Formula.Relation(Call("invRootDiagonal", w), FormulaRelationOperator.Equal,
            Call("Matrix.diagonal", Seq(Call("fun"), Sp,
                Parenthesized(Seq(i, Sp, Colon, Sp, v)), Sp, Mapsto, Sp,
                Call("Inv.inv", Call("Real.sqrt", new Formula.Apply(w, [i]))))));
        return Seq(Forall, Sp, Parenthesized(Seq(v, Sp, Colon, Sp, F.Id("Type"))), Comma, Sp,
            OpenBracket, Call("DecidableEq", v), CloseBracket, Sp,
            Forall, Sp, Parenthesized(Seq(w, Sp, Colon, Sp, v, Sp, To, Sp, real)), Comma, Sp, body);
    }

}
