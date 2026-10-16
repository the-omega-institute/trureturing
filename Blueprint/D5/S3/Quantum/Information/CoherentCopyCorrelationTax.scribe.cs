using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class CoherentCopyCorrelationTaxDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/CoherentCopyCorrelationTax.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A coherent premeasurement retains the input entropy and divides system-record "
            + "mutual information into diagonal entropy and relative entropy of coherence.",
        H("Coherent Premeasurement and Correlation Tax"),
        Blocks(
            IsoDefinition("copyIsometry", "The basis-copying isometry", IsoIsometryFormula(),
                "The rectangular matrix sends basis vector i to the product basis vector (i,i).", DescribeRole.Definition),
            IsoDefinition("copyIsometry_star_mul", "Basis copying is an isometry", IsoIsometryLaw(),
                "The adjoint of the copying matrix followed by the copying matrix is the identity on the input space.", DescribeRole.Theorem),
            Paragraph(Text(
                "The copying isometry sends basis vector i to the joint basis vector (i,i). "
                    + "The joint state is V rho V*, including the input's off-diagonal entries. "
                    + "Both marginals are obtained by partial trace.")),
            CopyNode("copy-matrix", "copyMatrix", "The coherent copying map", CopyMatrixFormula(),
                "The basis map sends i to (i,i). Its entry at p,i is the identity-matrix "
                    + "entry at p.1,i when p.1 = p.2, and zero otherwise. The displayed "
                    + "formula expands that basis map on both sides of M. A star between "
                    + "matrices denotes matrix multiplication; Matrix.conjTranspose takes the adjoint.",
                DescribeRole.Definition),
            CopyNode("copy-matrix-entry", "copyMatrix_entry", "Entries of the copied matrix", CopyEntryFormula(),
                "For every complex input matrix, only entries between correlated basis "
                    + "pairs survive. Prod.fst and Prod.snd are the two pair projections; "
                    + "ite selects its second argument when its condition holds and its third otherwise.",
                DescribeRole.Theorem),
            CopyNode("partial-trace-right-copy-matrix", "partialTraceRight_copyMatrix",
                "The reduced copied matrix is diagonal", CopyPartialTraceFormula(),
                "For every complex input matrix M, tracing out the second factor of its "
                    + "coherent copy gives Matrix.diagonal of the function i ↦ M i i. "
                    + "No positivity or trace normalization is required.",
                DescribeRole.Theorem),
            Result("correlated-entry", "coherentCopyState_correlated_entry",
                "Coherence survives on the correlated subspace",
                "For every input density state and every pair of indices, the joint matrix "
                    + "entry at (i,i),(j,j) equals the input entry at i,j.",
                Disp(Seq(Forall, Sp, Rho, Comma, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Comma, Sp,
                    Call("jointEntry", Rho, F.Id("i"), F.Id("j")), Sp, Eq, Sp,
                    Call("inputEntry", Rho, F.Id("i"), F.Id("j"))))),
            Result("system-marginal", "marginalRight_coherentCopyState",
                "The system marginal is the pinched input",
                "Tracing out the record leaves precisely the diagonal of the input.",
                MarginalFormula("marginalRight")),
            Result("record-marginal", "marginalLeft_coherentCopyState",
                "The record marginal has the Born weights",
                "Tracing out the system produces the same diagonal state: its ith diagonal "
                    + "entry is rho(i,i), and its off-diagonal entries vanish.",
                MarginalFormula("marginalLeft")),
            Result("entropy", "vonNeumannEntropy_coherentCopyState",
                "Coherent copying preserves entropy",
                "The copying map preserves multiplication, adjoints and trace. Functional "
                    + "calculus transports the logarithm through this map, including zero "
                    + "eigenvalues, so the entropy trace is unchanged.",
                Disp(Seq(Forall, Sp, Rho, Comma, Sp,
                    Call("vonNeumannEntropy", Call("coherentCopyState", Rho)), Sp, Eq, Sp,
                    Call("vonNeumannEntropy", Rho)))),
            Result("correlation-tax", "coherent_copy_correlation_tax",
                "Correlation equals record entropy plus coherence tax",
                "The two marginal entropies are the diagonal entropy, and the joint entropy "
                    + "is the original entropy. The pinching entropy identity supplies the "
                    + "remaining relative entropy term.",
                Disp(Seq(Forall, Sp, Rho, Comma, Sp,
                    Call("quantumMutualInformation", Call("coherentCopyState", Rho)), Sp, Eq, Sp,
                    Call("vonNeumannEntropy", Call("basisPinchingState", Rho)), Sp, Plus, Sp,
                    Call("quantumRelativeEntropy", Rho, Call("basisPinchingState", Rho))))))));

    private static DocumentBlock Result(
        string id, string declaration, string title, string text, Formula statement) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create(declaration == "coherent_copy_correlation_tax"
                    ? "D5/L/Quantum/baumgratz2014coherence"
                    : "D5/L/Quantum/watrous2018entropicidentities")),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Theorem);

    private static Formula MarginalFormula(string name) => Disp(Seq(
        Forall, Sp, Rho, Comma, Sp, Call(name, Call("coherentCopyState", Rho)), Sp, Eq, Sp,
        Call("basisPinchingState", Rho)));

    private static DocumentBlock CopyNode(string id, string declaration, string title,
        Formula statement, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula CopyMatrixFormula() => CopyBinders(CopyAll("M", CopyInputMatrix(),
        CopyEqual(CopyTyped(CopyCall("D5.S3.Quantum.Information.CoherentCopyCorrelationTax.copyMatrix",
                F.Id("M")), CopyOutputMatrix()),
            CopyMultiply(CopyMultiply(CopyBasisMap(), F.Id("M")),
                CopyCall("Matrix.conjTranspose", CopyBasisMap())))));

    private static Formula CopyEntryFormula() => CopyBinders(CopyAll("M", CopyInputMatrix(),
        CopyAll("a", CopyPair(), CopyAll("b", CopyPair(),
            CopyEqual(new Formula.Apply(
                    CopyCall("D5.S3.Quantum.Information.CoherentCopyCorrelationTax.copyMatrix", F.Id("M")),
                    [F.Id("a"), F.Id("b")]),
                CopyCall("ite", CopyEqual(CopyProjection("fst", "a"), CopyProjection("snd", "a")),
                    CopyCall("ite", CopyEqual(CopyProjection("fst", "b"), CopyProjection("snd", "b")),
                        new Formula.Apply(F.Id("M"), [CopyProjection("fst", "a"), CopyProjection("fst", "b")]),
                        D(0)), D(0)))))));

    private static Formula CopyPartialTraceFormula() => CopyBinders(CopyAll("M", CopyInputMatrix(),
        CopyEqual(CopyCall("D5.S3.Quantum.Information.PartialTraceMutualInformation.partialTraceRight",
                CopyCall("D5.S3.Quantum.Information.CoherentCopyCorrelationTax.copyMatrix", F.Id("M"))),
            CopyCall("Matrix.diagonal", CopyLambda("i", F.Id("n"),
                new Formula.Apply(F.Id("M"), [F.Id("i"), F.Id("i")]))))));

    private static Formula CopyBasisMap() => CopyLambda("p", CopyPair(), CopyLambda("i", F.Id("n"),
        CopyCall("ite", CopyEqual(CopyProjection("fst", "p"), CopyProjection("snd", "p")),
            new Formula.Apply(CopyTyped(D(1), CopyInputMatrix()), [CopyProjection("fst", "p"), F.Id("i")]),
            D(0))));

    private static Formula CopyBinders(Formula body) => Seq(Forall, Sp,
        CopyTyped(F.Id("n"), Seq(F.Id("Type"), Star)), Sp,
        OpenBracket, CopyCall("Fintype", F.Id("n")), CloseBracket, Sp,
        OpenBracket, CopyCall("DecidableEq", F.Id("n")), CloseBracket, Comma, Sp,
        Parenthesized(body));
    private static Formula CopyAll(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, CopyTyped(F.Id(name), type), Comma, Sp, Parenthesized(body));
    private static Formula CopyLambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, CopyTyped(F.Id(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula CopyPair() => Parenthesized(Seq(F.Id("n"), Sp, Times, Sp, F.Id("n")));
    private static Formula CopyComplexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula CopyInputMatrix() => CopyCall("Matrix", F.Id("n"), F.Id("n"), CopyComplexes());
    private static Formula CopyOutputMatrix() => CopyCall("Matrix", CopyPair(), CopyPair(), CopyComplexes());
    private static Formula CopyProjection(string name, string value) => CopyCall("Prod." + name, F.Id(value));
    private static Formula CopyTyped(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula CopyMultiply(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Star, Sp, Parenthesized(right));
    private static Formula CopyEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula CopyCall(string name, params Formula[] args)
    {
        var parts = new System.Collections.Generic.List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(part));
        }
        return new Formula.Apply(Seq(Operatorname, Grp(Seq([.. parts]))), [.. args]);
    }
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);

    private static DocumentBlock IsoDefinition(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create("copying-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Quantum/watrous2018entropicidentities")),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula IsoNamed(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula IsoApp(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula IsoCall(string name, params Formula[] args) => IsoApp(IsoNamed(name), args);
    private static Formula IsoQualified(string owner, string name) => Seq(IsoNamed(owner), Dot, IsoNamed(name));
    private static Formula IsoParenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula IsoAll(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, IsoParenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula IsoEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula IsoComplex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula IsoPair() => Seq(F.Id("n"), Sp, Times, Sp, F.Id("n"));
    private static Formula IsoMatrixType() => IsoCall("Matrix", F.Id("n"), F.Id("n"), IsoComplex());
    private static Formula IsoProjection(Formula p, byte i) => Seq(p, Dot, D(i));
    private static Formula IsoInstances(Formula body) => Seq(
        OpenBracket, IsoCall("Fintype", F.Id("n")), CloseBracket, Sp,
        OpenBracket, IsoCall("DecidableEq", F.Id("n")), CloseBracket, Comma, Sp, body);

    private static Formula IsoIsometryFormula()
    {
        Formula p = F.Id("p"), i = F.Id("i");
        Formula identity = IsoApp(IsoParenthesized(Seq(D(1), Colon, Sp, IsoMatrixType())), IsoProjection(p, 1), i);
        Formula rhs = IsoCall("ite", IsoEqual(IsoProjection(p, 1), IsoProjection(p, 2)), identity, D(0));
        return Disp(IsoAll("n", IsoNamed("Type"), Seq(
            OpenBracket, IsoCall("DecidableEq", F.Id("n")), CloseBracket, Comma, Sp,
            IsoAll("p", IsoPair(), IsoAll("i", F.Id("n"),
                IsoEqual(IsoCall("copyIsometry", p, i), rhs))))));
    }

    private static Formula IsoIsometryLaw()
    {
        Formula v = IsoParenthesized(Seq(IsoNamed("copyIsometry"), Colon, Sp,
            IsoCall("Matrix", IsoPair(), F.Id("n"), IsoComplex())));
        return Disp(IsoAll("n", IsoNamed("Type"), IsoInstances(IsoEqual(
            new Formula.Binary(IsoApp(IsoQualified("Matrix", "conjTranspose"), v), FormulaBinaryOperator.Multiply, v), D(1)))));
    }

}
