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
            CopyDefinition("copyIsometry", "The basis-copying isometry", CopyIsometryFormula(),
                "The rectangular matrix sends basis vector i to the product basis vector (i,i).", DescribeRole.Definition),
            CopyDefinition("copyIsometry_star_mul", "Basis copying is an isometry", CopyIsometryLaw(),
                "The adjoint of the copying matrix followed by the copying matrix is the identity on the input space.", DescribeRole.Theorem),
            CopyDefinition("copyMatrix", "Coherent matrix copying", CopyMatrixFormula(),
                "Coherent copying conjugates the input matrix by the rectangular copying isometry.", DescribeRole.Definition),
            CopyDefinition("copyMatrix_entry", "Entries of the copied matrix", CopyEntryFormula(),
                "The copied matrix retains an input entry exactly between two correlated product-basis indices and is zero at every other pair.", DescribeRole.Theorem),
            Paragraph(Text(
                "The copying isometry sends basis vector i to the joint basis vector (i,i). "
                    + "The joint state is V rho V*, including the input's off-diagonal entries. "
                    + "Both marginals are obtained by partial trace.")),
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

    private static DocumentBlock CopyDefinition(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create("copying-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Quantum/watrous2018entropicidentities")),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula CopyNamed(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula CopyApp(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula CopyCall(string name, params Formula[] args) => CopyApp(CopyNamed(name), args);
    private static Formula CopyQualified(string owner, string name) => Seq(CopyNamed(owner), Dot, CopyNamed(name));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula CopyAll(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula CopyEqual(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula CopyComplex() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula CopyPair() => Seq(F.Id("n"), Sp, Times, Sp, F.Id("n"));
    private static Formula CopyMatrixType() => CopyCall("Matrix", F.Id("n"), F.Id("n"), CopyComplex());
    private static Formula CopyProjection(Formula p, byte i) => Seq(p, Dot, D(i));
    private static Formula CopyInstances(Formula body) => Seq(
        OpenBracket, CopyCall("Fintype", F.Id("n")), CloseBracket, Sp,
        OpenBracket, CopyCall("DecidableEq", F.Id("n")), CloseBracket, Comma, Sp, body);

    private static Formula CopyIsometryFormula()
    {
        Formula p = F.Id("p"), i = F.Id("i");
        Formula identity = CopyApp(Parenthesized(Seq(D(1), Colon, Sp, CopyMatrixType())), CopyProjection(p, 1), i);
        Formula rhs = CopyCall("ite", CopyEqual(CopyProjection(p, 1), CopyProjection(p, 2)), identity, D(0));
        return Disp(CopyAll("n", CopyNamed("Type"), Seq(
            OpenBracket, CopyCall("DecidableEq", F.Id("n")), CloseBracket, Comma, Sp,
            CopyAll("p", CopyPair(), CopyAll("i", F.Id("n"),
                CopyEqual(CopyCall("copyIsometry", p, i), rhs))))));
    }

    private static Formula CopyIsometryLaw()
    {
        Formula v = Parenthesized(Seq(CopyNamed("copyIsometry"), Colon, Sp,
            CopyCall("Matrix", CopyPair(), F.Id("n"), CopyComplex())));
        return Disp(CopyAll("n", CopyNamed("Type"), CopyInstances(CopyEqual(
            new Formula.Binary(CopyApp(CopyQualified("Matrix", "conjTranspose"), v), FormulaBinaryOperator.Multiply, v), D(1)))));
    }

    private static Formula CopyMatrixFormula()
    {
        Formula v = Parenthesized(Seq(CopyNamed("copyIsometry"), Colon, Sp,
            CopyCall("Matrix", CopyPair(), F.Id("n"), CopyComplex())));
        Formula rhs = new Formula.Binary(new Formula.Binary(v, FormulaBinaryOperator.Multiply, F.Id("M")),
            FormulaBinaryOperator.Multiply, CopyApp(CopyQualified("Matrix", "conjTranspose"), v));
        return Disp(CopyAll("n", CopyNamed("Type"), CopyInstances(CopyAll("M", CopyMatrixType(),
            CopyEqual(CopyCall("copyMatrix", F.Id("M")), rhs)))));
    }

    private static Formula CopyEntryFormula()
    {
        Formula m = F.Id("M"), p = F.Id("p"), q = F.Id("q");
        Formula rhs = CopyCall("ite", CopyEqual(CopyProjection(p, 1), CopyProjection(p, 2)),
            CopyCall("ite", CopyEqual(CopyProjection(q, 1), CopyProjection(q, 2)),
                CopyApp(m, CopyProjection(p, 1), CopyProjection(q, 1)), D(0)), D(0));
        return Disp(CopyAll("n", CopyNamed("Type"), CopyInstances(CopyAll("M", CopyMatrixType(),
            CopyAll("p", CopyPair(), CopyAll("q", CopyPair(), CopyEqual(CopyCall("copyMatrix", m, p, q), rhs)))))));
    }
}
