using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class PartialTraceMutualInformationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/PartialTraceMutualInformation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial traces give density-state marginals, and independent product states have "
            + "zero quantum mutual information.",
        H("Partial Trace and Quantum Mutual Information"),
        Blocks(
            Describe.Lean(DescribeId.Create("trace-cfc"), DeclarationHandle.Create(Module + "re_trace_cfc"),
                H("The trace of a spectral function"), StatementSource.FromAuthor(TraceCfcFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a Hermitian matrix and any real function, the real trace of its continuous functional calculus equals the sum of that function over its eigenvalues."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("density-positive"),
                DeclarationHandle.Create(Module + "density_posSemidef"),
                H("Density states are positive in matrix coordinates"),
                StatementSource.FromAuthor(DensityPositivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The star algebra equivalence from CStarMatrix to Matrix preserves nonnegativity, hence positive semidefiniteness."))),
                DescribeRole.Theorem),
            Result("left-positive", "partialTraceLeft_posSemidef",
                "Tracing out the left factor preserves positivity",
                "For arbitrary finite carriers A and B, the reduced matrix is a finite sum "
                    + "of principal submatrices.", PositivityFormula("partialTraceLeft")),
            Result("right-positive", "partialTraceRight_posSemidef",
                "Tracing out the right factor preserves positivity",
                "The same principal-submatrix argument applies to the other factor.",
                PositivityFormula("partialTraceRight")),
            Result("left-trace", "trace_partialTraceLeft",
                "The left partial trace preserves trace",
                "For every joint matrix, summing the reduced diagonal recovers its diagonal sum.",
                TraceFormula("partialTraceLeft")),
            Result("right-trace", "trace_partialTraceRight",
                "The right partial trace preserves trace",
                "Together with positivity, trace preservation gives a normalized marginal.",
                TraceFormula("partialTraceRight")),
            Describe.Lean(
                DescribeId.Create("spectral-entropy"),
                DeclarationHandle.Create(Module + "spectralEntropy"),
                H("Spectral entropy of a Hermitian matrix"),
                StatementSource.FromAuthor(SpectralEntropyFormula()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Quantum/watrous2018entropicidentities")),
                Blocks(Paragraph(Text(
                    "For any Hermitian matrix on a finite carrier, spectralEntropy sums "
                    + "Real.negMulLog over its eigenvalues. On density matrices this is "
                    + "von Neumann entropy in nats, including singular states with "
                    + "the zero-eigenvalue contribution set to zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mutual-information"),
                DeclarationHandle.Create(Module + "quantumMutualInformation"),
                H("Mutual information of a joint density state"),
                StatementSource.FromAuthor(MutualInformationFormula()),
                AssessedProvenance.FromLiterature(
                        LibraryNoteRef.Create("D5/L/Quantum/watrous2018entropicidentities")),
                Blocks(Paragraph(Text(
                    "The only input is the joint state. marginalRight retains A and "
                    + "marginalLeft retains B; each is constructed by partial trace."))),
                DescribeRole.Definition),
            Result("product-entropy", "vonNeumannEntropy_productState",
                "Entropy adds on independent product states",
                "The spectrum of the product is the multiset of pairwise eigenvalue products. "
                    + "For any two density states on finite carriers, including singular states, "
                    + "the proof uses the zero value of x log x at zero.", ProductEntropyFormula()),
            Result("product-information", "quantumMutualInformation_productState",
                "Independent product states have zero mutual information",
                "The actual partial traces recover the two factors. Their entropies cancel "
                    + "the entropy of the product by tensor additivity.", ProductInformationFormula()))));

    private static DocumentBlock Result(
        string id, string declaration, string title, string text, Formula statement) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Module + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Quantum/blore2026partialtrace")),
            Blocks(Paragraph(Text(text))),
            DescribeRole.Theorem);

    private static Formula DensityPositivityFormula()
    {
        Formula n = F.Id("n"), rho = F.Id("rho");
        Formula body = new Formula.Apply(
            Seq(Operatorname, Grp(F.Id("Matrix"), Dot, F.Id("PosSemidef"))),
            [new Formula.Apply(Seq(Operatorname, Grp(F.Id("CStarMatrix"), Dot,
                F.Id("ofMatrix"), Dot, F.Id("symm"))), [Call("val", rho)])]);
        body = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("rho"), Call("DensityState", n), body);
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"), Seq(Operatorname, Grp(F.Id("Type"))),
            Seq(OpenBracket, Call("Fintype", n), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", n), CloseBracket, Sp, body)));
    }

    private static Formula PositivityFormula(string partialTrace) => Disp(Seq(
        Forall, Sp, F.Id("M"), Comma, Sp,
        Call("PosSemidef", F.Id("M")), Sp, Rightarrow, Sp,
        Call("PosSemidef", Call(partialTrace, F.Id("M")))));

    private static Formula TraceFormula(string partialTrace) => Disp(Seq(
        Forall, Sp, F.Id("M"), Comma, Sp,
        Call("trace", Call(partialTrace, F.Id("M"))), Sp, Eq, Sp,
        Call("trace", F.Id("M"))));

    private static Formula MutualInformationFormula()
    {
        Formula a = F.Id("A"), b = F.Id("B"), rho = F.Id("rho");
        Formula body = Seq(Call("quantumMutualInformation", rho), Sp, Eq, Sp,
            Call("vonNeumannEntropy", Call("marginalRight", rho)), Sp, Plus, Sp,
            Call("vonNeumannEntropy", Call("marginalLeft", rho)), Sp, Minus, Sp,
            Call("vonNeumannEntropy", rho));
        body = All("rho", Call("DensityState", Parenthesized(Seq(a, Sp, Times, Sp, b))), body);
        foreach (var carrier in new[] { b, a })
            body = Seq(OpenBracket, Call("Fintype", carrier), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", carrier), CloseBracket, Sp, body);
        return Disp(All("A", F.Id("Type"), All("B", F.Id("Type"), body)));
    }

    private static Formula SpectralEntropyFormula()
    {
        Formula n = F.Id("n"), rho = F.Id("rho"), h = F.Id("h"), i = F.Id("i");
        Formula matrix = Call("Matrix", n, n, Seq(Mathbb, Grp(F.Id("C"))));
        Formula hermitian = Seq(Operatorname,
            Grp(F.Id("Matrix"), Dot, F.Id("IsHermitian")));
        Formula eigenvalues = Seq(Operatorname,
            Grp(F.Id("Matrix"), Dot, F.Id("IsHermitian"), Dot, F.Id("eigenvalues")));
        Formula negMulLog = Seq(Operatorname, Grp(F.Id("Real"), Dot, F.Id("negMulLog")));
        Formula body = Seq(Call("spectralEntropy", h), Sp, Eq, Sp,
            Sum, Underscore, Grp(i, Colon, n), Sp,
            new Formula.Apply(negMulLog, [new Formula.Apply(eigenvalues, [h, i])]));
        Formula bindH = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("h"), new Formula.Apply(hermitian, [rho]), body);
        Formula bindRho = new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("rho"), matrix, bindH);
        return Disp(new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"), Seq(Operatorname, Grp(F.Id("Type"))),
            Seq(OpenBracket, Call("Fintype", n), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", n), CloseBracket, Sp, bindRho)));
    }

    private static Formula ProductEntropyFormula() => Disp(Seq(
        Forall, Sp, Rho, Comma, Sp, SigmaLower, Comma, Sp,
        Call("vonNeumannEntropy", Call("productState", Rho, SigmaLower)), Sp, Eq, Sp,
        Call("vonNeumannEntropy", Rho), Sp, Plus, Sp,
        Call("vonNeumannEntropy", SigmaLower)));

    private static Formula ProductInformationFormula() => Disp(Seq(
        Forall, Sp, Rho, Comma, Sp, SigmaLower, Comma, Sp,
        Call("quantumMutualInformation", Call("productState", Rho, SigmaLower)), Sp, Eq, Sp,
        Num(0)));

    private static Formula TraceCfcFormula()
    {
        Formula n = F.Id("n"), a = F.Id("A"), h = F.Id("hA"), f = F.Id("f"), i = F.Id("i");
        Formula real = Seq(Mathbb, Grp(F.Id("R"))), complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula body = Seq(new Formula.Apply(Qualified("Complex", "re"),
            [new Formula.Apply(Qualified("Matrix", "trace"), [Call("cfc", f, a)])]), Sp, Eq, Sp,
            Sum, Underscore, Grp(i, Sp, Colon, Sp, n), Sp,
            new Formula.Apply(f, [new Formula.Apply(Qualified("Matrix.IsHermitian", "eigenvalues"), [h, i])]));
        body = All("f", Parenthesized(Seq(real, Sp, To, Sp, real)), body);
        body = All("hA", new Formula.Apply(Qualified("Matrix", "IsHermitian"), [a]), body);
        body = All("A", Call("Matrix", n, n, complex), body);
        body = Seq(OpenBracket, Call("Fintype", n), CloseBracket, Sp, OpenBracket, Call("DecidableEq", n), CloseBracket, Sp, body);
        return Disp(All("n", F.Id("Type"), body));
    }
    private static Formula Qualified(string owner, string name)
    {
        var parts = owner.Split('.').Append(name).ToArray();
        Formula result = Seq(Operatorname, Grp(F.Id(parts[0])));
        foreach (var part in parts.Skip(1)) result = Seq(result, Dot, Operatorname, Grp(F.Id(part)));
        return result;
    }
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp,
        Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
}
