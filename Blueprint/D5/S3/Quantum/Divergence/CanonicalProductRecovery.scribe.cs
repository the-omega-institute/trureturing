using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class CanonicalProductRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual marginal support cancels singular tensor logarithms in product recovery.",
        H("Canonical Product Recovery"),
        Blocks(Describe.Lean(
            DescribeId.Create("canonical-product-recovery-chain"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Divergence/CanonicalProductRecovery.canonical_product_recovery_chain"),
            H("Singular joint states satisfy the product-reference chain rule"),
            StatementSource.FromAuthor(ChainFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(
                    Text("The whole chain is a repository-derived composition of known mechanisms, "
                        + "with no novelty claim. The adapted Alex Meiburg Physlib sources and "
                        + "the paper's full-rank boundary are attributed in "),
                    Ref("D5/L/Quantum/meiburg2026singulartensorrecovery"),
                    Text(".")),
                Paragraph(Text(
                "In the statement c and d denote gammaA and gammaB; underlyingMatrix is "
                + "CStarMatrix.ofMatrix.symm applied to the state matrix, and infinity is WithTop top. "
                + "The marginal and recovered state use the existing partial trace and product state. "
                + "Only the reference factors are positive definite. The proof contracts actual "
                + "marginal zero directions, retains support projections in the tensor logarithm, "
                + "and cancels them under the same joint-state weighted trace. "
                + "Every divergence in the displayed chain is in its supported finite branch. "
                + "The finite statement does not establish oscillator operator domains or Gibbs traces."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);

    private static Formula ChainFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var c = F.Id("c");
        var d = F.Id("d");
        var r = Call("fromLegacyDensityState", Call("marginalRight", Call("toLegacyDensityState", Rho)));
        var t = Call("fromLegacyDensityState", Call("marginalLeft", Call("toLegacyDensityState", Rho)));
        var rec = Call("fromLegacyDensityState", Call("productState", Call("toLegacyDensityState", r), Call("toLegacyDensityState", d)));
        var reference = Call("fromLegacyDensityState", Call("productState", Call("toLegacyDensityState", c), Call("toLegacyDensityState", d)));
        Formula Fin(Formula x, Formula y) => Call("finiteTraceLogRelativeEntropy", x, y);
        Formula Ext(Formula x, Formula y) => Call("extendedQuantumRelativeEntropy", x, y);
        Formula Finite(Formula x, Formula y) => Seq(Ext(x, y), Sp, Neq, Sp, Infty);
        var result = Seq(
            Call("SupportContained", Rho, rec), Sp, Land, Sp,
            Fin(Rho, reference), Sp, Minus, Sp, Fin(r, c), Sp, Eq, Sp, Fin(Rho, rec), Sp, Land, Sp,
            Ext(Rho, reference), Sp, Eq, Sp, Ext(Rho, rec), Sp, Plus, Sp, Ext(r, c), Sp, Land, Sp,
            Finite(Rho, reference), Sp, Land, Sp,
            Finite(Rho, rec), Sp, Land, Sp,
            Finite(r, c), Sp, Land, Sp,
            Finite(t, d), Sp, Land, Sp,
            Fin(Rho, rec), Sp, Eq, Sp,
            Call("quantumMutualInformation", Call("toLegacyDensityState", Rho)), Sp, Plus, Sp, Fin(t, d));
        var conditions = Seq(
            Call("PosDef", Call("underlyingMatrix", c)), Sp, Land, Sp,
            Call("PosDef", Call("underlyingMatrix", d)), Sp, Rightarrow, Sp, Open, result, Close);
        var instances = Seq(
            OpenBracket, Call("Fintype", a), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", a), CloseBracket, Sp,
            OpenBracket, Call("Fintype", b), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", b), CloseBracket, Sp,
            All(Rho, Call("DensityState", Seq(a, Sp, Times, Sp, b)),
                All(c, Call("DensityState", a), All(d, Call("DensityState", b), conditions))));
        return Disp(All(a, Seq(Operatorname, Grp(F.Id("Type"))), All(b, Seq(Operatorname, Grp(F.Id("Type"))), instances)));
    }
}
