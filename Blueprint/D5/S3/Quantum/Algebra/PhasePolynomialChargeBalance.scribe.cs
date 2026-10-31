using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PhasePolynomialChargeBalanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generic diagonal coefficient rescaling and charge balance for an infinite-order phase.", H("Diagonal Polynomial Charge Balance"),
        Blocks(
            Describe.Lean(DescribeId.Create("coeff-aeval-diag"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PhasePolynomialChargeBalance.coeff_aeval_diag"),
                H("Diagonal coefficient formula"), StatementSource.FromAuthor(Disp(All("sigma", F.Id("Type"), All("R", F.Id("Type"), Seq(OpenBracket, Call("CommRing", F.Id("R")), CloseBracket, Sp, All("d", Rel(F.Id("sigma"), To, F.Id("R")), All("f", Call("MvPolynomial", F.Id("sigma"), F.Id("R")), All("m", Call("Exponent", F.Id("sigma")), Rel(Call("coeff", Call("aevalDiag", F.Id("d"), F.Id("f")), F.Id("m")), Eq, Rel(Call("exponentProduct", F.Id("m"), F.Id("d")), Cdot, Call("coeff", F.Id("f"), F.Id("m")))))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/physlibphasepolynomial2026")),
                Blocks(Paragraph(Text("For any commutative ring R and any variable type sigma, aevalDiag(d,f) substitutes C(d(i))*X(i) into f. Exponent(sigma) is sigma to finitely supported natural numbers. ExponentProduct(m,d) is the product over the support of m of d(i) raised to m(i). The coefficient of m after substitution is that product times the original coefficient. This is the pinned Physlib declaration, with its proof retained."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coeff-eq-zero-of-charge-ne-zero"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PhasePolynomialChargeBalance.coeff_eq_zero_of_charge_ne_zero"),
                H("Charge balance"), StatementSource.FromAuthor(Disp(All("sigma", F.Id("Type"), All("K", F.Id("Type"), Seq(OpenBracket, Call("Field", F.Id("K")), CloseBracket, Sp, All("w", Rel(F.Id("sigma"), To, F.Id("Z")), All("c", F.Id("K"), Rel(Rel(F.Id("c"), Neq, D(0)), Implies, Rel(All("n", F.Id("Z"), Rel(Rel(Call("zpow", F.Id("c"), F.Id("n")), Eq, D(1)), Implies, Rel(F.Id("n"), Eq, D(0)))), Implies, All("f", Call("MvPolynomial", F.Id("sigma"), F.Id("K")), Rel(Rel(Call("chargeSubstitution", F.Id("w"), F.Id("c"), F.Id("f")), Eq, F.Id("f")), Implies, All("m", Call("Exponent", F.Id("sigma")), Rel(Rel(Call("charge", F.Id("w"), F.Id("m")), Neq, D(0)), Implies, Rel(Call("coeff", F.Id("f"), F.Id("m")), Eq, D(0))))))))))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/physlibphasepolynomial2026")),
                Blocks(Paragraph(Text("For a field K, integer weights w and a nonzero scalar c, assume c^n=1 only for n=0 among all integers. ChargeSubstitution substitutes C(c raised to w(i))*X(i). Formal invariance under this substitution forces a coefficient to vanish whenever the sum over its finite exponent support of m(i)*w(i) is nonzero. No assumption about actual conjugate evaluation belongs to this supplier; that bridge is established separately."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exists-infiniteOrder-unitary"),
                DeclarationHandle.Create("D5/S3/Quantum/Algebra/PhasePolynomialChargeBalance.exists_infiniteOrder_unitary"),
                H("An infinite-order complex unitary phase"), StatementSource.FromAuthor(Disp(Ex("w", Call("unitary", F.Id("C")), All("n", F.Id("Z"), Rel(Rel(Call("zpow", F.Id("w"), F.Id("n")), Eq, D(1)), Implies, Rel(F.Id("n"), Eq, D(0))))))),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/physlibphasepolynomial2026")),
                Blocks(Paragraph(Text("There exists a complex unitary scalar with no nontrivial integer power equal to one. The retained Physlib proof constructs exp(i) and uses the irrationality of pi. These three leaf transplants use the pinned source and full Apache-2.0 license recorded in the cited source note, and retire when equivalent declarations are available in the repository pin of Mathlib."))), DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) { content.Add(Comma); content.Add(Sp); }
            content.Add(arguments[i]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Unique(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Star, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Rel(Formula left, Formula relation, Formula right) =>
        Seq(Open, left, Sp, relation, Sp, right, Close);
    private static Formula And(params Formula[] parts)
    {
        var content = new List<Formula> { Open };
        for (var i = 0; i < parts.Length; i++)
        {
            if (i > 0) { content.Add(Sp); content.Add(Land); content.Add(Sp); }
            content.Add(parts[i]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }
    private static Formula Coordinates(Formula body, bool finite = true) =>
        All("iota", F.Id("Type"), finite
            ? Seq(OpenBracket, Call("Fintype", F.Id("iota")), CloseBracket, Sp, body) : body);
    private static Formula P => Call("Poly", F.Id("iota"));
    private static Formula V => Rel(F.Id("iota"), To, F.Id("C"));
    private static Formula M => Call("Matrix", F.Id("iota"), F.Id("iota"), F.Id("C"));
    private static Formula Actual(Formula p, Formula z) => Call("actual", p, z);
    private static Formula Q(Formula h, Formula z) => Call("starDotMul", h, z);
}
