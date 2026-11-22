using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class RHPrimeWindowRemainderDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/IntegratedExplicit/RHPrimeWindowRemainder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prime-window remainder under RH",
        H("Spectral primitives at the endpoints"),
        Blocks(
            Describe.Lean(DescribeId.Create("spectral-primitive"),
                DeclarationHandle.Create(Module + "spectralPrimitive"),
                H("Primitive on the product of circles"), StatementSource.FromAuthor(Primitive()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each index k refers to an actual nontrivial zero occurrence ρₖ. "
                    + "Write cₖ=1/(ρₖ(1−ρₖ)) and γₖ=Im ρₖ. The ordinate bound |γₖ|>10 "
                    + "dominates each primitive term by |cₖ|/10 on the entire product. "
                    + "The resulting uniformly convergent series has continuous real part P."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("window-discrepancy"),
                DeclarationHandle.Create(Module + "windowDiscrepancy"),
                H("Centered prime-only window mass"), StatementSource.FromAuthor(Discrepancy()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/zhao2025mertensmeans")),
                Blocks(Paragraph(Text(
                    "Write Qϑ(x) for the prime-only tail, the integral of (ϑ(u)−u)/u² over u>x "
                    + "from Zhao's equation (14). The window mass N(a,B) is the integral of "
                    + "max(−Qϑ(x),0)/√x from a to B."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fixed-cutoff-constant"),
                DeclarationHandle.Create(Module + "fixedCutoffConstant"),
                H("Constant for a fixed left cutoff"), StatementSource.FromAuthor(Constant()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let φ(t) have coordinates exp(iγₖt). The function e is the log-coordinate density "
                    + "max(√(exp y)(−Qϑ(exp y)),0) minus 2 and the real part of the normalized zero "
                    + "series. Under RH that series is Σₖ cₖφ(y)ₖ, and e is absolutely integrable "
                    + "above log 2."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("prime-window-remainder-of-rh"),
                DeclarationHandle.Create(Module + "prime_window_remainder_of_rh"),
                H("Uniform remainder, cluster interval and exact window identity"), StatementSource.FromAuthor(Claim()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Analytic/zhao2025mertensmeans")),
                Blocks(
                    Paragraph(Text(
                        "Write H for the closure of the real orbit φ, and K(a) for the set of real "
                        + "cluster values of E(a,B) as B tends to infinity. The translated image "
                        + "C(a)+P(H) consists of all C(a)+P(h) with h in H.")),
                    Paragraph(Text(
                        "Under RH each zero frequency equals iγₖ. Integrate the normalized series "
                        + "term by term over the logarithmic window using the summable majorant |cₖ|. "
                        + "The two endpoint series give P(φ(log B))−P(φ(log a)). "
                        + "The residual is exactly the integral of e on the same window, bounded "
                        + "in absolute value by the integral of |e| over (log a,∞).")),
                    Paragraph(Text(
                        "For fixed a the residual converges to the integral of e over (log a,∞). "
                        + "Forward recurrence gives all phases in H, and compactness makes the "
                        + "translated image closed. The image is connected because the real orbit "
                        + "is continuous. At time zero the normalized series has positive real part "
                        + "given by the first Li mass. Integrating over a short interval shows that "
                        + "P takes distinct values on the orbit."))),
                DescribeRole.Theorem))));

    private static Formula Field(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula Real => Field("R");
    private static Formula Phases => new Formula.Power(Field("T"), Field("N"));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Bind(FormulaQuantifier kind, string name, Formula domain, Formula body) =>
        new Formula.Bind(kind, FormulaIdentifier.Create(name), domain, body);
    private static Formula All(string name, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, Real, body);
    private static Formula ExistsReal(string name, Formula body) =>
        Bind(FormulaQuantifier.Exists, name, Real, body);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula At(Formula symbol, Formula index) => Seq(symbol, Underscore, Grp(index));
    private static Formula AtCutoff(Formula cutoff) => Call("P", Call("phi", Call("log", cutoff)));

    private static Formula Primitive()
    {
        var h = F.Id("h");
        var k = F.Id("k");
        var term = new Formula.Fraction(
            Multiply(At(F.Id("c"), k), At(h, k)),
            Multiply(F.Id("i"), At(GammaLower, k)));
        var series = Seq(Sum, Underscore, Grp(k, Sp, InMacro, Sp, Field("N")), Sp, term);
        return Disp(Bind(FormulaQuantifier.ForAll, "h", Phases,
            Eq(Call("P", h), Seq(Re, Sp, Open, series, Close))));
    }

    private static Formula Discrepancy()
    {
        var a = F.Id("a");
        var b = F.Id("B");
        return Disp(All("a", All("B", Eq(Call("E", a, b),
            Subtract(Call("N", a, b), Multiply(D(2), Call("log", new Formula.Fraction(b, a))))))));
    }

    private static Formula Constant()
    {
        var a = F.Id("a");
        var y = F.Id("y");
        var error = Seq(Int, Underscore, Grp(Call("log", a)), Caret, Grp(Infty), Sp,
            Call("e", y), Sp, F.Id("d"), y);
        return Disp(All("a", Eq(Call("C", a), Subtract(error, AtCutoff(a)))));
    }

    private static Formula Claim()
    {
        var a = F.Id("a");
        var b = F.Id("B");
        var x = F.Id("X");
        var eps = F.Id("epsilon");
        var lower = F.Id("l");
        var upper = F.Id("u");
        var discrepancy = Add(Subtract(Call("E", a, b), AtCutoff(b)), AtCutoff(a));
        var bound = Lt(new Formula.Absolute(discrepancy), eps);
        var allCutoffs = All("a", All("B", Imp(Le(x, a), Imp(Le(a, b), bound))));
        var uniform = All("epsilon", Imp(Lt(D(0), eps), ExistsReal("X", And(Le(D(2), x), allCutoffs))));
        var cluster = Call("K", a);
        var interval = Seq(OpenBracket, lower, Comma, Sp, upper, CloseBracket);
        var nondegenerate = ExistsReal("l", ExistsReal("u", And(Lt(lower, upper), Eq(cluster, interval))));
        var image = Add(Call("C", a), Call("P", F.Id("H")));
        var fixedCutoff = All("a", Imp(Le(D(2), a), And(Eq(cluster, image), nondegenerate)));
        var y = F.Id("y");
        var error = Seq(Int, Underscore, Grp(Call("log", a)), Caret, Grp(Call("log", b)), Sp,
            Call("e", y), Sp, F.Id("d"), y);
        var identity = All("a", All("B", Imp(Le(D(2), a), Imp(Le(a, b), Eq(discrepancy, error)))));
        return Disp(Imp(F.Id("RH"), And(uniform, And(fixedCutoff, identity))));
    }
}
